//! ELF utilities.
//!
//! Adapted from <https://github.com/nix-community/nix-ld-rs>.
//! Copyright (c) 2023 Zhaofeng Li and nix-ld-rs contributors

mod dynamic;

use core::cmp::max;
use core::ffi::c_void;
use core::fmt;
use core::mem;
use core::slice;

use astd::heapless::Vec as ArrayVec;
use astd::io::{Error as IoError, Read, ReadExactError, Seek, SeekFrom};
use cfg_match::cfg_match;
use displaydoc::Display;
use plain::Plain;

use crate::memory::{PageProtection, VirtualMapper};
use dynamic::Dynamic;
use x86::current::paging::VAddr;

cfg_match! {
    target_arch = "x86_64" => {
        use goblin::elf64 as elf_types;
        const EM_SELF: u16 = elf_types::header::EM_X86_64;
        const R_RELATIVE: u32 = elf_types::reloc::R_X86_64_RELATIVE;
    }
    target_arch = "x86" => {
        use goblin::elf32 as elf_types;
        const EM_SELF: u16 = elf_types::header::EM_386;
        const R_RELATIVE: u32 = elf_types::reloc::R_386_RELATIVE;
    }
}

use elf_types::{
    header::{Header, ET_DYN},
    program_header::{ProgramHeader, PF_R, PF_W, PF_X, PT_LOAD},
};

const HEADER_SIZE: usize = mem::size_of::<Header>();
const MAX_PROGRAM_HEADERS: usize = 20;

#[derive(Display, Debug)]
pub enum Error {
    /// Binary not long enough to have an ELF header
    TooShort,

    /// Binary is not an ELF
    BadMagic,

    /// Binary is for wrong architecture (expected 0x{expected:x}, got 0x{actual:x})
    WrongArchitecture { expected: u16, actual: u16 },

    /// Binary is not relocatable
    NotRelocatable,

    /// Binary has bad program header size {0}
    BadProgramHeaderSize(usize),

    /// Too many program headers
    TooManyProgramHeaders,

    /// No loadable segments
    NoLoadableSegments,

    /// Failed to memory map
    MapFailed,

    /// I/O error: {0}
    IoError(IoError),
}

pub struct ElfHandle<F: Read + Seek> {
    file: F,
    header: Header,
    program_headers: ArrayVec<ProgramHeader, MAX_PROGRAM_HEADERS>,
    start_pos: u64,
    page_size: usize,
    elf_end: usize,
}

pub struct ElfMapping {
    pub phys_base: usize,
    pub load_addr: usize,
    pub load_size: usize,
    pub load_bias: usize,
    pub entry_point: *const c_void,
    pub max_vaddr: usize,
}

struct DisplayPFlags<'ph>(&'ph ProgramHeader);

#[derive(Debug, Clone)]
struct LoadableSummary {
    total_mapping_size: usize,
    first_vaddr: usize,
}

trait ProgramHeaderExt {
    fn prot_flags(&self) -> PageProtection;
}

impl Into<Error> for IoError {
    fn into(self) -> Error {
        Error::IoError(self)
    }
}

impl<E> Into<Error> for ReadExactError<E>
where
    E: Into<Error>,
{
    fn into(self) -> Error {
        match self {
            ReadExactError::UnexpectedEof => Error::TooShort,
            ReadExactError::Other(e) => e.into(),
        }
    }
}

impl<T> ElfHandle<T>
where
    T: Read + Seek,
    T::Error: Into<Error>,
{
    pub fn parse(mut file: T, page_size: usize) -> Result<Self, Error> {
        let start_pos = file.stream_position().map_err(Into::into)?;

        let mut header_bytes = [0u8; HEADER_SIZE];
        file.read_exact(&mut header_bytes).map_err(Into::into)?;

        let header = Header::from_bytes(&header_bytes);
        if &header.e_ident[..4] != b"\x7fELF".as_slice() {
            return Err(Error::BadMagic);
        }

        if header.e_machine != EM_SELF {
            return Err(Error::WrongArchitecture {
                expected: EM_SELF,
                actual: header.e_machine,
            });
        }

        if header.e_type != ET_DYN {
            // We only support PIE kernels
            return Err(Error::NotRelocatable);
        }

        if header.e_phentsize as usize != mem::size_of::<ProgramHeader>() {
            return Err(Error::BadProgramHeaderSize(header.e_phentsize as usize));
        }

        if header.e_phnum as usize > MAX_PROGRAM_HEADERS {
            return Err(Error::TooManyProgramHeaders);
        }

        let mut program_headers = ArrayVec::new();

        let mut elf_end = 0;
        for _ in 0..header.e_phnum {
            let mut ph_bytes = [0u8; mem::size_of::<ProgramHeader>()];
            file.read_exact(&mut ph_bytes).map_err(Into::into)?;

            let ph = <ProgramHeader as Plain>::from_bytes(&ph_bytes)
                .unwrap()
                .clone();

            let file_end = ph.p_offset + ph.p_filesz;
            elf_end = max(elf_end, file_end as usize);

            program_headers.push(ph).unwrap();
        }

        if header.e_shoff != 0 {
            let file_end = header.e_shoff + header.e_shentsize as u64 * header.e_shnum as u64;
            elf_end = max(elf_end, file_end as usize);
        }

        log::info!("ELF end: {}", elf_end);

        Ok(Self {
            file,
            header: header.clone(),
            program_headers,
            start_pos,
            page_size,
            elf_end,
        })
    }

    pub fn load(mut self, memory: &mut impl VirtualMapper) -> Result<(ElfMapping, T), Error> {
        let summary = if let Some(summary) = self.summarize_loadable() {
            summary
        } else {
            return Err(Error::NoLoadableSegments);
        };

        log::info!("Summary: {:?}", summary);

        log::info!("Program headers:");
        for ph in self.program_headers.iter() {
            log::info!("- {:?}", ph);
        }

        // This assumes that the ELF is relocatable
        let load_size = self.page_align(summary.total_mapping_size);
        let load_base_map = unsafe {
            memory.map_anonymous(
                VAddr(0),
                load_size,
                PageProtection {
                    read: false,
                    write: false,
                    execute: false,
                },
            )
        };

        let load_addr_loader = load_base_map.paddr.0 as *mut c_void;
        let load_addr = load_base_map.vaddr.0 as *mut c_void;

        if load_addr_loader.is_null() {
            return Err(Error::MapFailed);
        }

        // The first section's code starts at
        //
        //     load_addr + page_offset(ph.p_vaddr)
        let load_bias = (load_addr as usize).wrapping_sub(self.page_start(summary.first_vaddr));
        let load_bias_loader =
            (load_addr_loader as usize).wrapping_sub(self.page_start(summary.first_vaddr));
        let max_vaddr = load_addr as usize + summary.total_mapping_size;
        let entry_point = (load_bias + self.header.e_entry as usize) as *const c_void;

        log::debug!("   Total Size: 0x{:x}", summary.total_mapping_size);
        log::debug!("    Load Addr: {:x?}", load_addr);
        log::debug!("  First Vaddr: 0x{:x?}", summary.first_vaddr);
        log::debug!("    Load Bias: 0x{:x?}", load_bias);
        log::debug!("  Entry Point: 0x{:x?}", entry_point);
        log::debug!("    Page Size: {}", self.page_size);

        for ph in self.program_headers.iter() {
            if ph.p_type != PT_LOAD || ph.p_memsz == 0 {
                continue;
            }

            let memsz = ph.p_memsz as usize;
            let filesz = ph.p_filesz as usize;
            let vaddr = ph.p_vaddr as usize;
            let vend = vaddr + memsz;
            let fend = vaddr + filesz;
            let offset = ph.p_offset as usize;

            let prot = ph.prot_flags();

            let total_map_size = self.page_align(vend) - self.page_start(vaddr);
            let file_map_size =
                self.page_align(core::cmp::min(fend, vend)) - self.page_start(vaddr);

            // There can very well be a section with filesz == 0
            if file_map_size > 0 {
                // Assumption:
                //
                //     page_offset(ph.p_vaddr) == page_offset(ph.p_offset)
                //
                // We do the following mmap for the file-backed portion:
                let mapping = unsafe {
                    let addr = self.page_start(load_bias + vaddr);
                    let size = file_map_size;

                    log::trace!(
                        "mmap [{ph}] [0x{addr:x}-0x{mend:x}] (vaddr=0x{vaddr:x}, offset=0x{offset:x})",
                        mend = addr + size,
                        ph = DisplayPFlags(ph),
                    );

                    memory
                        .map_anonymous(VAddr::from_usize(addr), size, prot)
                        .paddr
                        .0 as *mut c_void
                };

                if mapping.is_null() {
                    log::error!("Failed to map segment 0x{:x}", vaddr);
                    return Err(Error::MapFailed);
                }

                // FIXME: Unwritable memory
                let dst = unsafe { slice::from_raw_parts_mut(mapping as *mut u8, file_map_size) };

                self.file
                    .seek(SeekFrom::Start(
                        self.start_pos + self.page_start(offset) as u64,
                    ))
                    .map_err(Into::into)?;
                self.file.read_exact(dst).map_err(Into::into)?;
            }

            // Memory beyond memsz is zero-initialized
            if memsz > filesz && (ph.p_flags & PF_W != 0) {
                // Zero out the fractional page
                let zero_addr = load_bias_loader + vaddr + filesz;
                let zero_end = self.page_align(zero_addr);
                if zero_end > zero_addr {
                    let fractional_page = unsafe {
                        slice::from_raw_parts_mut(zero_addr as *mut u8, zero_end - zero_addr)
                    };
                    fractional_page.fill(0);
                }

                if file_map_size < total_map_size {
                    let mapping = unsafe {
                        let addr = load_addr.add(file_map_size);
                        let size = total_map_size - file_map_size;
                        log::trace!(
                            "mmap [{ph}] [{addr:?}-0x{mend:x}] (vaddr=0x{vaddr:x}, anon)",
                            mend = addr as usize + size,
                            ph = DisplayPFlags(ph),
                        );

                        memory.map_anonymous(VAddr(addr as u64), size, prot).paddr.0 as *mut c_void
                    };

                    if mapping.is_null() {
                        log::error!("Failed to map anonymous portion for segment 0x{:x}", vaddr);
                        return Err(Error::MapFailed);
                    }
                }
            }
        }

        if let Some(dynamic) =
            Dynamic::from_program_headers(self.program_headers.iter(), load_bias, load_bias_loader)
        {
            log::debug!("Applying relocations");
            dynamic.fixup();
        }

        log::debug!("GDB: add-symbol-file /path/to/elf -o 0x{:x}", load_bias);

        Ok((
            ElfMapping {
                phys_base: load_addr_loader as usize,
                load_bias,
                load_size,
                load_addr: load_addr as usize,
                entry_point,
                max_vaddr,
            },
            self.file,
        ))
    }

    pub fn elf_end(&self) -> usize {
        self.elf_end
    }

    fn summarize_loadable(&self) -> Option<LoadableSummary> {
        let mut first_vaddr = None;
        let mut addr_min = usize::MAX;
        let mut addr_max = usize::MIN;

        for ph in self.program_headers.iter() {
            if ph.p_type != PT_LOAD || ph.p_memsz == 0 {
                continue;
            }

            if first_vaddr.is_none() {
                first_vaddr = Some(ph.p_vaddr as usize);
            }

            if addr_min > ph.p_vaddr as usize {
                addr_min = ph.p_vaddr as usize;
            }

            let vend = ph.p_vaddr as usize + ph.p_memsz as usize;
            if addr_max < vend {
                addr_max = vend;
            }
        }

        first_vaddr.map(|first_vaddr| LoadableSummary {
            first_vaddr,
            total_mapping_size: addr_max - addr_min,
        })
    }

    #[inline(always)]
    fn page_align(&self, v: usize) -> usize {
        (v + self.page_size - 1) & !(self.page_size - 1)
    }

    #[inline(always)]
    fn page_start(&self, v: usize) -> usize {
        v & !(self.page_size - 1)
    }
}

impl ProgramHeaderExt for ProgramHeader {
    #[inline(always)]
    fn prot_flags(&self) -> PageProtection {
        let p_flags = &self.p_flags;
        PageProtection {
            read: p_flags & PF_R != 0,
            write: p_flags & PF_W != 0,
            execute: p_flags & PF_X != 0,
        }
    }
}

impl<'ph> fmt::Display for DisplayPFlags<'ph> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let p_flags = &self.0.p_flags;
        let mut write_prot = |mask, s| {
            if p_flags & mask != 0 {
                write!(f, "{}", s)
            } else {
                write!(f, " ")
            }
        };
        write_prot(PF_R, "R")?;
        write_prot(PF_W, "W")?;
        write_prot(PF_X, "X")?;
        Ok(())
    }
}
