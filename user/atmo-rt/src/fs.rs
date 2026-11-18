//! An in-memory file system.
//!
//! Files and directories are entries of one table, named by their full path.
//! File contents are in pages from [`crate::mem`]. A program can register
//! data that is part of its image as a read-only initial file; the data is
//! copied the first time the file is written.

use core::cell::UnsafeCell;
use core::ffi::{c_char, CStr};

use crate::mem;
use crate::sys::PAGE_SIZE;
use crate::time;

pub const MAX_NODES: usize = 256;
pub const MAX_OPEN: usize = 96;
pub const PATH_MAX: usize = 128;

/// Open flags of the C interface.
pub const READ: u32 = 1;
pub const WRITE: u32 = 2;
pub const CREATE: u32 = 4;
pub const TRUNCATE: u32 = 8;

/// Errors of the C interface, as negative results.
pub const E_NOT_FOUND: i32 = -2;
pub const E_IO: i32 = -5;
pub const E_BAD_HANDLE: i32 = -9;
pub const E_NO_MEMORY: i32 = -12;
pub const E_ACCESS: i32 = -13;
pub const E_BUSY: i32 = -16;
pub const E_EXISTS: i32 = -17;
pub const E_NOT_DIR: i32 = -20;
pub const E_IS_DIR: i32 = -21;
pub const E_INVALID: i32 = -22;
pub const E_NO_SPACE: i32 = -28;
pub const E_NAME_TOO_LONG: i32 = -36;
pub const E_NOT_EMPTY: i32 = -39;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Free,
    File,
    Dir,
}

#[derive(Clone, Copy)]
struct Node {
    kind: Kind,
    path: [u8; PATH_MAX],
    path_len: usize,
    data: *mut u8,
    size: usize,
    /// Pages that back `data`. Zero for image data and for empty files.
    pages: usize,
    /// How many handles are open on the node.
    open: u32,
    /// Modification time in nanoseconds of the monotonic clock.
    mtime: u64,
}

const FREE_NODE: Node = Node {
    kind: Kind::Free,
    path: [0; PATH_MAX],
    path_len: 0,
    data: core::ptr::null_mut(),
    size: 0,
    pages: 0,
    open: 0,
    mtime: 0,
};

#[derive(Clone, Copy)]
struct Handle {
    used: bool,
    node: usize,
    pos: usize,
    flags: u32,
}

const FREE_HANDLE: Handle = Handle { used: false, node: 0, pos: 0, flags: 0 };

struct Fs {
    nodes: [Node; MAX_NODES],
    handles: [Handle; MAX_OPEN],
}

struct Shared(UnsafeCell<Fs>);
// The runtime runs in one kernel thread and does not switch tasks inside
// this module.
unsafe impl Sync for Shared {}

static FS: Shared =
    Shared(UnsafeCell::new(Fs { nodes: [FREE_NODE; MAX_NODES], handles: [FREE_HANDLE; MAX_OPEN] }));

fn fs() -> &'static mut Fs {
    unsafe { &mut *FS.0.get() }
}

/// The canonical form of a path: no leading slash, no leading `./`, and no
/// trailing slash. The root is the empty path. A relative path is taken from
/// the root; there is no current directory.
unsafe fn path_bytes<'a>(path: *const c_char) -> Result<&'a [u8], i32> {
    if path.is_null() {
        return Err(E_INVALID);
    }
    let mut bytes = CStr::from_ptr(path).to_bytes();
    if bytes.is_empty() {
        return Err(E_INVALID);
    }
    loop {
        if bytes.first() == Some(&b'/') {
            bytes = &bytes[1..];
        } else if bytes.starts_with(b"./") {
            bytes = &bytes[2..];
        } else if bytes == b"." {
            bytes = &bytes[1..];
        } else {
            break;
        }
    }
    while bytes.last() == Some(&b'/') {
        bytes = &bytes[..bytes.len() - 1];
    }
    if bytes.len() > PATH_MAX {
        return Err(E_NAME_TOO_LONG);
    }
    Ok(bytes)
}

fn find(f: &Fs, path: &[u8]) -> Option<usize> {
    f.nodes.iter().position(|n| n.kind != Kind::Free && &n.path[..n.path_len] == path)
}

/// The directory part of a path.
fn parent(path: &[u8]) -> &[u8] {
    match path.iter().rposition(|&b| b == b'/') {
        Some(i) => &path[..i],
        None => &path[..0],
    }
}

/// Whether `path` names a directory. The root always exists.
fn is_dir(f: &Fs, path: &[u8]) -> bool {
    path.is_empty() || matches!(find(f, path), Some(i) if f.nodes[i].kind == Kind::Dir)
}

fn create(f: &mut Fs, path: &[u8], kind: Kind) -> Result<usize, i32> {
    if path.is_empty() {
        return Err(E_EXISTS);
    }
    if !is_dir(f, parent(path)) {
        return Err(E_NOT_FOUND);
    }
    let i = f.nodes.iter().position(|n| n.kind == Kind::Free).ok_or(E_NO_SPACE)?;
    let node = &mut f.nodes[i];
    *node = FREE_NODE;
    node.kind = kind;
    node.path[..path.len()].copy_from_slice(path);
    node.path_len = path.len();
    node.mtime = time::now();
    Ok(i)
}

fn release_data(node: &mut Node) {
    if node.pages != 0 {
        mem::free_pages(node.data as usize, node.pages);
    }
    node.data = core::ptr::null_mut();
    node.pages = 0;
    node.size = 0;
}

/// Makes room for `capacity` bytes in pages that the node owns.
fn reserve(node: &mut Node, capacity: usize) -> Result<(), i32> {
    if node.pages != 0 && capacity <= node.pages * PAGE_SIZE {
        return Ok(());
    }
    // Grow by at least half so that appending is not quadratic.
    let want = capacity.max(node.pages * PAGE_SIZE * 3 / 2).max(PAGE_SIZE);
    let pages = want.div_ceil(PAGE_SIZE);
    let data = mem::alloc_pages(pages).ok_or(E_NO_MEMORY)? as *mut u8;
    if node.size != 0 {
        unsafe { core::ptr::copy_nonoverlapping(node.data, data, node.size) };
    }
    if node.pages != 0 {
        mem::free_pages(node.data as usize, node.pages);
    }
    node.data = data;
    node.pages = pages;
    Ok(())
}

fn handle(f: &mut Fs, fd: i32) -> Result<&mut Handle, i32> {
    if fd < 0 || fd as usize >= MAX_OPEN || !f.handles[fd as usize].used {
        return Err(E_BAD_HANDLE);
    }
    Ok(&mut f.handles[fd as usize])
}

fn code(result: Result<i64, i32>) -> i64 {
    match result {
        Ok(value) => value,
        Err(e) => e as i64,
    }
}

/// Registers `size` bytes at `data` as the contents of a new file. The data
/// must stay valid. Missing parent directories are created.
#[no_mangle]
pub unsafe extern "C" fn art_fs_add_static(path: *const c_char, data: *const u8, size: usize) -> i32 {
    code((|| {
        let path = path_bytes(path)?;
        let f = fs();
        if find(f, path).is_some() {
            return Err(E_EXISTS);
        }
        make_parents(f, path)?;
        let i = create(f, path, Kind::File)?;
        f.nodes[i].data = data as *mut u8;
        f.nodes[i].size = size;
        Ok(0)
    })()) as i32
}

fn make_parents(f: &mut Fs, path: &[u8]) -> Result<(), i32> {
    let dir = parent(path);
    if is_dir(f, dir) {
        return Ok(());
    }
    if find(f, dir).is_some() {
        return Err(E_NOT_DIR);
    }
    make_parents(f, dir)?;
    create(f, dir, Kind::Dir).map(|_| ())
}

/// Opens a file and returns a handle, or a negative error.
#[no_mangle]
pub unsafe extern "C" fn art_fs_open(path: *const c_char, flags: u32) -> i32 {
    code((|| {
        let path = path_bytes(path)?;
        let f = fs();
        let node = match find(f, path) {
            Some(i) if f.nodes[i].kind == Kind::Dir => return Err(E_IS_DIR),
            Some(i) => i,
            None if flags & CREATE != 0 => create(f, path, Kind::File)?,
            None => return Err(E_NOT_FOUND),
        };
        let fd = f.handles.iter().position(|h| !h.used).ok_or(E_NO_SPACE)?;
        if flags & TRUNCATE != 0 && flags & WRITE != 0 {
            release_data(&mut f.nodes[node]);
            f.nodes[node].mtime = time::now();
        }
        f.nodes[node].open += 1;
        f.handles[fd] = Handle { used: true, node, pos: 0, flags };
        Ok(fd as i64)
    })()) as i32
}

#[no_mangle]
pub extern "C" fn art_fs_close(fd: i32) -> i32 {
    code((|| {
        let f = fs();
        let h = handle(f, fd)?;
        h.used = false;
        let node = h.node;
        f.nodes[node].open -= 1;
        Ok(0)
    })()) as i32
}

/// Reads up to `count` bytes. Returns the number read, zero at the end.
#[no_mangle]
pub unsafe extern "C" fn art_fs_read(fd: i32, buf: *mut u8, count: usize) -> i64 {
    code((|| {
        let f = fs();
        let h = *handle(f, fd)?;
        if h.flags & READ == 0 {
            return Err(E_ACCESS);
        }
        let node = &f.nodes[h.node];
        let n = count.min(node.size.saturating_sub(h.pos));
        if n != 0 {
            core::ptr::copy_nonoverlapping(node.data.add(h.pos), buf, n);
        }
        f.handles[fd as usize].pos = h.pos + n;
        Ok(n as i64)
    })())
}

/// Writes `count` bytes at the position of the handle.
#[no_mangle]
pub unsafe extern "C" fn art_fs_write(fd: i32, buf: *const u8, count: usize) -> i64 {
    code((|| {
        let f = fs();
        let h = *handle(f, fd)?;
        if h.flags & WRITE == 0 {
            return Err(E_ACCESS);
        }
        let end = h.pos.checked_add(count).ok_or(E_INVALID)?;
        let node = &mut f.nodes[h.node];
        reserve(node, end.max(node.size))?;
        if h.pos > node.size {
            core::ptr::write_bytes(node.data.add(node.size), 0, h.pos - node.size);
        }
        core::ptr::copy_nonoverlapping(buf, node.data.add(h.pos), count);
        node.size = node.size.max(end);
        node.mtime = time::now();
        f.handles[fd as usize].pos = end;
        Ok(count as i64)
    })())
}

/// Moves the position of a handle. `whence` is 0 for the start, 1 for the
/// current position, 2 for the end. Returns the new position.
#[no_mangle]
pub extern "C" fn art_fs_seek(fd: i32, offset: i64, whence: u32) -> i64 {
    code((|| {
        let f = fs();
        let h = *handle(f, fd)?;
        let base = match whence {
            0 => 0,
            1 => h.pos as i64,
            2 => f.nodes[h.node].size as i64,
            _ => return Err(E_INVALID),
        };
        let pos = base.checked_add(offset).ok_or(E_INVALID)?;
        if pos < 0 {
            return Err(E_INVALID);
        }
        f.handles[fd as usize].pos = pos as usize;
        Ok(pos)
    })())
}

/// Sets the size of an open file.
#[no_mangle]
pub extern "C" fn art_fs_truncate(fd: i32, size: usize) -> i32 {
    code((|| {
        let f = fs();
        let h = *handle(f, fd)?;
        if h.flags & WRITE == 0 {
            return Err(E_ACCESS);
        }
        let node = &mut f.nodes[h.node];
        if size == 0 {
            release_data(node);
        } else {
            reserve(node, size.max(node.size))?;
            if size > node.size {
                unsafe { core::ptr::write_bytes(node.data.add(node.size), 0, size - node.size) };
            }
            node.size = size;
        }
        node.mtime = time::now();
        Ok(0)
    })()) as i32
}

#[repr(C)]
pub struct Stat {
    pub size: u64,
    /// Nanoseconds of the monotonic clock at the last change.
    pub mtime: u64,
    pub is_dir: u32,
}

#[no_mangle]
pub unsafe extern "C" fn art_fs_stat(path: *const c_char, out: *mut Stat) -> i32 {
    code((|| {
        let path = path_bytes(path)?;
        let f = fs();
        if path.is_empty() {
            out.write(Stat { size: 0, mtime: 0, is_dir: 1 });
            return Ok(0);
        }
        let node = &f.nodes[find(f, path).ok_or(E_NOT_FOUND)?];
        out.write(Stat {
            size: node.size as u64,
            mtime: node.mtime,
            is_dir: (node.kind == Kind::Dir) as u32,
        });
        Ok(0)
    })()) as i32
}

/// Removes a file that is not open.
#[no_mangle]
pub unsafe extern "C" fn art_fs_remove(path: *const c_char) -> i32 {
    code((|| {
        let path = path_bytes(path)?;
        let f = fs();
        let i = find(f, path).ok_or(E_NOT_FOUND)?;
        if f.nodes[i].kind == Kind::Dir {
            return Err(E_IS_DIR);
        }
        if f.nodes[i].open != 0 {
            return Err(E_BUSY);
        }
        release_data(&mut f.nodes[i]);
        f.nodes[i].kind = Kind::Free;
        Ok(0)
    })()) as i32
}

/// Renames a file or a directory. The new name must not exist. Renaming a
/// directory renames everything below it.
#[no_mangle]
pub unsafe extern "C" fn art_fs_rename(from: *const c_char, to: *const c_char) -> i32 {
    code((|| {
        let from = path_bytes(from)?;
        let to = path_bytes(to)?;
        let f = fs();
        let i = find(f, from).ok_or(E_NOT_FOUND)?;
        if find(f, to).is_some() {
            return Err(E_EXISTS);
        }
        if to.is_empty() || !is_dir(f, parent(to)) {
            return Err(E_NOT_FOUND);
        }
        if f.nodes[i].kind == Kind::Dir {
            if to == from || is_below(from, to) {
                return Err(E_INVALID);
            }
            // Check every new path before changing any.
            for node in f.nodes.iter() {
                if node.kind != Kind::Free
                    && is_below(from, &node.path[..node.path_len])
                    && node.path_len - from.len() + to.len() > PATH_MAX
                {
                    return Err(E_NAME_TOO_LONG);
                }
            }
            for node in f.nodes.iter_mut() {
                if node.kind != Kind::Free && is_below(from, &node.path[..node.path_len]) {
                    let mut path = [0u8; PATH_MAX];
                    let rest = node.path_len - from.len();
                    path[..to.len()].copy_from_slice(to);
                    path[to.len()..to.len() + rest]
                        .copy_from_slice(&node.path[from.len()..node.path_len]);
                    node.path = path;
                    node.path_len = to.len() + rest;
                }
            }
        }
        let node = &mut f.nodes[i];
        node.path = [0; PATH_MAX];
        node.path[..to.len()].copy_from_slice(to);
        node.path_len = to.len();
        Ok(0)
    })()) as i32
}

/// Creates a directory. With `parents`, missing parent directories are
/// created and an existing directory is not an error.
#[no_mangle]
pub unsafe extern "C" fn art_fs_mkdir(path: *const c_char, parents: bool) -> i32 {
    code((|| {
        let path = path_bytes(path)?;
        let f = fs();
        if is_dir(f, path) {
            return if parents { Ok(0) } else { Err(E_EXISTS) };
        }
        if find(f, path).is_some() {
            return Err(E_EXISTS);
        }
        if parents {
            make_parents(f, path)?;
        }
        create(f, path, Kind::Dir).map(|_| 0)
    })()) as i32
}

/// Whether `path` is anywhere below the directory `dir`.
fn is_below(dir: &[u8], path: &[u8]) -> bool {
    if dir.is_empty() {
        return !path.is_empty();
    }
    path.len() > dir.len() + 1 && &path[..dir.len()] == dir && path[dir.len()] == b'/'
}

/// The name of `path` inside the directory `dir`, if it is directly inside.
fn child_name<'a>(dir: &[u8], path: &'a [u8]) -> Option<&'a [u8]> {
    if !is_below(dir, path) {
        return None;
    }
    let name = if dir.is_empty() { path } else { &path[dir.len() + 1..] };
    if name.contains(&b'/') {
        None
    } else {
        Some(name)
    }
}

/// Removes an empty directory.
#[no_mangle]
pub unsafe extern "C" fn art_fs_rmdir(path: *const c_char) -> i32 {
    code((|| {
        let path = path_bytes(path)?;
        let f = fs();
        let i = find(f, path).ok_or(E_NOT_FOUND)?;
        if f.nodes[i].kind != Kind::Dir {
            return Err(E_NOT_DIR);
        }
        if f.nodes.iter().any(|n| n.kind != Kind::Free && is_below(path, &n.path[..n.path_len])) {
            return Err(E_NOT_EMPTY);
        }
        f.nodes[i].kind = Kind::Free;
        Ok(0)
    })()) as i32
}

/// Removes everything below a directory. Fails if a file below it is open.
#[no_mangle]
pub unsafe extern "C" fn art_fs_clear(path: *const c_char) -> i32 {
    code((|| {
        let path = path_bytes(path)?;
        let f = fs();
        if f.nodes.iter().any(|n| {
            n.kind != Kind::Free && n.open != 0 && is_below(path, &n.path[..n.path_len])
        }) {
            return Err(E_BUSY);
        }
        for node in f.nodes.iter_mut() {
            if node.kind != Kind::Free && is_below(path, &node.path[..node.path_len]) {
                release_data(node);
                node.kind = Kind::Free;
            }
        }
        Ok(0)
    })()) as i32
}

/// Reads one entry of a directory. `cursor` starts at zero and the call
/// advances it. Returns 1 with the entry name in `name`, 0 at the end, or a
/// negative error.
#[no_mangle]
pub unsafe extern "C" fn art_fs_readdir(
    path: *const c_char,
    cursor: *mut u32,
    name: *mut u8,
    capacity: usize,
) -> i32 {
    code((|| {
        let path = path_bytes(path)?;
        let f = fs();
        if !is_dir(f, path) {
            return Err(E_NOT_DIR);
        }
        let mut i = *cursor as usize;
        while i < MAX_NODES {
            let node = &f.nodes[i];
            i += 1;
            if node.kind == Kind::Free {
                continue;
            }
            if let Some(entry) = child_name(path, &node.path[..node.path_len]) {
                if entry.len() + 1 > capacity {
                    return Err(E_NAME_TOO_LONG);
                }
                core::ptr::copy_nonoverlapping(entry.as_ptr(), name, entry.len());
                name.add(entry.len()).write(0);
                *cursor = i as u32;
                return Ok(1);
            }
        }
        *cursor = i as u32;
        Ok(0)
    })()) as i32
}

/// The bytes in files below a directory, and the number of free table
/// entries.
#[no_mangle]
pub unsafe extern "C" fn art_fs_usage(path: *const c_char, bytes: *mut u64, free_nodes: *mut u32) -> i32 {
    code((|| {
        let path = path_bytes(path)?;
        let f = fs();
        let mut total = 0u64;
        let mut free = 0u32;
        for node in f.nodes.iter() {
            if node.kind == Kind::Free {
                free += 1;
            } else if is_below(path, &node.path[..node.path_len]) {
                total += node.size as u64;
            }
        }
        bytes.write(total);
        free_nodes.write(free);
        Ok(0)
    })()) as i32
}

// ---------------------------------------------------------------------------
// Initial files from a tar archive

const TAR_BLOCK: usize = 512;

/// Parses an octal field of a tar header.
fn tar_octal(field: &[u8]) -> usize {
    let mut value = 0usize;
    for &b in field {
        if (b'0'..=b'7').contains(&b) {
            value = value * 8 + (b - b'0') as usize;
        } else if value != 0 || (b != b' ' && b != 0) {
            break;
        }
    }
    value
}

fn tar_str(field: &[u8]) -> &[u8] {
    let end = field.iter().position(|&b| b == 0).unwrap_or(field.len());
    &field[..end]
}

/// Registers the regular files of a ustar archive as initial files below the
/// root. The archive must stay valid; file contents are not copied. Returns
/// the number of files, or a negative error.
#[no_mangle]
pub unsafe extern "C" fn art_fs_add_tar(data: *const u8, size: usize) -> i32 {
    if data.is_null() {
        return E_INVALID;
    }
    let archive = core::slice::from_raw_parts(data, size);
    let mut offset = 0;
    let mut count = 0;
    while offset + TAR_BLOCK <= archive.len() {
        let header = &archive[offset..offset + TAR_BLOCK];
        if header.iter().all(|&b| b == 0) {
            break;
        }
        let name = tar_str(&header[0..100]);
        let prefix = if &header[257..262] == b"ustar" { tar_str(&header[345..500]) } else { &header[..0] };
        let length = tar_octal(&header[124..136]);
        let kind = header[156];
        let body = offset + TAR_BLOCK;
        if body + length > archive.len() {
            return E_INVALID;
        }
        if kind == b'0' || kind == 0 {
            // The path is prefix/name, with a terminator for the C interface.
            let mut path = [0u8; PATH_MAX + 2];
            let mut len = 0;
            for part in [prefix, name] {
                if part.is_empty() {
                    continue;
                }
                if len + part.len() + 1 > PATH_MAX {
                    return E_NAME_TOO_LONG;
                }
                if len != 0 {
                    path[len] = b'/';
                    len += 1;
                }
                path[len..len + part.len()].copy_from_slice(part);
                len += part.len();
            }
            if len != 0 {
                let status =
                    art_fs_add_static(path.as_ptr() as *const c_char, archive[body..].as_ptr(), length);
                if status < 0 {
                    return status;
                }
                count += 1;
            }
        }
        offset = body + length.div_ceil(TAR_BLOCK) * TAR_BLOCK;
    }
    count
}
