; Initialization
;
; References:
;  - RedLeaf
;  - https://www.gnu.org/software/grub/manual/multiboot/multiboot.html
;  - https://intermezzos.github.io/book/first-edition/paging.html
;  - https://wiki.osdev.org/Setting_Up_Long_Mode
;  - https://www.ics.uci.edu/~aburtsev/143A/hw/hw3-boot-into-c/hw3-boot-into-c.html

global start
global bootinfo
global start64
global stack_bottom
global stack_top
extern main

section .text
; We assume that we are already in Protected Mode, and
; we want to enter Long Mode.
;
; We will only map 1GiB of memory here. We export a pointer
; to the page table, so that we can finish mapping everything
; in Rust.

bits 32
start:
    mov esp, stack_top

    call check_multiboot
    call check_cpuid
    call check_long_mode

    call set_up_page_tables
    call enable_paging

	; CHECKED

    ; load the 64-bit GDT
    lgdt [gdt64.pointer]

    ; jump to long mode
    jmp gdt64.code:start64

    hlt ; Halt the processor.

bits 64
; Prints `ERR: ` and the given error code to screen and hangs.
; parameter: error code (in ascii) in al
error64:
    mov dword [0xb8000], 0x4f524f45
    mov dword [0xb8004], 0x4f3a4f52
    mov dword [0xb8008], 0x4f204f20
    mov byte  [0xb800a], al
    hlt

start64:
    ; load 0 into all data segment registers
    mov ax, 0
    mov ss, ax
    mov ds, ax
    mov es, ax
    mov fs, ax
    mov gs, ax

    ; FIXME: argc, argv
    call main

    hlt

bits 32
check_multiboot:
    mov [bootinfo], ebx
    cmp eax, 0x36d76289 ; If multiboot2, this value will be in the eax register on boot.
    jne .no_multiboot
	test ebx, ebx
	jz .no_multiboot
    ret
.no_multiboot:
    mov al, "0"
    jmp error

check_cpuid:
    ; Check if CPUID is supported by attempting to flip the ID bit (bit 21)
    ; in the FLAGS register. If we can flip it, CPUID is available.

    ; Copy FLAGS in to EAX via stack
    pushfd
    pop eax

    ; Copy to ECX as well for comparing later on
    mov ecx, eax

    ; Flip the ID bit
    xor eax, 1 << 21

    ; Copy EAX to FLAGS via the stack
    push eax
    popfd

    ; Copy FLAGS back to EAX (with the flipped bit if CPUID is supported)
    pushfd
    pop eax

    ; Restore FLAGS from the old version stored in ECX (i.e. flipping the
    ; ID bit back if it was ever flipped).
    push ecx
    popfd

    ; Compare EAX and ECX. If they are equal then that means the bit
    ; wasn't flipped, and CPUID isn't supported.
    cmp eax, ecx
    je .no_cpuid
    ret
.no_cpuid:
    mov al, "1"
    jmp error

check_long_mode:
    ; test if extended processor info in available
    mov eax, 0x80000000    ; implicit argument for cpuid
    cpuid                  ; get highest supported argument
    cmp eax, 0x80000001    ; it needs to be at least 0x80000001
    jb .no_long_mode       ; if it's less, the CPU is too old for long mode

    ; use extended info to test if long mode is available
    mov eax, 0x80000001    ; argument for extended processor info
    cpuid                  ; returns various feature bits in ecx and edx
    test edx, 1 << 29      ; test if the LM-bit is set in the D-register
    jz .no_long_mode       ; If it's not set, there is no long mode

    ret
.no_long_mode:
    mov al, "2"
    jmp error

; map some pages, then let Rust handle the rest
set_up_page_tables:
    ; map first P4 entry to P3 table
    mov eax, p3_table
    or eax, 0b11 ; present + writable
    mov [p4_table], eax

    ; map first P3 entry to P2 table
    mov eax, p2_table
    or eax, 0b11 ; present + writable
    mov [p3_table], eax

	; map fourth P3 entry to P2 apic table
	mov eax, p2_apic_table
	or eax, 0b11
	mov [p3_table + 24], eax

    ; == map each P2 entry to a huge 2MiB page
    mov ecx, 0         ; counter variable

.map_p2_table:
    ; map ecx-th P2 entry to a huge page that starts at address 2MiB*ecx
    mov eax, 0x200000  ; 2MiB
    mul ecx            ; start address of ecx-th page
    or eax, 0b10000011 ; present + writable + huge
    mov [p2_table + ecx * 8], eax ; map ecx-th entry

    inc ecx            ; increase counter
    cmp ecx, 512       ; if counter == 512, the whole P2 table is mapped
    jne .map_p2_table  ; else map the next entry

    ; == map each P2_apic entry to a huge 2MiB page
    mov ecx, 0         ; counter variable

.map_p2_apic_table:
    ; map ecx-th P2 entry to a huge page that starts at address 0xc0000000 + 2MiB*ecx
    mov eax, 0x200000  ; 2MiB
    mul ecx            ; start address of ecx-th page
	add eax, 0xc0000000
    or eax, 0b10000011 ; present + writable + huge
    mov [p2_apic_table + ecx * 8], eax ; map ecx-th entry

    inc ecx            ; increase counter
    cmp ecx, 512       ; if counter == 512, the whole P2 table is mapped
    jne .map_p2_apic_table  ; else map the next entry

    ret

enable_paging:
    ; load P4 to cr3 register (cpu uses this to access the P4 table)
    mov eax, p4_table
    mov cr3, eax

    ; enable PAE-flag in cr4 (Physical Address Extension)
    mov eax, cr4
    or eax, 1 << 5
    mov cr4, eax

    ; set the long mode bit in the EFER MSR (model specific register)
    mov ecx, 0xC0000080
    rdmsr
    or eax, 1 << 8
    wrmsr

    ; enable paging in the cr0 register
    mov eax, cr0
    or eax, 1 << 31
    mov cr0, eax

    ret

; Prints `ERR: ` and the given error code to screen and hangs.
; parameter: error code (in ascii) in al
error:
    mov dword [0xb8000], 0x4f524f45
    mov dword [0xb8004], 0x4f3a4f52
    mov dword [0xb8008], 0x4f204f20
    mov byte  [0xb800a], al
    hlt

section .rodata
gdt64:
    dq 0 ; zero entry
.code: equ $ - gdt64
    dq (1<<43) | (1<<44) | (1<<47) | (1<<53) ; code segment
.pointer:
    dw $ - gdt64 - 1
    dq gdt64

section .bss
align 4096

p4_table:
    resb 4096
p3_table:
    resb 4096
p2_table:
    resb 4096
p2_apic_table:
    resb 4096

stack_bottom:
    resb 1024 * 1024 * 32 ; Reserve this many bytes
stack_top:

bootinfo:
    resb 8 ; Place holder to save bootinfo entry
