; Multiboot 1, not Multiboot 2

section .multiboot_header
header_start:
	; bit 0: Page-align modules
	; bit 1: Must pass memory map
	; bit 2: Must pass video mode table

	flags equ 0b011
    dd 0x1badb002 ; magic number (multiboot)
    dd flags      ; flags

    ; checksum
	dd -0x1badb002 - flags

	dd 0 ; header_addr
	dd 0 ; load_addr
	dd 0 ; load_end_addr
	dd 0 ; bss_end_addr
	dd 0 ; entry_addr
	dd 0 ; mode_type
	dd 1024 ; width
	dd 768 ; height
	dd 32 ; depth
header_end:
