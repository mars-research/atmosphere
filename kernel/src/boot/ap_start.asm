; AP boot trampoline
;
; Reference:
; - RedLeaf

default abs

global ap_start16
global ap_start32

section .text

bits 16
ap_start16:
	cli

	; Zero out all segment registers
	xor  ax, ax
	mov  ds, ax
	mov  es, ax
	mov  ss, ax
	mov  gs, ax
	mov  fs, ax

	; Clear direction flag
	cld

	lgdt [gdt32desc]

	mov  eax, cr0

	; Set protected mode bit
	or   eax, 1
	mov  cr0, eax

	jmp gdt32.code:ap_start32

bits 32 
ap_start32:
	; Initialize other segments for proper functioning
	mov eax, gdt32.data

	mov ds, eax
	mov es, eax
	mov ss, eax

	; Zero unused segments
	xor eax, eax
	mov fs, eax
	mov gs, eax

	; Load CR3
	lea ebx, ap_start16
	sub ebx, 8
	mov eax, [ebx]
	mov cr3, eax

	; Enable PAE
	mov eax, cr4
	or eax, 1 << 5
	mov cr4, eax

	; Enable Long Mode
	mov ecx, 0xc0000080
	rdmsr
	or eax, 1 << 8
	wrmsr

	; Enable paging
	mov eax, cr0
	or eax, 1 << 31
	mov cr0, eax

	; Load 64-bit GDT
	lgdt [gdt64.pointer]

	; Jump to long mode
	jmp gdt64.code:start64

bits 64
start64:
	; Reset segments
	mov ax, 0
	mov ss, ax
	mov ds, ax
	mov es, ax
	mov fs, ax
	mov gs, ax

	; Enable PCID
	mov rax, cr4
	or rax, 1 << 17
	mov cr4, rax

	; Load stack
	lea rbx, ap_start16
	sub rbx, 16
	mov rsp, [rbx]

	mov rdi, [rbx - 16]
	call [rbx - 8]

hlt:
	hlt
	jmp hlt

section .rodata
align 4096

gdt32:
	dd 0 ; zero entry
	dd 0
.code: equ $ - gdt32 
	db 0xff
	db 0xff
	db 0
	db 0
	db 0
	db 0x9a
	db 0xcf
	db 0
.data: equ $ - gdt32
	db 0xff
	db 0xff
	db 0
	db 0
	db 0
	db 0x92
	db 0xcf
	db 0
gdt32_end:

gdt32desc:
   dw gdt32_end - gdt32 - 1; last byte in table
   dd gdt32		  ; start of table

align 4096
gdt64:
	dq 0 ; zero entry
.code: equ $ - gdt64
	dq (1<<43) | (1<<44) | (1<<47) | (1<<53) ; code segment
.pointer:
	dw $ - gdt64 - 1
	dq gdt64
