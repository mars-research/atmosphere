# Early-Boot

## Linux/x86 Boot Protocol

We implement the [Linux/x86 Boot Protocol](https://www.kernel.org/doc/html/latest/x86/boot.html).
We set the following in the header:
- xloadflags.XLF_KERNEL_64: The bootloader will drop us directly in long mode with [some region](https://www.kernel.org/doc/html/latest/x86/boot.html) identity-mapped.

## Kexec Boot Protocol


## crt0
