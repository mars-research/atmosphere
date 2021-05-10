# QEMU GRUB Configurations

To avoid rebuilding the floppy image with `grub-mkrescue` every time we rebuild the kernel, we load the kernel itself through a virtual FAT filesystem.
