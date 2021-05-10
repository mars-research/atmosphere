# TODO: Switch to cargo-make

QEMU ?= $(shell which qemu-system-x86_64)

qemu_common := -enable-kvm -no-reboot
qemu_common += -nographic -serial mon:stdio
qemu_common += -d int,cpu_reset,guest_errors,trace:guest_cpu_exit -D debug.log

.PHONY: clean
clean:
	cargo clean
	rm -rf build

.PHONY: kernel
kernel: build/atmosphere

.PHONY: qemu
qemu: build/atmosphere build/qemu-grub.iso
	sudo $(QEMU) $(qemu_common) \
		-cpu host -m 8G \
		-hda build/qemu-grub.iso \
		-hdb fat:rw:build

.PHONY: build/atmosphere
build/atmosphere:
	cargo build --release

build/qemu-grub.iso: misc/qemu-grub/boot/grub/grub.cfg
	mkdir -p build
	grub-mkrescue -o $@ misc/qemu-grub
