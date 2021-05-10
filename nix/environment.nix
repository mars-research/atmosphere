let
  pkgs = import ./nixpkgs.nix;

  rustPlatform = pkgs.makeRustPlatform {
    rustc = pkgs.rust-pinned;
    cargo = pkgs.rust-pinned;
  };
in {
  inherit pkgs;

  dependencies = with pkgs; [
    rust-pinned

    cargo-make

    gnumake utillinux

    gcc10 clang_10 nasm
    qemu grub2 xorriso

    python3
  ];
}
