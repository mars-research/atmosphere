{
  description = "RedLeaf Operating System";

  inputs = {
    mars-std.url = "github:mars-research/mars-std";
    kexec-tools.url = "github:mars-research/kexec-tools/mb2-x86-64";
  };

  outputs = { self, mars-std, kexec-tools, ... }: let
    supportedSystems = [ "x86_64-linux" ];
  in mars-std.lib.eachSystem supportedSystems (system: let
    nightlyVersion = "2021-09-07";

    pkgs = mars-std.legacyPackages.${system};
    pinnedRust = pkgs.rust-bin.nightly.${nightlyVersion}.default.override {
      extensions = [ "rust-src" "rust-analyzer-preview" "clippy" ];
      targets = [ "x86_64-unknown-linux-gnu" ];
    };
    rustPlatform = pkgs.makeRustPlatform {
      rustc = pinnedRust;
      cargo = pinnedRust;
    };
  in {
    packages = {
      build-tool = pkgs.callPackage ./build-tool {
        inherit rustPlatform;
        cargo = pinnedRust;
      };
    };

    devShell = pkgs.mkShell {
      nativeBuildInputs = [
        pinnedRust

        self.packages.${system}.build-tool
      ] ++ (with pkgs; [
        gnumake utillinux cargo-expand

        gcc10 clang_10 nasm
        grub2 xorriso gdb

        qemu bochs

        python3

        editorconfig-checker

        cachix pkgs.mars-research.mars-tools

        kexec-tools.defaultPackage.${system}

        # Bareflank pal.py code generator
        cmake
      ]) ++ (with pkgs.python3Packages; [
        # Bareflank pal.py code generator
        lxml pyyaml colorama
      ]);

      inputsFrom = [
        self.packages.${system}.build-tool
      ];
    };
  });
}
