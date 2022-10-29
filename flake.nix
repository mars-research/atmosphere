{
  description = "RedLeaf Operating System";

  inputs = {
    mars-std.url = "github:mars-research/mars-std";
    crane = {
      url = "github:ipetkov/crane";
      inputs.nixpkgs.follows = "mars-std/nixpkgs";
      inputs.flake-utils.follows = "mars-std/flake-utils";
      inputs.flake-compat.follows = "mars-std/flake-compat";
    };
  };

  outputs = { self, mars-std, crane, ... }: let
    supportedSystems = [ "x86_64-linux" ];
  in mars-std.lib.eachSystem supportedSystems (system: let
    nightlyVersion = "2022-10-20";

    pkgs = mars-std.legacyPackages.${system};
    pinnedRust = pkgs.rust-bin.nightly.${nightlyVersion}.default.override {
      extensions = [ "rust-src" "rust-analyzer-preview" "clippy" ];
      targets = [ "x86_64-unknown-linux-gnu" ];
    };
    rustPlatform = pkgs.makeRustPlatform {
      rustc = pinnedRust;
      cargo = pinnedRust;
    };

    craneLib = (crane.mkLib pkgs).overrideToolchain pinnedRust;
  in {
    packages = {
      build-tool = craneLib.buildPackage {
        src = craneLib.cleanCargoSource ./.;
        cargoExtraArgs = "-p build-tool";
        buildInputs = [ pkgs.openssl ];
        nativeBuildInputs = [ pkgs.pkg-config ];
      };
    };

    devShell = pkgs.mkShell {
      nativeBuildInputs = [
        pinnedRust

        self.packages.${system}.build-tool
      ] ++ (with pkgs; [
        gnumake utillinux cargo-expand cargo-outdated cargo-edit

        gcc10 clang_10 nasm
        grub2 xorriso gdb

        qemu bochs

        python3

        editorconfig-checker

        cachix pkgs.mars-research.mars-tools

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
