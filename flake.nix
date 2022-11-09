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
    prusti = {
      # Changes yet to be upstreamed
      url = "github:mars-research/prusti-dev/24831959eaf32772a9f2705bb2257beb166d1338";
      inputs.nixpkgs.follows = "mars-std/nixpkgs";
      inputs.rust-overlay.follows = "mars-std/rust-overlay";
      inputs.utils.follows = "mars-std/flake-utils";
    };
  };

  outputs = { self, mars-std, crane, prusti, ... }: let
    supportedSystems = [ "x86_64-linux" "aarch64-linux" ];
  in mars-std.lib.eachSystem supportedSystems (system: let
    nightlyVersion = "2022-10-20";

    pkgs = mars-std.legacyPackages.${system};
    x86Pkgs = mars-std.legacyPackages.x86_64-linux;

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
        pkgs.mars-research.mars-tools
      ] ++ (with pkgs; [
        gnumake utillinux cargo-expand cargo-outdated cargo-edit

        nasm
        grub2 xorriso gdb

        qemu bochs

        python3

        editorconfig-checker

        cachix

        prusti.packages.${system}.prusti
      ]);

      inputsFrom = [
        self.packages.${system}.build-tool
      ];

      # Used by build-tool
      GRUB_X86_MODULES = "${x86Pkgs.grub2}/lib/grub/i386-pc";
    };
  });
}
