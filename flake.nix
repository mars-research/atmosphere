{
  description = "Atmosphere";

  inputs = {
    mars-std.url = "github:mars-research/mars-std";
    crane = {
      url = "github:ipetkov/crane";
      inputs.nixpkgs.follows = "mars-std/nixpkgs";
      inputs.flake-utils.follows = "mars-std/flake-utils";
      inputs.flake-compat.follows = "mars-std/flake-compat";
    };
    verus = {
      url = "github:mars-research/verus/mars";
      inputs.nixpkgs.follows = "mars-std/nixpkgs";
      inputs.flake-utils.follows = "mars-std/flake-utils";
      inputs.flake-compat.follows = "mars-std/flake-compat";
      inputs.crane.follows = "crane";
    };
  };

  outputs = { self, mars-std, crane, verus, ... }: let
    supportedSystems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" ];
  in mars-std.lib.eachSystem supportedSystems (system: let
    pkgs = mars-std.legacyPackages.${system};
    inherit (pkgs) lib;
    x86Pkgs = mars-std.legacyPackages.x86_64-linux;
    x86Tools = pkgs.pkgsCross.gnu64;

    pinnedRust = pkgs.rust-bin.fromRustupToolchainFile ./rust-toolchain.toml;
    rustPlatform = pkgs.makeRustPlatform {
      rustc = pinnedRust;
      cargo = pinnedRust;
    };

    craneLib = (crane.mkLib pkgs).overrideToolchain pinnedRust;

    pinnedVerus = verus.packages.${system};

    mkShell = pkgs.mkShell.override {
      stdenv = pkgs.llvmPackages_14.stdenv;
    };

    mkCargoShim = sub: pkgs.writeShellScriptBin "cargo-${sub}" ''
      shift 1
      exec atmo ${sub} "$@"
    '';
  in {
    devShell = mkShell {
      nativeBuildInputs = [
        pinnedRust
        pinnedVerus.verus-no-std
        pinnedVerus.line-count

        pkgs.mars-research.mars-tools
      ] ++ (with pkgs; [
        llvmPackages_14.bintools
        llvmPackages_14.llvm

        cargo-expand cargo-outdated cargo-edit

        pkg-config

        x86Pkgs.grub2

        util-linuxMinimal

        nasm

        gdb

        qemu

        editorconfig-checker

        jq

        (python3.withPackages (py: with py; [ z3 ]))

        (pkgs.writeShellScriptBin "x86_64.ld" ''
          exec ${x86Tools.buildPackages.bintools}/bin/${x86Tools.stdenv.cc.targetPrefix}ld "$@"
        '')

        (pkgs.writeShellScriptBin "atmo" ''
          set -euo pipefail
          metadata=$(cargo metadata --format-version 1)
          root=$(echo $metadata | jq -r '.workspace_root')
          target_dir=$(echo $metadata | jq -r '.target_directory')
          pushd "$root/build-tool" >/dev/null
          cargo build --quiet

          "$target_dir/debug/atmo" "$@"
        '')

        (mkCargoShim "verify")
        (mkCargoShim "gdb")
      ]);

      buildInputs = [ pkgs.openssl ];

      RUSTC_BOOTSTRAP = "1";

      # Used by build-tool
      GRUB_X86_MODULES = "${x86Pkgs.grub2}/lib/grub/i386-pc";
    };
  });
}
