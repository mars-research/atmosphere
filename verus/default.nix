{ pkgs, newScope, crane }:

let
  callPackage = newScope self;

  self = rec {
    pkgsBoot = callPackage ./nixpkgs.nix { };

    rustc = callPackage ./rustc.nix { };
    cargo = pkgs.cargo.override {
      inherit rustc;
    };
    rust = pkgs.symlinkJoin {
      name = "rust-verus";
      paths = [ rustc cargo ];
    };

    rustPlatform = pkgs.makeRustPlatform {
      inherit rustc cargo;
    };
    craneLib = (crane.mkLib pkgsBoot).overrideToolchain rust;

    z3 = callPackage ./z3.nix {
      inherit (pkgs) z3;
    };

    verus-unwrapped = callPackage ./verus-unwrapped.nix { };
    verus = callPackage ./verus.nix { };
  };
in self
