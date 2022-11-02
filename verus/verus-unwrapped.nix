{ lib, fetchFromGitHub, pkgsBoot, craneLib, z3 }:

let
  src = fetchFromGitHub {
    owner = "verus-lang";
    repo = "verus";
    rev = "63df20a5f2782c69d964c873702655d9b73b7408";
    hash = "sha256-Q5Kd1NDSogTqLLhCJD1/rbOu4B1xdZi0LNlwROBZ8mE=";
  };
in craneLib.buildPackage {
  name = "verus-unwrapped";

  inherit src;

  cargoToml = src + "/source/Cargo.toml";
  cargoLock = ./Cargo.lock;
  cargoArtifacts = null;

  nativeBuildInputs = [ z3 ];

  buildInputs = [
    pkgsBoot.llvmPackages_13.llvm
  ];

  postPatch = ''
    cp ${./Cargo.lock} source/Cargo.lock
  '';
  preConfigure = ''
    cd source
  '';

  postInstall = ''
    mkdir $out/lib
    cp ../rust/install/bin/*.so $out/lib
    cp ../rust/install/bin/*.rlib $out/lib
  '';

  # Their tests have hardcoded the path to the Rust install base :/
  doCheck = false;

  dontStrip = true;
  dontPatchELF = true;
  doNotRemoveReferencesToVendorDir = true;

  passthru = {
    inherit src;
  };
}
