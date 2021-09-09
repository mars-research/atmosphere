{ pkgs, lib, stdenv, cacert, cargo, pkg-config, rustPlatform, runCommand, openssl }:

with builtins;

let
  src = lib.cleanSourceWith {
    filter = name: type: !(elem (baseNameOf name) ["target"]);
    src = lib.cleanSource ./.;
  };

  lockHash = "sha256-77JpgvBhdDilUBevf2ugQdprcLlyGvsreGlQrU1VBmM=";
  vendorHash = "sha256-b7JV+RLhz/XpdxCzvo1vJv9/82GrAD391lINkbW5/hs=";

  # Giant hack to build this in isolation from other workspace members
  # We can't pull in the entire workspace because it will require a rebuild
  # on every single change.
  lock = stdenv.mkDerivation {
    name = "atmo-lock";

    outputHashMode = "recursive";
    outputHashAlgo = "sha256";
    outputHash = lockHash;

    inherit src;

    nativeBuildInputs = [ cacert cargo pkg-config ];
    buildInputs = [ openssl ];

    buildPhase = ''
      export SOURCE_DATE_EPOCH=1
      export CARGO_HOME=$(mktemp -d cargo-home.XXX)

      cat ${../Cargo.lock} > Cargo.lock

      cargo check
    '';

    installPhase = ''
      cp Cargo.lock $out
    '';

    impureEnvVars = lib.fetchers.proxyImpureEnvVars;
  };

  lockedSrc = runCommand "atmo-src" {} ''
    cp -r ${src} $out
    chmod u+w $out
    cat ${lock} > $out/Cargo.lock
  '';
in rustPlatform.buildRustPackage {
  pname = "atmo";
  version = "0.1.0";

  src = lockedSrc;

  nativeBuildInputs = [ pkg-config ];
  buildInputs = [ openssl ];

  cargoSha256 = vendorHash;
}
