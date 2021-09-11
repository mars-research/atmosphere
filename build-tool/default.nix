{ pkgs, lib, stdenv, cacert, cargo, pkg-config, rustPlatform, runCommand, openssl }:

with builtins;

let
  cargoSha256 = "sha256-DbMLXDDtfonq/KeH6tZSnzcb58KI7n4rMwKsgMIn1Gs=";
in rustPlatform.buildRustPackage {
  pname = "build-tool";
  version = "0.1.0";

  src = lib.cleanSourceWith {
    filter = name: type: !(elem (baseNameOf name) ["target"]);
    src = lib.cleanSource ./.;
  };

  inherit cargoSha256;

  buildInputs = [ openssl ];
  nativeBuildInputs = [ pkg-config ];

  postInstall = lib.optionalString (stdenv.hostPlatform == stdenv.buildPlatform) ''
    mkdir completions
    for shell in bash fish zsh; do
      $out/bin/atmo gen-completions $shell > completions/$shell
    done

    mkdir -p "$out/share/"{bash-completion/completions,fish/vendor_completions.d,zsh/site-functions}
    cp completions/bash $out/share/bash-completion/completions/atmo
    cp completions/fish $out/share/fish/vendor_completions.d/atmo.fish
    cp completions/zsh $out/share/zsh/site-functions/_atmo
  '';
}
