{ lib, pkgsBoot, fetchurl, rustc }:

pkgsBoot.rustc.overrideAttrs (old: {
  version = "1.58.1";

  # We clone Verus's Rust tree ourselves and produce a tarball
  # with vendored dependencies with `./x.py dist`.
  src = fetchurl {
    url = "https://cloud.naive.network/s/MsJPGJnaTdqDjHi/download/rustc-1.58.1-dev-src.tar.gz";
    hash = "sha256-CE46ELm838j3syyhZWzPNjdAiuEn520UsP+8zMZKevU=";
  };

  configureFlags = let
    filtered = builtins.filter (flag: !(lib.hasPrefix "--release-channel" flag)) old.configureFlags;
  in filtered ++ [
    "--release-channel=dev"
  ];

  postInstall = old.postInstall + ''
  '';
})
