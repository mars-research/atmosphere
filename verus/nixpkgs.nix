# Building Verus requires a older Rust version to bootstrap (v minus 1),
# as well as an older version of LLVM. So let's just build with an older
# nixpkgs tree that had Rust 1.58 :/

{ pkgs }:
let
  nixpkgs = builtins.fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/23d785aa6f853e6cf3430119811c334025bbef55.tar.gz";
    sha256 = "sha256:00fvaap8ibhy63jjsvk61sbkspb8zj7chvg13vncn7scr4jlzd60";
  };
in import nixpkgs {
  inherit (pkgs) system overlays;
}
