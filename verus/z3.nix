{ lib, fetchFromGitHub, z3 }:

z3.overrideAttrs (old: rec {
  version = "4.10.1";
  src = fetchFromGitHub {
    owner = "Z3Prover";
    repo = "z3";
    rev = "z3-${version}";
    hash = "sha256-1SAutuTtiBVqop5F0RKqtyVFH3gjR7PNwZC+z/0HPfw=";
  };
})
