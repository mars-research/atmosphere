#!/bin/sh

set -euo pipefail

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
RUST=$(nix-build --quiet --no-out-link -E "with import $DIR/nixpkgs.nix; rust-pinned")

export PATH=$RUST/bin:$PATH
exec $RUST/bin/rust-analyzer "$@"
