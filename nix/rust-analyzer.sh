#!/bin/sh

set -euo pipefail

DIR="$(dirname -- $0)"
RUST=$(dirname $(nix-shell $DIR/../shell.nix --run "which rustc"))

export PATH=$RUST:$PATH
exec $RUST/rust-analyzer "$@"
