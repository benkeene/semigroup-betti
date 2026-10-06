#!/bin/zsh
# Fast single-file check with the same LEAN_PATH as build_direct.sh (no lake).
cd "$(dirname "$0")"
TC=$(cat lean-toolchain | sed 's#leanprover/lean4:#leanprover--lean4---#')
LEAN=~/.elan/toolchains/$TC/bin/lean
OUT=.lake/build/lib/lean
LP=""; for d in .lake/packages/*/.lake/build/lib/lean; do LP="$LP$PWD/$d:"; done; LP="$LP$PWD/$OUT"
export LEAN_PATH="$LP"
$LEAN "$@"
