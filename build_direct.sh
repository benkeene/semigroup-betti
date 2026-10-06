#!/bin/zsh
# Fallback build without lake (lake 4.34.0-rc1 crashes with SIGTRAP on macOS 27.0.1; see README).
# Compiles the project modules in dependency order with the pinned toolchain's `lean`, using the
# Mathlib/package oleans in .lake/packages (same revisions as lake-manifest.json).
set -e
cd "$(dirname "$0")"
TC=$(cat lean-toolchain | sed 's#leanprover/lean4:#leanprover--lean4---#')
LEAN=~/.elan/toolchains/$TC/bin/lean
OUT=.lake/build/lib/lean
mkdir -p $OUT/SemigroupBetti
LP=""; for d in .lake/packages/*/.lake/build/lib/lean; do LP="$LP$PWD/$d:"; done; LP="$LP$PWD/$OUT"
export LEAN_PATH="$LP"
compile() { # $1 = module path like SemigroupBetti/Basic.lean
  local src=$1; local mod=${src%.lean}
  echo "== $src"; $LEAN "$src" -o "$OUT/$mod.olean" -i "$OUT/$mod.ilean" ${@:2}
}
compile SemigroupBetti/Basic.lean
compile SemigroupBetti/Defs.lean
compile SemigroupBetti/Fiber.lean
compile SemigroupBetti/Critical.lean
compile SemigroupBetti/Bridge.lean
compile SemigroupBetti/Partition.lean
compile SemigroupBetti/Identities.lean
compile SemigroupBetti/Antichain.lean
compile SemigroupBetti/Arith.lean
compile SemigroupBetti/Exceptional.lean
compile SemigroupBetti/Main.lean
compile SemigroupBetti.lean
compile Challenge.lean
compile Solution.lean
echo "build_direct: OK"
