#!/bin/zsh
# Compile one module to its olean (for iterative development): ./mk.sh SemigroupBetti/Defs.lean
cd "$(dirname "$0")"
OUT=.lake/build/lib/lean
mkdir -p $OUT/SemigroupBetti
mod=${1%.lean}
./check.sh "$1" -o "$OUT/$mod.olean" -i "$OUT/$mod.ilean"
