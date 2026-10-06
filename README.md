# β₁ ≤ 2·width for four-generated numerical semigroups — Lean 4 formalization (in progress)

**Status: complete (2026-10-07).** `Challenge.lean` states the theorems of record with deliberate `sorry`s;
`Solution.lean` proves both with no `sorry` (axioms: `propext`, `Classical.choice`, `Quot.sound`), via the
development library `SemigroupBetti/` (combinatorial proof of `β₁ ≤ 2W`, Lemmas 0A–16 of
`PROOF_B_lean_writeup.md`, and the bridge `μ(I) ≤ β₁`). See `SemigroupBetti/NOTES.md` for the map from
write-up lemmas to Lean names. Only the inequality half of the bridge is formalized (enough for the
statements of record); `μ(I) = β₁` is not.

## What this is
Let S = ⟨n₀ < n₁ < n₂ < n₃⟩ be a minimally four-generated numerical semigroup of width w = n₃ − n₀, and
W = w / gcd(n₁−n₀, n₂−n₀, n₃−n₀). The first Betti number β₁ of K[S] (the minimal number of generators of the toric
ideal) satisfies β₁ ≤ 2W ≤ 2w. This replaces the conjectured quadratic bound (w+1 choose 2) of Herzog–Stamate (2014) and
Caviglia–Moscariello–Sammartano (2024) in embedding dimension four, and is sharp for every w ≥ 4.
Informal proof: `../../agents/shared/claim_0003/PROOF_B_combinatorial.md` (combinatorial support counting; the version to
be formalized) and `PROOF.md` (Minkowski-based; not formalized). Lean-oriented explicit write-up: `PROOF_B_lean_writeup.md`.

## Layout (Palomar registry convention, as in benkeene/erdos266)
- `Challenge.lean` — statements of record (`SemigroupBetti.beta1_le_two_mul_normalizedWidth`,
  `SemigroupBetti.beta1_le_two_mul_width`), using only Mathlib notions: the toric ideal as the kernel of
  `MvPolynomial.aeval (fun i => X ^ n i)`, and `Submodule.spanRank`.
- `Solution.lean` — the same statements (restated verbatim, without importing `Challenge`, as in erdos266)
  proved by bridges into the library.
- `SemigroupBetti/` — development library: factorizations in ℕ⁴, the fiber graphs ∇_d, the combinatorial β₁,
  the counting lemmas, and the bridge to `spanRank` of the toric ideal.
- `comparator.json`, `formalization.yaml`, pinned `lean-toolchain` and `lake-manifest.json`
  (Mathlib `de5ce8a9a6`, same as erdos266).

## Building
```
lake exe cache get
lake build
```

## Local build note (2026-10-07)
Pinned to Lean `v4.34.0` and Mathlib `5ed2965256`. (The earlier pin v4.34.0-rc1 was dropped because that toolchain's `lake`
crashes with SIGTRAP on macOS 27; `build_direct.sh` is kept only as a lake-free fallback.) `lake build` log: `lake_build.log`.
