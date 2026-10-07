# β₁ ≤ 2·width for four-generated numerical semigroups — Lean 4 formalization

**Status: complete.** `Challenge.lean` states the theorems of record with deliberate `sorry`s;
`Solution.lean` proves both with no `sorry` (axioms: `propext`, `Classical.choice`, `Quot.sound`), via the
development library `SemigroupBetti/` (combinatorial proof of `β₁ ≤ 2W`, Lemmas 0A–16 of
`PROOF_B_lean_writeup.md`, and the bridge `μ(I) ≤ β₁`). See `SemigroupBetti/NOTES.md` for the map from
write-up lemmas to Lean names. Only the inequality half of the bridge is formalized (enough for the
statements of record); `μ(I) = β₁` is not.

## What this is
Let S = ⟨n₀ < n₁ < n₂ < n₃⟩ be a minimally four-generated numerical semigroup of width w = n₃ − n₀, and
W = w / gcd(n₁−n₀, n₂−n₀, n₃−n₀). The first Betti number β₁ of K[S] (the minimal number of generators of the toric
ideal) satisfies β₁ ≤ 2W ≤ 2w. This replaces the conjectured quadratic bound (w+1 choose 2) of Herzog–Stamate (2014) and
Caviglia–Moscariello–Sammartano (2024) in embedding dimension four. The bound is sharp for every w ≥ 4; sharpness is an
informal companion result and is **not** formalized here.

## Layout
- `Challenge.lean` — statements of record (`SemigroupBetti.beta1_le_two_mul_normalizedWidth`,
  `SemigroupBetti.beta1_le_two_mul_width`), using only Mathlib notions: the toric ideal as the kernel of
  `MvPolynomial.aeval (fun i => X ^ n i)`, and `Submodule.spanRank`.
- `Solution.lean` — the same statements (restated verbatim, without importing `Challenge`) proved by bridges into
  the library.
- `SemigroupBetti/` — development library: factorizations in ℕ⁴, the fiber graphs ∇_d, the combinatorial β₁,
  the counting lemmas, and the bridge to `spanRank` of the toric ideal.
- `comparator.json` — the declarations `lake comparator` must match and the permitted axioms.
- `formalization.yaml` — Palomar metadata (v0.4); `CORRESPONDENCE.md` — informal ↔ formal statement argument and
  build record; `LICENSE` — Apache-2.0 (matches `project.license`).
- `scripts/verify-comparator.sh`, `scripts/validate-formalization.rb` — copied from PalomarTemplate;
  `scripts/check-lean-sources.py` — minimal local check of Palomar's module-header and file-size rules.
- `lean-toolchain` (`leanprover/lean4:v4.35.0-rc3`), `lakefile.toml` (Mathlib tag `v4.35.0-rc3`, commit
  `c55e6e786f`), committed `lake-manifest.json`.

Every `.lean` file uses Lean's module system (`module`, `public import`, `@[expose] public section`).

## Building
```
lake exe cache get
lake build
```
(On 2026-10-06 the Mathlib cache for `v4.35.0-rc3` was incomplete, so `lake build` compiled about 4,900 Mathlib modules
locally; this takes roughly half an hour on a 16-core machine.)

## Verification
```
python3 scripts/check-lean-sources.py     # module headers, file-size limits
ruby scripts/validate-formalization.rb    # formalization.yaml: YAML, Apache-2.0 licence, no TEMPLATE values
./scripts/verify-comparator.sh            # lake comparator: Solution vs Challenge (Linux + bubblewrap only)
```
GitHub Actions (`.github/workflows/ci.yml`, adapted from PalomarTemplate) runs the metadata/licence checks, the
README submission-link check, the Lean source check and `lake build` on every push to `main` and on manual dispatch.
The template's Comparator job (which installs bubblewrap and relaxes the runner's AppArmor user-namespace restriction
before running `scripts/verify-comparator.sh`) is **not yet** in the workflow; until it is added, Comparator has to be
run on a Linux machine with `bwrap`.

## Submission
Palomar submissions go through https://submit.palomar-registry.org/ with the full 40-character commit SHA.

## History
Earlier pins were Lean v4.34.0-rc1 / Mathlib `de5ce8a9a6` (dropped because that toolchain's `lake` crashed with SIGTRAP
on macOS 27) and v4.34.0 / `5ed2965256`. The lake-free helper scripts used then (`build_direct.sh`, `check.sh`,
`mk.sh`) were removed with the move to v4.35.0-rc3 and the module system.
