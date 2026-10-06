/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/
module

public import Mathlib

/-! # Development library for the combinatorial proof of `β₁ ≤ 2W` (skeleton). -/

@[expose] public section

namespace SemigroupBetti

/-- A factorization of `d` with respect to the generator vector `n` is `z : Fin 4 → ℕ` with
`∑ i, z i * n i = d`. -/
def IsFactorization (n : Fin 4 → ℕ) (d : ℕ) (z : Fin 4 → ℕ) : Prop :=
  ∑ i, z i * n i = d

end SemigroupBetti
