/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/
module

public import SemigroupBetti.Exceptional

/-!
# The combinatorial theorem `β₁ ≤ 2W ≤ 2w`

Write-up `PROOF_B_lean_writeup.md`: Lemma 13 (non-exceptional cases) and Lemma 16 (exceptional
case `(s,t) = (1,1)`, i.e. `(A,B) = (1, W-1)`).
-/

@[expose] public section

namespace SemigroupBetti

namespace GenData

variable (G : GenData)

/-- **Main combinatorial theorem.** `β₁ ≤ 2W`. -/
theorem beta1_le_two_W : G.beta1 ≤ 2 * G.W := by
  by_cases h : (G.s, G.t) = (1, 1)
  · obtain ⟨hA, hB⟩ := G.st_eq_one_one_iff.1 h
    exact G.beta1_le_two_W_exceptional hA hB
  · exact G.beta1_le_two_W_of_ne h

/-- `β₁ ≤ 2w`. -/
theorem beta1_le_two_w : G.beta1 ≤ 2 * G.w :=
  G.beta1_le_two_W.trans (Nat.mul_le_mul_left 2 G.W_le_w)

end GenData

end SemigroupBetti
