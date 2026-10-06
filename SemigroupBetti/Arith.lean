/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/
module

public import SemigroupBetti.Antichain

/-!
# The general arithmetic bound and the non-exceptional cases

Write-up `PROOF_B_lean_writeup.md`: Lemma 13.
-/

@[expose] public section

namespace SemigroupBetti

namespace GenData

variable (G : GenData)

/-- **Lemma 13 (general bound).** `β₁ ≤ 4 + 2(R - 1) + (p + q - 1)`. -/
theorem beta1_le_general : G.beta1 ≤ 4 + 2 * (G.R - 1) + (G.p + G.q - 1) := by
  rw [G.beta1_eq]
  have := G.sigma_le_four
  have := G.P_le
  have := G.Q_le
  have := G.E_le
  omega

/-- **Lemma 13 (closed form).** `4 + 2(R-1) + (p+q-1) = 2W - 2 max(s,t) + (s+t)/d + 1`. -/
theorem general_bound_eq :
    4 + 2 * (G.R - 1) + (G.p + G.q - 1) = 2 * G.W - 2 * max G.s G.t + (G.s + G.t) / G.dg + 1 := by
  rw [← G.p_add_q_eq, G.R_eq]
  have := G.two_le_R; rw [G.R_eq] at this
  have := G.p_pos
  omega

lemma dg_eq_s_of_s_eq_t (h : G.s = G.t) : G.dg = G.s := by unfold dg; rw [← h, Nat.gcd_self]

/-- The exceptional case `(s,t) = (1,1)` is exactly `(A, B) = (1, W - 1)`. -/
lemma st_eq_one_one_iff : (G.s, G.t) = (1, 1) ↔ G.A = 1 ∧ G.B = G.W - 1 := by
  have := G.B_lt_W
  simp only [Prod.mk.injEq, s, t]
  omega

/-- **Lemma 13.** If `(s,t) ≠ (1,1)` then `β₁ ≤ 2W`. -/
theorem beta1_le_two_W_of_ne (h : (G.s, G.t) ≠ (1, 1)) : G.beta1 ≤ 2 * G.W := by
  have hb := G.beta1_le_general
  rw [G.general_bound_eq] at hb
  have hs := G.s_pos
  have ht := G.t_pos
  have hR := G.two_le_R
  rw [G.R_eq] at hR
  rw [← G.p_add_q_eq] at hb
  have hpq := G.p_add_q_le
  rcases lt_trichotomy G.s G.t with hlt | heq | hgt
  · -- Case 1: `s < t`
    omega
  · -- Cases 3–4: `s = t`, so `d = s` and `p = q = 1`
    have hdg : G.dg = G.s := G.dg_eq_s_of_s_eq_t heq
    have hp : G.p = 1 := by
      have := G.dg_mul_p; rw [hdg, ← heq] at this
      exact (Nat.mul_eq_left (by omega)).1 this
    have hq : G.q = 1 := by
      have := G.dg_mul_q; rw [hdg] at this
      exact (Nat.mul_eq_left (by omega)).1 this
    have hs2 : 2 ≤ G.s := by
      by_contra hc
      exact h (Prod.ext (by simp only; omega) (by simp only; omega))
    omega
  · -- Case 2: `s > t`
    omega

end GenData

end SemigroupBetti
