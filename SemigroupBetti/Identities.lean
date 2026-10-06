/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/
import SemigroupBetti.Partition

/-!
# Arithmetic parameters, the three vector identities, and interior bounds

Write-up `PROOF_B_lean_writeup.md`: Definition 8, Lemma 8, Lemma 9.
The write-up's lowercase `d = gcd(s,t)` is called `dg` here (to avoid a clash with degrees).
-/

namespace SemigroupBetti

open Finset

namespace GenData

variable (G : GenData)

/-! ### Definition 8 -/

/-- `s = A`. -/
def s : ℕ := G.A
/-- `t = W - B`. -/
def t : ℕ := G.W - G.B
/-- `d = gcd(s, t)` (named `dg`). -/
def dg : ℕ := Nat.gcd G.s G.t
/-- `p = t / d`. -/
def p : ℕ := G.t / G.dg
/-- `q = s / d`. -/
def q : ℕ := G.s / G.dg
/-- `R = min(B, W - A)`. -/
def R : ℕ := min G.B (G.W - G.A)

lemma s_pos : 1 ≤ G.s := G.A_pos
lemma t_pos : 1 ≤ G.t := by have := G.B_lt_W; unfold t; omega
lemma dg_pos : 1 ≤ G.dg := Nat.gcd_pos_of_pos_left _ G.s_pos
lemma dg_mul_p : G.dg * G.p = G.t := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
lemma dg_mul_q : G.dg * G.q = G.s := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
lemma p_pos : 1 ≤ G.p := by
  have h := G.dg_mul_p; have := G.t_pos
  rcases Nat.eq_zero_or_pos G.p with h0 | h0
  · rw [h0, mul_zero] at h; omega
  · exact h0
lemma q_pos : 1 ≤ G.q := by
  have h := G.dg_mul_q; have := G.s_pos
  rcases Nat.eq_zero_or_pos G.q with h0 | h0
  · rw [h0, mul_zero] at h; omega
  · exact h0
lemma dg_mul_p_add_q : G.dg * (G.p + G.q) = G.s + G.t := by
  rw [mul_add, G.dg_mul_p, G.dg_mul_q, add_comm]
lemma p_add_q_eq : G.p + G.q = (G.s + G.t) / G.dg := by
  rw [← G.dg_mul_p_add_q, Nat.mul_div_cancel_left _ G.dg_pos]
lemma p_add_q_le : G.p + G.q ≤ G.s + G.t := by
  rw [← G.dg_mul_p_add_q]; exact Nat.le_mul_of_pos_left _ G.dg_pos
lemma W_eq_B_add_t : G.W = G.B + G.t := by have := G.B_lt_W; unfold t; omega
lemma R_eq : G.R = G.W - max G.s G.t := by
  have := G.A_lt_B; have := G.B_lt_W; unfold R s t; omega
lemma two_le_R : 2 ≤ G.R := by
  have := G.two_le_B; have := G.two_le_W_sub_A; unfold R; omega
/-- `p A = q t`. -/
lemma p_mul_A : G.p * G.A = G.q * G.t := by
  have h : G.dg * (G.p * G.A) = G.dg * (G.q * G.t) := by
    calc G.dg * (G.p * G.A) = (G.dg * G.p) * G.A := by ring
      _ = G.t * (G.dg * G.q) := by rw [G.dg_mul_p, G.dg_mul_q]; rfl
      _ = G.dg * (G.q * G.t) := by ring
  exact Nat.eq_of_mul_eq_mul_left G.dg_pos h

/-! ### Lemma 8 -/

/-- `U₁ = (0,B,0,0)`, `V₁ = (B-A,0,A,0)`. -/
def U1 : Fin 4 → ℕ := ![0, G.B, 0, 0]
def V1 : Fin 4 → ℕ := ![G.B - G.A, 0, G.A, 0]
/-- `U₂ = (0,0,W-A,0)`, `V₂ = (0,W-B,0,B-A)`. -/
def U2 : Fin 4 → ℕ := ![0, 0, G.W - G.A, 0]
def V2 : Fin 4 → ℕ := ![0, G.W - G.B, 0, G.B - G.A]
/-- `U₃ = (0,p,q,0)`, `V₃ = (p,0,0,q)`. -/
def U3 : Fin 4 → ℕ := ![0, G.p, G.q, 0]
def V3 : Fin 4 → ℕ := ![G.p, 0, 0, G.q]

lemma nu_vec (x0 x1 x2 x3 : ℕ) :
    G.nu ![x0, x1, x2, x3] = x0 * G.m + x1 * (G.m + G.a) + x2 * (G.m + G.b) + x3 * (G.m + G.w) := by
  rw [nu_eq_sum]; simp

lemma len_vec (x0 x1 x2 x3 : ℕ) : len ![x0, x1, x2, x3] = x0 + x1 + x2 + x3 := by
  simp [len, Fin.sum_univ_four]

/-- **Lemma 8, first identity.** -/
theorem identity1 : G.nu G.U1 = G.nu G.V1 ∧ len G.U1 = len G.V1 ∧ len G.U1 = G.B := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le G.A_lt_B.le
  have e1 : G.B - G.A = k := by omega
  simp only [U1, V1, nu_vec, len_vec, e1]
  refine ⟨?_, by omega, by omega⟩
  rw [G.a_eq, G.b_eq, hk]; ring

/-- **Lemma 8, second identity.** -/
theorem identity2 : G.nu G.U2 = G.nu G.V2 ∧ len G.U2 = len G.V2 ∧ len G.U2 = G.W - G.A := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le G.A_lt_B.le
  obtain ⟨l, hl⟩ := Nat.exists_eq_add_of_le G.B_lt_W.le
  have e1 : G.B - G.A = k := by omega
  have e2 : G.W - G.B = l := by omega
  have e3 : G.W - G.A = k + l := by omega
  simp only [U2, V2, nu_vec, len_vec, e1, e2, e3]
  refine ⟨?_, by omega, by omega⟩
  rw [G.a_eq, G.b_eq, G.w_eq, hl, hk]; ring

/-- **Lemma 8, third identity.** -/
theorem identity3 : G.nu G.U3 = G.nu G.V3 ∧ len G.U3 = len G.V3 ∧ len G.U3 = G.p + G.q := by
  simp only [U3, V3, nu_vec, len_vec]
  refine ⟨?_, by omega, by omega⟩
  have h := G.p_mul_A
  rw [G.a_eq, G.b_eq, G.w_eq, G.W_eq_B_add_t]
  linear_combination G.g * h

/-! ### Lemma 9 -/

/-- **Lemma 9 (coordinate 1).** At a degree splitting along a pair `K ∋ 1`, the selected
`K`-vector has `1 ≤ u ≤ B - 1` at coordinate `1`. -/
theorem sel_one_bounds {d : ℕ} {K : Finset (Fin 4)} (hS : G.IsSplit d K) (hK : K.card = 2)
    (h1 : 1 ∈ K) : 1 ≤ G.sel d K 1 ∧ G.sel d K 1 ≤ G.B - 1 := by
  refine ⟨G.sel_pos hS hK h1, ?_⟩
  by_contra hc
  have hB := G.two_le_B
  have hge : G.B ≤ G.sel d K 1 := by omega
  have key : ∀ K : Finset (Fin 4), K.card = 2 → 1 ∈ K →
      (∃ k ∈ K, k ≠ 1) ∧ ((0 : Fin 4) ∉ K ∨ (2 : Fin 4) ∉ K) := by decide
  obtain ⟨⟨k, hkK, hk1⟩, h02⟩ := key K hK h1
  have hU : G.U1 ≤ G.sel d K := by
    intro i; fin_cases i <;> simp [U1, hge]
  have hUk : G.U1 k < G.sel d K k := by
    have := G.sel_pos hS hK hkK
    fin_cases k <;> simp_all [U1]
  have hAB := G.A_lt_B
  have hA := G.A_pos
  rcases h02 with h0 | h2
  · exact G.no_replace hS hK hU G.identity1.1 hUk h0 (by simp [V1]; omega)
  · exact G.no_replace hS hK hU G.identity1.1 hUk h2 (by simp [V1]; omega)

/-- **Lemma 9 (coordinate 2).** At a degree splitting along a pair `K ∋ 2`, the selected
`K`-vector has `1 ≤ v ≤ W - A - 1` at coordinate `2`. -/
theorem sel_two_bounds {d : ℕ} {K : Finset (Fin 4)} (hS : G.IsSplit d K) (hK : K.card = 2)
    (h2 : 2 ∈ K) : 1 ≤ G.sel d K 2 ∧ G.sel d K 2 ≤ G.W - G.A - 1 := by
  refine ⟨G.sel_pos hS hK h2, ?_⟩
  by_contra hc
  have hWA := G.two_le_W_sub_A
  have hge : G.W - G.A ≤ G.sel d K 2 := by omega
  have key : ∀ K : Finset (Fin 4), K.card = 2 → 2 ∈ K →
      (∃ k ∈ K, k ≠ 2) ∧ ((1 : Fin 4) ∉ K ∨ (3 : Fin 4) ∉ K) := by decide
  obtain ⟨⟨k, hkK, hk2⟩, h13⟩ := key K hK h2
  have hU : G.U2 ≤ G.sel d K := by
    intro i; fin_cases i <;> simp [U2, hge]
  have hUk : G.U2 k < G.sel d K k := by
    have := G.sel_pos hS hK hkK
    fin_cases k <;> simp_all [U2]
  have hAB := G.A_lt_B
  have hBW := G.B_lt_W
  rcases h13 with h1 | h3
  · exact G.no_replace hS hK hU G.identity2.1 hUk h1 (by simp [V2]; omega)
  · exact G.no_replace hS hK hU G.identity2.1 hUk h3 (by simp [V2]; omega)

end GenData

end SemigroupBetti
