/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/
module

public import Mathlib

/-!
# Generator data, vectors in `ℕ⁴`, and normalized arithmetic

Write-up `PROOF_B_lean_writeup.md`, §1: Definitions 1–2 and Lemma 1.
-/

@[expose] public section

namespace SemigroupBetti

open Finset

/-- The generator vector `(m, m+a, m+b, m+w)`. -/
def gens (m a b w : ℕ) : Fin 4 → ℕ := ![m, m + a, m + b, m + w]

/-- **Definition 1.** Generator data with the standing hypotheses `(H)`. -/
structure GenData where
  m : ℕ
  a : ℕ
  b : ℕ
  w : ℕ
  m_pos : 0 < m
  a_pos : 0 < a
  a_lt_b : a < b
  b_lt_w : b < w
  gcd_eq_one : Nat.gcd m (Nat.gcd a (Nat.gcd b w)) = 1
  /-- Minimality: no generator is an `ℕ`-combination of the other three. -/
  minimal : ∀ i : Fin 4, ∀ z : Fin 4 → ℕ, z i = 0 → ∑ j, z j * gens m a b w j ≠ gens m a b w i

/-- **Definition 2.** Length `|z| = ∑ zᵢ`. -/
def len (z : Fin 4 → ℕ) : ℕ := ∑ i, z i

/-- **Definition 2.** Support `{i : zᵢ > 0}`. -/
def supp (z : Fin 4 → ℕ) : Finset (Fin 4) := Finset.univ.filter (fun i => 0 < z i)

/-- **Definition 2.** Two vectors share a variable. -/
def SharesVar (z z' : Fin 4 → ℕ) : Prop := ∃ i, 0 < z i ∧ 0 < z' i

instance : DecidableRel SharesVar := fun z z' =>
  inferInstanceAs (Decidable (∃ i, 0 < z i ∧ 0 < z' i))

@[simp] lemma mem_supp {z : Fin 4 → ℕ} {i : Fin 4} : i ∈ supp z ↔ 0 < z i := by
  simp [supp]

lemma SharesVar.symm {z z' : Fin 4 → ℕ} (h : SharesVar z z') : SharesVar z' z := by
  obtain ⟨i, h1, h2⟩ := h; exact ⟨i, h2, h1⟩

lemma sharesVar_comm {z z' : Fin 4 → ℕ} : SharesVar z z' ↔ SharesVar z' z :=
  ⟨SharesVar.symm, SharesVar.symm⟩

lemma sharesVar_iff_supp {z z' : Fin 4 → ℕ} :
    SharesVar z z' ↔ ¬ Disjoint (supp z) (supp z') := by
  simp only [SharesVar, Finset.not_disjoint_iff, mem_supp]

namespace GenData

variable (G : GenData)

/-- The generator vector `n = (m, m+a, m+b, m+w)`. -/
def n : Fin 4 → ℕ := gens G.m G.a G.b G.w

/-- `g = gcd(a, gcd(b, w))`. -/
def g : ℕ := Nat.gcd G.a (Nat.gcd G.b G.w)

/-- `A = a / g`. -/
def A : ℕ := G.a / G.g
/-- `B = b / g`. -/
def B : ℕ := G.b / G.g
/-- `W = w / g` (normalized width). -/
def W : ℕ := G.w / G.g

/-- **Definition 2.** Degree `ν(z) = ∑ zᵢ nᵢ`. -/
def nu (z : Fin 4 → ℕ) : ℕ := ∑ i, z i * G.n i

/-- **Definition 2.** Weight `ω(z) = a z₁ + b z₂ + w z₃`. -/
def omega (z : Fin 4 → ℕ) : ℕ := G.a * z 1 + G.b * z 2 + G.w * z 3

@[simp] lemma n_zero : G.n 0 = G.m := rfl
@[simp] lemma n_one : G.n 1 = G.m + G.a := rfl
@[simp] lemma n_two : G.n 2 = G.m + G.b := rfl
@[simp] lemma n_three : G.n 3 = G.m + G.w := rfl

lemma minimal' (i : Fin 4) (z : Fin 4 → ℕ) (hz : z i = 0) : G.nu z ≠ G.n i :=
  G.minimal i z hz

lemma nu_eq_sum (z : Fin 4 → ℕ) : G.nu z = z 0 * G.m + z 1 * (G.m + G.a) +
    z 2 * (G.m + G.b) + z 3 * (G.m + G.w) := by
  simp [nu, Fin.sum_univ_four]

/-- `ν(z) = m|z| + ω(z)`. -/
lemma nu_eq_len_add_omega (z : Fin 4 → ℕ) : G.nu z = G.m * len z + G.omega z := by
  rw [nu_eq_sum]; simp only [len, omega, Fin.sum_univ_four]; ring

lemma n_strictMono : StrictMono G.n := by
  have h1 := G.a_pos; have h2 := G.a_lt_b; have h3 := G.b_lt_w
  refine Fin.strictMono_iff_lt_succ.2 ?_
  intro i; fin_cases i <;> simp <;> omega

lemma n_mono : Monotone G.n := G.n_strictMono.monotone

lemma m_le_n (i : Fin 4) : G.m ≤ G.n i := by
  have := G.n_mono (Fin.zero_le i); simpa using this

lemma n_pos (i : Fin 4) : 0 < G.n i := lt_of_lt_of_le G.m_pos (G.m_le_n i)

lemma n_le_n_three (i : Fin 4) : G.n i ≤ G.n 3 := G.n_mono (Fin.le_last i)

/-! ### Additivity of `ν` -/

@[simp] lemma nu_zero : G.nu 0 = 0 := by simp [nu]

lemma nu_add (x y : Fin 4 → ℕ) : G.nu (x + y) = G.nu x + G.nu y := by
  simp [nu, add_mul, Finset.sum_add_distrib]

lemma nu_single (i : Fin 4) (k : ℕ) : G.nu (Pi.single i k) = k * G.n i := by
  simp only [nu]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [hj]
  · simp

/-- If `x ≤ y` coordinatewise then `ν(y) = ν(x) + ν(y - x)`. -/
lemma nu_sub {x y : Fin 4 → ℕ} (h : x ≤ y) : G.nu y = G.nu x + G.nu (y - x) := by
  rw [← nu_add]; congr 1; ext i; simp only [Pi.add_apply, Pi.sub_apply]
  have hi : x i ≤ y i := h i
  omega

lemma single_le_nu (z : Fin 4 → ℕ) (i : Fin 4) : z i * G.n i ≤ G.nu z := by
  unfold nu
  exact Finset.single_le_sum (f := fun j => z j * G.n j) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ i)

lemma m_mul_le_nu (z : Fin 4 → ℕ) (i : Fin 4) : G.m * z i ≤ G.nu z := by
  calc G.m * z i ≤ z i * G.n i := by rw [mul_comm]; exact Nat.mul_le_mul_left _ (G.m_le_n i)
    _ ≤ G.nu z := G.single_le_nu z i

lemma nu_eq_zero_iff {z : Fin 4 → ℕ} : G.nu z = 0 ↔ z = 0 := by
  constructor
  · intro h; ext i
    have := G.single_le_nu z i
    have hp := G.n_pos i
    simp only [Pi.zero_apply]
    rw [h] at this
    exact (Nat.mul_eq_zero.1 (Nat.le_zero.1 this)).resolve_right hp.ne'
  · rintro rfl; simp

lemma nu_pos_of_pos {z : Fin 4 → ℕ} {i : Fin 4} (h : 0 < z i) : 0 < G.nu z :=
  lt_of_lt_of_le (Nat.mul_pos h (G.n_pos i)) (G.single_le_nu z i)

/-! ### Lemma 1: normalized arithmetic -/

lemma g_dvd_a : G.g ∣ G.a := Nat.gcd_dvd_left _ _
lemma g_dvd_b : G.g ∣ G.b := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
lemma g_dvd_w : G.g ∣ G.w := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)

lemma g_pos : 0 < G.g := Nat.gcd_pos_of_pos_left _ G.a_pos

lemma one_le_g : 1 ≤ G.g := G.g_pos

lemma a_eq : G.a = G.g * G.A := (Nat.mul_div_cancel' G.g_dvd_a).symm
lemma b_eq : G.b = G.g * G.B := (Nat.mul_div_cancel' G.g_dvd_b).symm
lemma w_eq : G.w = G.g * G.W := (Nat.mul_div_cancel' G.g_dvd_w).symm

lemma A_pos : 0 < G.A := by
  have h := G.a_pos; rw [G.a_eq] at h; exact Nat.pos_of_mul_pos_left h

lemma one_le_A : 1 ≤ G.A := G.A_pos

lemma A_lt_B : G.A < G.B := by
  have h := G.a_lt_b; rw [G.a_eq, G.b_eq] at h; exact Nat.lt_of_mul_lt_mul_left h

lemma B_lt_W : G.B < G.W := by
  have h := G.b_lt_w; rw [G.b_eq, G.w_eq] at h; exact Nat.lt_of_mul_lt_mul_left h

lemma two_le_B : 2 ≤ G.B := by have := G.A_pos; have := G.A_lt_B; omega
lemma three_le_W : 3 ≤ G.W := by have := G.two_le_B; have := G.B_lt_W; omega
lemma two_le_W_sub_A : 2 ≤ G.W - G.A := by
  have := G.A_lt_B; have := G.B_lt_W; omega

lemma gcd_ABW : Nat.gcd G.A (Nat.gcd G.B G.W) = 1 := by
  have hbw : G.g ∣ Nat.gcd G.b G.w := Nat.dvd_gcd G.g_dvd_b G.g_dvd_w
  have h1 : Nat.gcd G.B G.W = Nat.gcd G.b G.w / G.g := Nat.gcd_div G.g_dvd_b G.g_dvd_w
  rw [A, h1, Nat.gcd_div G.g_dvd_a hbw]
  exact Nat.div_self G.g_pos

lemma gcd_m_g : Nat.gcd G.m G.g = 1 := G.gcd_eq_one

lemma W_le_w : G.W ≤ G.w := by
  rw [G.w_eq]; exact Nat.le_mul_of_pos_left _ G.g_pos

lemma n_eq_normalized : G.n = ![G.m, G.m + G.g * G.A, G.m + G.g * G.B, G.m + G.g * G.W] := by
  rw [← G.a_eq, ← G.b_eq, ← G.w_eq]; rfl

end GenData

end SemigroupBetti
