/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/
import SemigroupBetti.Arith

/-!
# The exceptional case `(A, B) = (1, W - 1)`

Write-up `PROOF_B_lean_writeup.md`: Lemma 14, Lemma 15, Lemma 16.
-/

namespace SemigroupBetti

open Finset

namespace GenData

variable (G : GenData)

/-! ### Generic helpers: selected pairs on a side, saturation -/

/-- Two selected `K`-vectors (`K = {i,k}`) are comparable iff their `i`- and `k`-coordinates are. -/
lemma sel_le_of_coords {K : Finset (Fin 4)} {i k : Fin 4} (hKe : K = {i, k}) (hK : K.card = 2)
    {d d' : ℕ} (hS : G.IsSplit d K) (hS' : G.IsSplit d' K)
    (hi : G.sel d K i ≤ G.sel d' K i) (hk : G.sel d K k ≤ G.sel d' K k) :
    G.sel d K ≤ G.sel d' K := by
  intro j
  by_cases hj : j ∈ K
  · rw [hKe, mem_insert, mem_singleton] at hj
    rcases hj with rfl | rfl
    · exact hi
    · exact hk
  · rw [G.sel_eq_zero hS hK hj, G.sel_eq_zero hS' hK hj]

/-- The selected `(i, k)`-coordinate pairs of a family on side `K = {i,k}`. -/
noncomputable def pairsOf (F : Finset ℕ) (K : Finset (Fin 4)) (i k : Fin 4) : Finset (ℕ × ℕ) :=
  F.image (fun d => (G.sel d K i, G.sel d K k))

lemma pairsOf_injOn {F : Finset ℕ} {K : Finset (Fin 4)} {i k : Fin 4} (hik : i ≠ k)
    (hKe : K = {i, k}) (hF : ∀ d ∈ F, G.IsSplit d K) :
    Set.InjOn (fun d => (G.sel d K i, G.sel d K k)) F := by
  have hK : K.card = 2 := by rw [hKe]; exact card_pair hik
  intro d hd d' hd' h
  simp only [Prod.mk.injEq] at h
  have hle := G.sel_le_of_coords hKe hK (hF d hd) (hF d' hd') h.1.le h.2.le
  have hge := G.sel_le_of_coords hKe hK (hF d' hd') (hF d hd) h.1.ge h.2.ge
  rw [← (G.sel_of_split (hF d hd) hK).1, ← (G.sel_of_split (hF d' hd') hK).1,
    le_antisymm hle hge]

lemma card_pairsOf {F : Finset ℕ} {K : Finset (Fin 4)} {i k : Fin 4} (hik : i ≠ k)
    (hKe : K = {i, k}) (hF : ∀ d ∈ F, G.IsSplit d K) : (G.pairsOf F K i k).card = F.card :=
  card_image_of_injOn (G.pairsOf_injOn hik hKe hF)

lemma pairsOf_antichain {F : Finset ℕ} {K : Finset (Fin 4)} {i k : Fin 4} (hik : i ≠ k)
    (hKe : K = {i, k}) (hF : ∀ d ∈ F, G.IsSplit d K) : IsPairAntichain (G.pairsOf F K i k) := by
  have hK : K.card = 2 := by rw [hKe]; exact card_pair hik
  intro x hx y hy h1 h2
  obtain ⟨d, hd, rfl⟩ := mem_image.1 hx
  obtain ⟨d', hd', rfl⟩ := mem_image.1 hy
  by_cases hne : d = d'
  · rw [hne]
  · exact absurd (G.sel_le_of_coords hKe hK (hF d hd) (hF d' hd') h1 h2)
      (G.sel_antichain hK (hF d hd) (hF d' hd') hne)

lemma pairsOf_pos {F : Finset ℕ} {K : Finset (Fin 4)} {i k : Fin 4} (hik : i ≠ k)
    (hKe : K = {i, k}) (hF : ∀ d ∈ F, G.IsSplit d K) :
    ∀ x ∈ G.pairsOf F K i k, 1 ≤ x.1 ∧ 1 ≤ x.2 := by
  have hK : K.card = 2 := by rw [hKe]; exact card_pair hik
  intro x hx
  obtain ⟨d, hd, rfl⟩ := mem_image.1 hx
  exact ⟨G.sel_pos (hF d hd) hK (by rw [hKe]; simp),
    G.sel_pos (hF d hd) hK (by rw [hKe]; simp)⟩

/-- **Saturation.** If the selected `k`-coordinates of a family of size `c` take values in
`[1, c]`, every value in `[1, c]` is attained. -/
lemma exists_coord_eq {K : Finset (Fin 4)} {i k : Fin 4} (hik : i ≠ k) (hKe : K = {i, k})
    (F : Finset ℕ) (hF : ∀ d ∈ F, G.IsSplit d K) {c : ℕ}
    (hc : ∀ d ∈ F, 1 ≤ G.sel d K k ∧ G.sel d K k ≤ c) (hcard : F.card = c) {v : ℕ}
    (hv1 : 1 ≤ v) (hvc : v ≤ c) : ∃ d ∈ F, G.sel d K k = v := by
  obtain ⟨d, hd, h⟩ := surj_on_of_inj_on_of_card_le (s := F) (t := Icc 1 c)
    (fun d _ => G.sel d K k) (fun d hd => mem_Icc.2 (hc d hd))
    (fun d d' hd hd' h => G.sel_coord_injOn hik hKe F hF hd hd' h)
    (by simp [hcard]) v (mem_Icc.2 ⟨hv1, hvc⟩)
  exact ⟨d, hd, h.symm⟩

/-! ### Facts in the exceptional case -/

section Exceptional

variable {G}
variable (hA : G.A = 1) (hB : G.B = G.W - 1)
include hA hB
set_option linter.unusedSectionVars false

lemma exc_R : G.R = G.W - 1 := by
  have := G.three_le_W; unfold R; omega

lemma exc_p : G.p = 1 := by
  have := G.three_le_W
  have ht : G.t = 1 := by unfold t; omega
  have hs : G.s = 1 := hA
  unfold p dg; rw [ht, hs]; rfl

lemma exc_q : G.q = 1 := by
  have := G.three_le_W
  have ht : G.t = 1 := by unfold t; omega
  have hs : G.s = 1 := hA
  unfold q dg; rw [ht, hs]; rfl

lemma exc_U2 : G.U2 = Pi.single 2 (G.W - 1) := by
  funext j; fin_cases j <;> simp [U2, hA]

lemma exc_V2 : G.V2 = ![0, 1, 0, G.W - 2] := by
  have := G.three_le_W
  have h1 : G.W - G.B = 1 := by omega
  have h2 : G.B - G.A = G.W - 2 := by omega
  simp only [V2, h1, h2]

/-- `ν(0,0,W-1,0) = ν(0,1,0,W-2)`, both equal to `(W-1) n₂`. -/
lemma exc_nu_V2 : G.nu ![0, 1, 0, G.W - 2] = (G.W - 1) * G.n 2 := by
  rw [← exc_V2 hA hB, ← G.identity2.1, exc_U2 hA hB, G.nu_single]

/-- `gcd(n₂, n₃) = 1` in the exceptional family. -/
lemma exc_coprime : Nat.Coprime (G.n 3) (G.n 2) := by
  have hW := G.three_le_W
  have hn2 : G.n 2 = G.m + G.g * (G.W - 1) := by rw [n_two, G.b_eq, hB]
  have hn3 : G.n 3 = G.n 2 + G.g := by
    rw [hn2, n_three, G.w_eq]
    have : G.W = (G.W - 1) + 1 := by omega
    conv_lhs => rw [this]
    ring
  set k := Nat.gcd (G.n 3) (G.n 2)
  have hk3 : k ∣ G.n 3 := Nat.gcd_dvd_left _ _
  have hk2 : k ∣ G.n 2 := Nat.gcd_dvd_right _ _
  have hkg : k ∣ G.g := by
    rw [hn3] at hk3; exact (Nat.dvd_add_right hk2).1 hk3
  have hkm : k ∣ G.m := by
    rw [hn2] at hk2
    exact (Nat.dvd_add_left (Dvd.dvd.mul_right hkg _)).1 hk2
  have := Nat.dvd_gcd hkm hkg
  rw [G.gcd_m_g] at this
  exact Nat.dvd_one.1 this

end Exceptional

/-! ### Lemma 14 -/

lemma sideP_split {d : ℕ} (hd : d ∈ G.famP) : G.IsSplit d {2, 3} := by
  have hc : ({0, 1} : Finset (Fin 4))ᶜ = {2, 3} := by decide
  exact hc ▸ (G.isSplit_of_mem_fam hd).compl

lemma sideQ_split {d : ℕ} (hd : d ∈ G.famQ) : G.IsSplit d {1, 3} := by
  have hc : ({0, 2} : Finset (Fin 4))ᶜ = {1, 3} := by decide
  exact hc ▸ (G.isSplit_of_mem_fam hd).compl

/-- **Lemma 14.** If `A = 1`, `B = W - 1` and `P = W - 2`, then `c₂ = W - 1`. -/
theorem lemma14 (hA : G.A = 1) (hB : G.B = G.W - 1) (hP : G.P = G.W - 2) :
    G.crit 2 = G.W - 1 := by
  have hW := G.three_le_W
  -- `c₂ ≤ W - 1`
  have hle : G.crit 2 ≤ G.W - 1 := by
    apply Nat.find_min'
    rw [isCritCand_iff]
    refine ⟨by omega, ![0, 1, 0, G.W - 2], exc_nu_V2 hA hB, fun h => ?_⟩
    have := congrFun h 1
    simp at this
  by_contra hne
  have hc : G.crit 2 ≤ G.W - 2 := by omega
  have hc1 := G.one_le_crit 2
  -- saturation: some `𝓟` degree has selected `23`-vector `(0,0,W-2,y)`
  have hK : ({2, 3} : Finset (Fin 4)).card = 2 := by decide
  obtain ⟨D, hD, hzD⟩ := G.exists_coord_eq (K := {2, 3}) (i := 3) (k := 2) (by decide) (by decide)
    G.famP (fun d hd => G.sideP_split hd)
    (fun d hd => by
      have := G.sel_two_bounds (G.sideP_split hd) hK (by decide)
      rw [hA] at this; exact this)
    hP (v := G.W - 2) (by omega) le_rfl
  have hS23 := G.sideP_split hD
  have hS01 := G.isSplit_of_mem_fam hD
  set z := G.sel D {2, 3} with hz
  have hz0 : z 0 = 0 := G.sel_eq_zero hS23 hK (by decide)
  have hz1 : z 1 = 0 := G.sel_eq_zero hS23 hK (by decide)
  have hz3 : 0 < z 3 := G.sel_pos hS23 hK (by decide)
  have hnuz : G.nu z = D := (G.sel_of_split hS23 hK).1
  -- the alternative `r` at the critical degree avoids `2` and uses `0` or `1`
  obtain ⟨r, hr, hrne⟩ := G.exists_alt 2
  have hr2 := G.alt_coord_eq_zero hr hrne
  have hr01 : 0 < r 0 ∨ 0 < r 1 := by
    by_contra h0
    push Not at h0
    have hr0 : r 0 = 0 := by omega
    have hr1 : r 1 = 0 := by omega
    have hreq : r = Pi.single 3 (r 3) := by
      funext j; fin_cases j <;> simp [hr0, hr1, hr2]
    rw [hreq, G.nu_single] at hr
    have hdvd : G.n 3 ∣ G.crit 2 * G.n 2 := ⟨r 3, by rw [← hr, mul_comm]⟩
    have h3 := (exc_coprime hA hB).dvd_of_dvd_mul_right hdvd
    have := Nat.le_of_dvd (by omega) h3
    have := G.W_le_w
    have := G.m_pos
    have hn3 : G.n 3 = G.m + G.w := rfl
    omega
  -- the bridge `b = r + (W-2-c₂) e₂ + y e₃`
  let b := r + Pi.single 2 (G.W - 2 - G.crit 2) + Pi.single 3 (z 3)
  have hb : G.nu b = D := by
    simp only [b]
    rw [G.nu_add, G.nu_add, G.nu_single, G.nu_single, hr, ← hnuz, G.nu_eq_sum z, hz0, hz1, hzD,
      ← Nat.add_mul, Nat.add_sub_cancel' hc, n_two, n_three]
    ring
  have hK01 : ({0, 1} : Finset (Fin 4)).card = 2 := by decide
  have hy := G.sel_of_split hS01 hK01
  rcases hr01 with h | h
  · refine G.no_bridge hS23 hnuz hy.1 hb (i := 3) (by decide) hz3 (j := 0) (by decide)
      (G.sel_pos hS01 hK01 (by decide)) ⟨3, ?_, hz3⟩ ⟨0, ?_, G.sel_pos hS01 hK01 (by decide)⟩
    · simp [b]; omega
    · simp [b]; omega
  · refine G.no_bridge hS23 hnuz hy.1 hb (i := 3) (by decide) hz3 (j := 1) (by decide)
      (G.sel_pos hS01 hK01 (by decide)) ⟨3, ?_, hz3⟩ ⟨1, ?_, G.sel_pos hS01 hK01 (by decide)⟩
    · simp [b]; omega
    · simp [b]; omega

/-! ### Lemma 15 -/

/-- **Lemma 15.** If `A = 1`, `B = W - 1` and `Q = W - 2`, then some `𝓠` degree has selected
`13`-vector with `u = 1`, and every such vector is exactly `(0,1,0,W-2)`. -/
theorem lemma15 (hA : G.A = 1) (hB : G.B = G.W - 1) (hQ : G.Q = G.W - 2) :
    (∃ D ∈ G.famQ, G.sel D {1, 3} 1 = 1) ∧
      ∀ D ∈ G.famQ, G.sel D {1, 3} 1 = 1 → G.sel D {1, 3} = ![0, 1, 0, G.W - 2] := by
  have hW := G.three_le_W
  have hK : ({1, 3} : Finset (Fin 4)).card = 2 := by decide
  have hF : ∀ d ∈ G.famQ, G.IsSplit d {1, 3} := fun d hd => G.sideQ_split hd
  refine ⟨?_, ?_⟩
  · exact G.exists_coord_eq (K := {1, 3}) (i := 3) (k := 1) (by decide) (by decide) G.famQ hF
      (fun d hd => by
        have := G.sel_one_bounds (hF d hd) hK (by decide)
        rw [hB] at this; exact this)
      (by have : G.Q = G.famQ.card := rfl; omega) (v := 1) le_rfl (by omega)
  · intro D hD hu
    have hS := hF D hD
    have hz0 : G.sel D {1, 3} 0 = 0 := G.sel_eq_zero hS hK (by decide)
    have hz2 : G.sel D {1, 3} 2 = 0 := G.sel_eq_zero hS hK (by decide)
    -- lower bound `v ≥ W - 2` from Lemma 11
    have hT := G.pairsOf_antichain (F := G.famQ) (i := 1) (k := 3) (by decide) (by decide) hF
    have hpos := G.pairsOf_pos (F := G.famQ) (i := 1) (k := 3) (by decide) (by decide) hF
    have hmem : (G.sel D {1, 3} 1, G.sel D {1, 3} 3) ∈ G.pairsOf G.famQ {1, 3} 1 3 := mem_image.2 ⟨D, hD, rfl⟩
    have hco := hT.corank_le hpos hmem
    have hfilt : (G.pairsOf G.famQ {1, 3} 1 3).filter (fun y => (G.sel D {1, 3} 1, G.sel D {1, 3} 3).1 ≤ y.1) =
        G.pairsOf G.famQ {1, 3} 1 3 := by
      apply filter_true_of_mem
      intro y hy; simp only; rw [hu]; exact (hpos y hy).1
    rw [hfilt, G.card_pairsOf (by decide) (by decide) hF] at hco
    simp only at hco
    have hQ' : G.famQ.card = G.W - 2 := hQ
    rw [hQ'] at hco
    -- upper bound `v ≤ W - 2` by the exceptional replacement
    have hv : G.sel D {1, 3} 3 ≤ G.W - 2 := by
      by_contra hv
      have hU : G.V2 ≤ G.sel D {1, 3} := by
        rw [exc_V2 hA hB]; intro j; fin_cases j <;> simp [hz0, hz2, hu]; omega
      exact G.no_replace hS hK hU G.identity2.1.symm (k := 3)
        (by rw [exc_V2 hA hB]; simp; omega) (j := 2) (by decide)
        (by rw [exc_U2 hA hB]; simp; omega)
    funext j; fin_cases j <;> simp [hz0, hz2, hu]; omega

/-! ### Lemma 16 -/

/-- **Lemma 16.** If `(A, B) = (1, W - 1)` then `P + Q ≤ 2W - 5`. -/
theorem lemma16_PQ (hA : G.A = 1) (hB : G.B = G.W - 1) : G.P + G.Q ≤ 2 * G.W - 5 := by
  have hW := G.three_le_W
  have hP := G.P_le
  have hQ := G.Q_le
  rw [exc_R hA hB] at hP hQ
  by_contra hc
  have hP' : G.P = G.W - 2 := by omega
  have hQ' : G.Q = G.W - 2 := by omega
  have hc2 := G.lemma14 hA hB hP'
  obtain ⟨⟨D, hD, hu⟩, hall⟩ := G.lemma15 hA hB hQ'
  have hsel := hall D hD hu
  have hK : ({1, 3} : Finset (Fin 4)).card = 2 := by decide
  have hDeq : D = G.crit 2 * G.n 2 := by
    rw [← (G.sel_of_split (G.sideQ_split hD) hK).1, hsel, exc_nu_V2 hA hB, hc2]
  obtain ⟨-, hcon, hS, -⟩ := G.mem_fam.1 hD
  subst hDeq
  exact hS ⟨_, by rw [G.compSupp_critVertex 2]; rfl⟩

/-- **Lemma 16.** If `(A, B) = (1, W - 1)` then `β₁ ≤ 2W`. -/
theorem beta1_le_two_W_exceptional (hA : G.A = 1) (hB : G.B = G.W - 1) :
    G.beta1 ≤ 2 * G.W := by
  have hW := G.three_le_W
  have hPQ := G.lemma16_PQ hA hB
  have hE := G.E_le
  rw [exc_p hA hB, exc_q hA hB] at hE
  have hσ := G.sigma_le_four
  rw [G.beta1_eq]
  omega

end GenData

end SemigroupBetti
