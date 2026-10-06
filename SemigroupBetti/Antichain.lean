/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/
import SemigroupBetti.Identities

/-!
# Antichain counting

Write-up `PROOF_B_lean_writeup.md`: Lemma 10, Lemma 11, Lemma 12.
-/

namespace SemigroupBetti

open Finset

/-! ### Lemma 11: positive-pair antichains -/

section PairAntichain

variable {T : Finset (ℕ × ℕ)}

/-- Distinct members of `T` are coordinatewise incomparable. -/
def IsPairAntichain (T : Finset (ℕ × ℕ)) : Prop :=
  ∀ x ∈ T, ∀ y ∈ T, x.1 ≤ y.1 → x.2 ≤ y.2 → x = y

lemma IsPairAntichain.fst_inj (hT : IsPairAntichain T) {x y : ℕ × ℕ} (hx : x ∈ T) (hy : y ∈ T)
    (h : x.1 = y.1) : x = y := by
  rcases le_total x.2 y.2 with h2 | h2
  · exact hT x hx y hy h.le h2
  · exact (hT y hy x hx h.ge h2).symm

lemma IsPairAntichain.snd_inj (hT : IsPairAntichain T) {x y : ℕ × ℕ} (hx : x ∈ T) (hy : y ∈ T)
    (h : x.2 = y.2) : x = y := by
  rcases le_total x.1 y.1 with h1 | h1
  · exact hT x hx y hy h1 h.le
  · exact (hT y hy x hx h1 h.ge).symm

/-- **Lemma 11 (forward bound).** The number of members whose first coordinate is at most
`x.1` (the rank of `x` in the sorted enumeration) is at most `x.1`. -/
lemma IsPairAntichain.rank_le (hT : IsPairAntichain T) (hpos : ∀ x ∈ T, 1 ≤ x.1 ∧ 1 ≤ x.2)
    {x : ℕ × ℕ} : (T.filter (fun y => y.1 ≤ x.1)).card ≤ x.1 := by
  have := card_le_card_of_injOn (fun y : ℕ × ℕ => y.1) (s := T.filter (fun y => y.1 ≤ x.1)) (t := Icc 1 x.1)
    (fun y hy => by
      have hy' := mem_filter.1 (mem_coe.1 hy)
      exact mem_coe.2 (mem_Icc.2 ⟨(hpos y hy'.1).1, hy'.2⟩))
    (fun y hy y' hy' h => hT.fst_inj (mem_filter.1 (mem_coe.1 hy)).1
      (mem_filter.1 (mem_coe.1 hy')).1 h)
  simpa using this

/-- **Lemma 11 (backward bound).** The number of members whose first coordinate is at least
`x.1` is at most `x.2`. -/
lemma IsPairAntichain.corank_le (hT : IsPairAntichain T) (hpos : ∀ x ∈ T, 1 ≤ x.1 ∧ 1 ≤ x.2)
    {x : ℕ × ℕ} (hx : x ∈ T) : (T.filter (fun y => x.1 ≤ y.1)).card ≤ x.2 := by
  have hle : ∀ y ∈ T, x.1 ≤ y.1 → y.2 ≤ x.2 := by
    intro y hy h1
    by_contra h2
    have := hT x hx y hy h1 (by omega)
    subst this; omega
  have := card_le_card_of_injOn (fun y : ℕ × ℕ => y.2) (s := T.filter (fun y => x.1 ≤ y.1)) (t := Icc 1 x.2)
    (fun y hy => by
      have hy' := mem_filter.1 (mem_coe.1 hy)
      exact mem_coe.2 (mem_Icc.2 ⟨(hpos y hy'.1).2, hle y hy'.1 hy'.2⟩))
    (fun y hy y' hy' h => hT.snd_inj (mem_filter.1 (mem_coe.1 hy)).1
      (mem_filter.1 (mem_coe.1 hy')).1 h)
  simpa using this

/-- **Lemma 11.** In a positive-pair antichain with `k` members, for every `1 ≤ r ≤ k` the
`r`-th member in increasing order of first coordinate satisfies `u ≥ r` and `v ≥ k + 1 - r`.
(Stated as existence of a member with these bounds; the member is the one of rank `r`.) -/
theorem IsPairAntichain.exists_rank (hT : IsPairAntichain T)
    (hpos : ∀ x ∈ T, 1 ≤ x.1 ∧ 1 ≤ x.2) {r : ℕ} (hr1 : 1 ≤ r) (hrk : r ≤ T.card) :
    ∃ x ∈ T, r ≤ x.1 ∧ T.card + 1 - r ≤ x.2 := by
  classical
  let rk : ℕ × ℕ → ℕ := fun x => (T.filter (fun y => y.1 ≤ x.1)).card
  have hmaps : ∀ x (hx : x ∈ T), rk x ∈ Icc 1 T.card := by
    intro x hx
    refine mem_Icc.2 ⟨card_pos.2 ⟨x, mem_filter.2 ⟨hx, le_rfl⟩⟩, card_le_card (filter_subset _ _)⟩
  have hinj : ∀ x y (hx : x ∈ T) (hy : y ∈ T), rk x = rk y → x = y := by
    intro x y hx hy h
    by_contra hne
    have hne1 : x.1 ≠ y.1 := fun h1 => hne (hT.fst_inj hx hy h1)
    rcases Nat.lt_or_gt_of_ne hne1 with hlt | hlt
    · have : (T.filter (fun z => z.1 ≤ x.1)) ⊂ (T.filter (fun z => z.1 ≤ y.1)) := by
        refine ⟨fun z hz => ?_, fun hsub => ?_⟩
        · have := mem_filter.1 hz; exact mem_filter.2 ⟨this.1, by omega⟩
        · have := (mem_filter.1 (hsub (mem_filter.2 ⟨hy, le_rfl⟩))).2; omega
      have := card_lt_card this; simp only [rk] at h; omega
    · have : (T.filter (fun z => z.1 ≤ y.1)) ⊂ (T.filter (fun z => z.1 ≤ x.1)) := by
        refine ⟨fun z hz => ?_, fun hsub => ?_⟩
        · have := mem_filter.1 hz; exact mem_filter.2 ⟨this.1, by omega⟩
        · have := (mem_filter.1 (hsub (mem_filter.2 ⟨hx, le_rfl⟩))).2; omega
      have := card_lt_card this; simp only [rk] at h; omega
  obtain ⟨x, hx, hxr⟩ := surj_on_of_inj_on_of_card_le (fun x _ => rk x) hmaps hinj
    (by simp) r (mem_Icc.2 ⟨hr1, hrk⟩)
  refine ⟨x, hx, ?_, ?_⟩
  · have := hT.rank_le hpos (x := x); simp only [rk] at hxr; omega
  · have hunion : T.filter (fun y => y.1 ≤ x.1) ∪ T.filter (fun y => x.1 ≤ y.1) = T := by
      ext y; simp only [mem_union, mem_filter]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro hy; rcases le_total y.1 x.1 with h | h
        · exact Or.inl ⟨hy, h⟩
        · exact Or.inr ⟨hy, h⟩
    have hinter : T.filter (fun y => y.1 ≤ x.1) ∩ T.filter (fun y => x.1 ≤ y.1) = {x} := by
      ext y; simp only [mem_inter, mem_filter, mem_singleton]
      constructor
      · rintro ⟨⟨hy, h1⟩, -, h2⟩; exact hT.fst_inj hy hx (le_antisymm h1 h2)
      · rintro rfl; exact ⟨⟨hx, le_rfl⟩, hx, le_rfl⟩
    have hsum := card_union_add_card_inter (T.filter (fun y => y.1 ≤ x.1))
      (T.filter (fun y => x.1 ≤ y.1))
    rw [hunion, hinter, card_singleton] at hsum
    have := hT.corank_le hpos hx
    simp only [rk] at hxr
    omega

end PairAntichain

namespace GenData

variable (G : GenData)

/-! ### Lemma 10 -/

/-- Two selected vectors on a pair side `K = {i, k}` with equal `k`-coordinates come from the same
degree (Lemma 7 plus totality of `≤` on the `i`-coordinate). -/
lemma sel_coord_injOn {K : Finset (Fin 4)} {i k : Fin 4} (hik : i ≠ k) (hKe : K = {i, k})
    (F : Finset ℕ) (hF : ∀ d ∈ F, G.IsSplit d K) :
    Set.InjOn (fun d => G.sel d K k) F := by
  have hK : K.card = 2 := by rw [hKe]; exact card_pair hik
  intro d hd d' hd' h
  simp only at h
  by_contra hne
  have hle : ∀ {e e' : ℕ}, e ∈ F → e' ∈ F → G.sel e K k = G.sel e' K k →
      G.sel e K i ≤ G.sel e' K i → G.sel e K ≤ G.sel e' K := by
    intro e e' he he' hk hi j
    by_cases hj : j ∈ K
    · rw [hKe, mem_insert, mem_singleton] at hj
      rcases hj with rfl | rfl
      · exact hi
      · exact hk.le
    · rw [G.sel_eq_zero (hF e he) hK hj, G.sel_eq_zero (hF e' he') hK hj]
  rcases le_total (G.sel d K i) (G.sel d' K i) with hi | hi
  · exact G.sel_antichain hK (hF d hd) (hF d' hd') hne (hle hd hd' h hi)
  · exact G.sel_antichain hK (hF d' hd') (hF d hd) (Ne.symm hne) (hle hd' hd h.symm hi)

/-- A family whose selected `k`-coordinates are injective with values in `[1, c]` has at most
`c` members. -/
lemma card_le_of_coord {K : Finset (Fin 4)} {i k : Fin 4} (hik : i ≠ k) (hKe : K = {i, k})
    (F : Finset ℕ) (hF : ∀ d ∈ F, G.IsSplit d K) {c : ℕ}
    (hc : ∀ d ∈ F, 1 ≤ G.sel d K k ∧ G.sel d K k ≤ c) : F.card ≤ c := by
  have := card_le_card_of_injOn (fun d => G.sel d K k) (t := Icc 1 c)
    (fun d hd => mem_coe.2 (mem_Icc.2 (hc d (mem_coe.1 hd))))
    (G.sel_coord_injOn hik hKe F hF)
  simpa using this

lemma isSplit_of_mem_fam {K : Finset (Fin 4)} {d : ℕ} (h : d ∈ G.fam K) : G.IsSplit d K :=
  (G.mem_fam.1 h).2.2.2

/-- **Lemma 10.** `P ≤ R - 1`. -/
theorem P_le : G.P ≤ G.R - 1 := by
  have hc : ({0, 1} : Finset (Fin 4))ᶜ = {2, 3} := by decide
  have h1 : G.P ≤ G.B - 1 :=
    G.card_le_of_coord (i := 0) (k := 1) (by decide) rfl G.famP
      (fun d hd => G.isSplit_of_mem_fam hd)
      (fun d hd => G.sel_one_bounds (G.isSplit_of_mem_fam hd) (by decide) (by decide))
  have h2 : G.P ≤ G.W - G.A - 1 :=
    G.card_le_of_coord (K := {2, 3}) (i := 3) (k := 2) (by decide) (by decide) G.famP
      (fun d hd => hc ▸ (G.isSplit_of_mem_fam hd).compl)
      (fun d hd => G.sel_two_bounds (hc ▸ (G.isSplit_of_mem_fam hd).compl) (by decide)
        (by decide))
  unfold R; omega

/-- **Lemma 10.** `Q ≤ R - 1`. -/
theorem Q_le : G.Q ≤ G.R - 1 := by
  have hc : ({0, 2} : Finset (Fin 4))ᶜ = {1, 3} := by decide
  have h1 : G.Q ≤ G.W - G.A - 1 :=
    G.card_le_of_coord (i := 0) (k := 2) (by decide) rfl G.famQ
      (fun d hd => G.isSplit_of_mem_fam hd)
      (fun d hd => G.sel_two_bounds (G.isSplit_of_mem_fam hd) (by decide) (by decide))
  have h2 : G.Q ≤ G.B - 1 :=
    G.card_le_of_coord (K := {1, 3}) (i := 3) (k := 1) (by decide) (by decide) G.famQ
      (fun d hd => hc ▸ (G.isSplit_of_mem_fam hd).compl)
      (fun d hd => G.sel_one_bounds (hc ▸ (G.isSplit_of_mem_fam hd).compl) (by decide)
        (by decide))
  unfold R; omega

/-! ### Lemma 12 -/

lemma isSplit12_of_mem_famE {d : ℕ} (h : d ∈ G.famE) : G.IsSplit d {1, 2} := by
  have hc : ({0, 3} : Finset (Fin 4))ᶜ = {1, 2} := by decide
  exact hc ▸ (G.isSplit_of_mem_fam h).compl

/-- **Lemma 12, exclusion step.** At a degree of `ℰ`, the selected interior vector `(0,u,v,0)`
does not satisfy `u ≥ p`, `v ≥ q`, `(u,v) ≠ (p,q)`. -/
theorem not_dominates_pq {d : ℕ} (hd : d ∈ G.famE) (hu : G.p ≤ G.sel d {1, 2} 1)
    (hv : G.q ≤ G.sel d {1, 2} 2) (hne : (G.sel d {1, 2} 1, G.sel d {1, 2} 2) ≠ (G.p, G.q)) :
    False := by
  have hS := G.isSplit12_of_mem_famE hd
  have hK : ({1, 2} : Finset (Fin 4)).card = 2 := by decide
  have hU : G.U3 ≤ G.sel d {1, 2} := by
    intro i; fin_cases i <;> simp [U3, hu, hv]
  have hp := G.p_pos
  by_cases h1 : G.p < G.sel d {1, 2} 1
  · exact G.no_replace hS hK hU G.identity3.1 (k := 1) (by simpa [U3] using h1)
      (j := 0) (by decide) (by simp [V3]; omega)
  · have h2 : G.q < G.sel d {1, 2} 2 := by
      by_contra h2
      exact hne (Prod.ext (by simp only; omega) (by simp only; omega))
    exact G.no_replace hS hK hU G.identity3.1 (k := 2) (by simpa [U3] using h2)
      (j := 0) (by decide) (by simp [V3]; omega)

/-- The selected interior pairs `(u, v)` over `ℰ`. -/
noncomputable def pairsE : Finset (ℕ × ℕ) :=
  G.famE.image (fun d => (G.sel d {1, 2} 1, G.sel d {1, 2} 2))

lemma sel12_le_iff {d d' : ℕ} (hd : d ∈ G.famE) (hd' : d' ∈ G.famE) :
    G.sel d {1, 2} ≤ G.sel d' {1, 2} ↔
      G.sel d {1, 2} 1 ≤ G.sel d' {1, 2} 1 ∧ G.sel d {1, 2} 2 ≤ G.sel d' {1, 2} 2 := by
  have hK : ({1, 2} : Finset (Fin 4)).card = 2 := by decide
  have hS := G.isSplit12_of_mem_famE hd
  have hS' := G.isSplit12_of_mem_famE hd'
  constructor
  · intro h; exact ⟨h 1, h 2⟩
  · rintro ⟨h1, h2⟩ i
    fin_cases i
    · simp [G.sel_eq_zero hS hK (i := 0) (by decide)]
    · exact h1
    · exact h2
    · simp [G.sel_eq_zero hS hK (i := 3) (by decide)]

lemma pairsE_injOn : Set.InjOn (fun d => (G.sel d {1, 2} 1, G.sel d {1, 2} 2)) G.famE := by
  intro d hd d' hd' h
  simp only [Prod.mk.injEq] at h
  have hK : ({1, 2} : Finset (Fin 4)).card = 2 := by decide
  have hle := (G.sel12_le_iff hd hd').2 ⟨h.1.le, h.2.le⟩
  have hge := (G.sel12_le_iff hd' hd).2 ⟨h.1.ge, h.2.ge⟩
  rw [← (G.sel_of_split (G.isSplit12_of_mem_famE hd) hK).1,
    ← (G.sel_of_split (G.isSplit12_of_mem_famE hd') hK).1, le_antisymm hle hge]

lemma card_pairsE : G.pairsE.card = G.E := card_image_of_injOn G.pairsE_injOn

lemma pairsE_antichain : IsPairAntichain G.pairsE := by
  intro x hx y hy h1 h2
  obtain ⟨d, hd, rfl⟩ := mem_image.1 hx
  obtain ⟨d', hd', rfl⟩ := mem_image.1 hy
  have hK : ({1, 2} : Finset (Fin 4)).card = 2 := by decide
  by_cases hne : d = d'
  · rw [hne]
  · exact absurd ((G.sel12_le_iff hd hd').2 ⟨h1, h2⟩)
      (G.sel_antichain hK (G.isSplit12_of_mem_famE hd) (G.isSplit12_of_mem_famE hd') hne)

lemma pairsE_pos : ∀ x ∈ G.pairsE, 1 ≤ x.1 ∧ 1 ≤ x.2 := by
  intro x hx
  obtain ⟨d, hd, rfl⟩ := mem_image.1 hx
  have hK : ({1, 2} : Finset (Fin 4)).card = 2 := by decide
  exact ⟨G.sel_pos (G.isSplit12_of_mem_famE hd) hK (by decide),
    G.sel_pos (G.isSplit12_of_mem_famE hd) hK (by decide)⟩

/-- **Lemma 12.** `E ≤ p + q - 1`. -/
theorem E_le : G.E ≤ G.p + G.q - 1 := by
  by_contra hc
  have hp := G.p_pos
  have hq := G.q_pos
  have hk : G.p + G.q ≤ G.pairsE.card := by rw [card_pairsE]; omega
  obtain ⟨x, hx, hx1, hx2⟩ :=
    G.pairsE_antichain.exists_rank G.pairsE_pos (r := G.p) hp (by omega)
  obtain ⟨d, hd, rfl⟩ := mem_image.1 hx
  exact G.not_dominates_pq hd hx1 (by simp only at hx2; omega)
    (fun h => by simp only [Prod.mk.injEq] at h; simp only at hx2; omega)

end GenData

end SemigroupBetti
