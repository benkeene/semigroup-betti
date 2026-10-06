/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/
import SemigroupBetti.Fiber

/-!
# Critical exponents and singleton-support components

Write-up `PROOF_B_lean_writeup.md`: Definition 5, Lemma 3, Definition 6, Lemma 4.
Here `k • eᵢ` is written `Pi.single i k`.
-/

namespace SemigroupBetti

open Finset

namespace GenData

variable (G : GenData)

/-- A factorization `y` dominates the "pair" `y k nₖ + y i nᵢ` for `k ≠ i`. -/
lemma pair_le_nu (y : Fin 4 → ℕ) {k i : Fin 4} (hki : k ≠ i) :
    y k * G.n k + y i * G.n i ≤ G.nu y :=
  Finset.add_le_sum (f := fun j => y j * G.n j) (fun _ _ => Nat.zero_le _)
    (mem_univ k) (mem_univ i) hki

/-! ### Definition 5 -/

/-- Membership in `Tᵢ`: `k ≥ 1` and `k nᵢ` has a factorization other than `k eᵢ`.
(The existential is over the finite fiber, which makes it decidable.) -/
def IsCritCand (i : Fin 4) (k : ℕ) : Prop :=
  1 ≤ k ∧ ∃ y ∈ G.fiber (k * G.n i), y ≠ Pi.single i k

instance (i : Fin 4) : DecidablePred (G.IsCritCand i) := fun k =>
  inferInstanceAs (Decidable (1 ≤ k ∧ ∃ y ∈ G.fiber (k * G.n i), y ≠ Pi.single i k))

lemma isCritCand_iff {i : Fin 4} {k : ℕ} :
    G.IsCritCand i k ↔ 1 ≤ k ∧ ∃ y : Fin 4 → ℕ, G.nu y = k * G.n i ∧ y ≠ Pi.single i k := by
  simp [IsCritCand]

/-- `nⱼ ∈ Tᵢ` for `j ≠ i`, witnessed by `nᵢ eⱼ ≠ nⱼ eᵢ`. -/
lemma isCritCand_n {i j : Fin 4} (hji : j ≠ i) : G.IsCritCand i (G.n j) := by
  rw [isCritCand_iff]
  refine ⟨G.n_pos j, Pi.single j (G.n i), by rw [G.nu_single, mul_comm], ?_⟩
  intro h
  have := congrFun h j
  simp [hji, (G.n_pos i).ne'] at this

lemma succ_ne (i : Fin 4) : i + 1 ≠ i := by fin_cases i <;> decide

lemma crit_exists (i : Fin 4) : ∃ k, G.IsCritCand i k := ⟨_, G.isCritCand_n (succ_ne i)⟩

/-- **Definition 5.** The critical exponent `cᵢ = min Tᵢ`. -/
def crit (i : Fin 4) : ℕ := Nat.find (G.crit_exists i)

lemma crit_spec (i : Fin 4) : G.IsCritCand i (G.crit i) := Nat.find_spec (G.crit_exists i)

/-! ### Lemma 3 -/

/-- **Lemma 3.1.** `1 ≤ cᵢ`. -/
lemma one_le_crit (i : Fin 4) : 1 ≤ G.crit i := (G.crit_spec i).1

/-- **Lemma 3.1.** `cᵢ ≤ nⱼ` for every `j ≠ i`. -/
lemma crit_le_n {i j : Fin 4} (hji : j ≠ i) : G.crit i ≤ G.n j :=
  Nat.find_min' _ (G.isCritCand_n hji)

lemma exists_alt (i : Fin 4) :
    ∃ y : Fin 4 → ℕ, G.nu y = G.crit i * G.n i ∧ y ≠ Pi.single i (G.crit i) :=
  (G.isCritCand_iff.1 (G.crit_spec i)).2

/-- **Lemma 3.2.** Every alternative factorization at the critical degree avoids `i`. -/
lemma alt_coord_eq_zero {i : Fin 4} {y : Fin 4 → ℕ} (hy : G.nu y = G.crit i * G.n i)
    (hne : y ≠ Pi.single i (G.crit i)) : y i = 0 := by
  by_contra hyi
  have hyi : 0 < y i := Nat.pos_of_ne_zero hyi
  have hni := G.n_pos i
  have hle : y i ≤ G.crit i := by
    have := G.single_le_nu y i
    rw [hy] at this
    exact Nat.le_of_mul_le_mul_right this hni
  rcases hle.lt_or_eq with hlt | heq
  · -- `v = y - yᵢ eᵢ` is an alternative for `r = cᵢ - yᵢ < cᵢ`
    have hsub : Pi.single i (y i) ≤ y := by
      intro k; by_cases hk : k = i
      · subst hk; simp
      · simp [hk]
    have hnu := G.nu_sub hsub
    rw [G.nu_single, hy] at hnu
    have hcand : G.IsCritCand i (G.crit i - y i) := by
      rw [isCritCand_iff]
      refine ⟨by omega, y - Pi.single i (y i), ?_, ?_⟩
      · rw [Nat.sub_mul]; omega
      · intro h
        have := congrFun h i
        simp at this; omega
    exact Nat.find_min (G.crit_exists i) (show G.crit i - y i < G.crit i by omega) hcand
  · -- `yᵢ = cᵢ` forces `y = cᵢ eᵢ`
    apply hne
    funext k
    by_cases hk : k = i
    · subst hk; simp [heq]
    · have h2 := G.pair_le_nu y hk
      rw [hy, heq] at h2
      have : y k * G.n k = 0 := by omega
      simp [hk, (G.n_pos k).ne'] at this ⊢; exact this

/-- The vertex `cᵢ eᵢ` of `∇_{cᵢ nᵢ}`. -/
def critVertex (i : Fin 4) : G.fiber (G.crit i * G.n i) :=
  ⟨Pi.single i (G.crit i), G.mem_fiber.2 (G.nu_single i _)⟩

/-- **Lemma 3.3.** `cᵢ eᵢ` is isolated in `∇_{cᵢ nᵢ}`. -/
lemma critVertex_not_adj (i : Fin 4) (z : G.fiber (G.crit i * G.n i)) :
    ¬ (G.nabla _).Adj (G.critVertex i) z := by
  rintro ⟨hne, k, hk, hzk⟩
  have hki : k = i := by
    by_contra h; simp [critVertex, h] at hk
  subst hki
  have hz : z.1 ≠ Pi.single k (G.crit k) := fun h => hne (Subtype.ext h.symm)
  have := G.alt_coord_eq_zero (G.mem_fiber.1 z.2) hz
  omega

/-- **Lemma 3.3.** The component of `cᵢ eᵢ` is `{cᵢ eᵢ}`. -/
lemma eq_critVertex_of_reachable (i : Fin 4) {z : G.fiber (G.crit i * G.n i)}
    (h : (G.nabla _).Reachable (G.critVertex i) z) : z = G.critVertex i := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => rfl
  | cons hadj _ => exact absurd hadj (G.critVertex_not_adj i _)

/-- **Lemma 3.3.** The component `{cᵢ eᵢ}` has support `{i}`. -/
lemma compSupp_critVertex (i : Fin 4) :
    G.compSupp ((G.nabla _).connectedComponentMk (G.critVertex i)) = {i} := by
  ext k
  rw [mem_compSupp, mem_singleton]
  constructor
  · rintro ⟨z, hz, hzk⟩
    have := G.eq_critVertex_of_reachable i (SimpleGraph.ConnectedComponent.exact hz).symm
    subst this
    by_contra h; simp [critVertex, h] at hzk
  · intro h
    rw [h]
    exact ⟨G.critVertex i, rfl, by simpa [critVertex] using Nat.lt_of_lt_of_le Nat.zero_lt_one (G.one_le_crit i)⟩

/-- **Lemma 3.4 (vertex form).** At a contributing degree, every vertex of a component with
support `{i}` is `cᵢ eᵢ`, and the degree is `cᵢ nᵢ`. -/
lemma singleton_comp_vertex {d : ℕ} (hd : G.contributes d) {i : Fin 4}
    {C : (G.nabla d).ConnectedComponent} (hC : G.compSupp C = {i}) (z : G.fiber d)
    (hz : (G.nabla d).connectedComponentMk z = C) :
    z.1 = Pi.single i (G.crit i) ∧ d = G.crit i * G.n i := by
  have hzd := G.mem_fiber.1 z.2
  have hdpos := G.pos_of_two_le_ncomp hd
  -- `z = k eᵢ` with `k = zᵢ`
  have hzform : z.1 = Pi.single i (z.1 i) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp only [Pi.single_apply, hj, ite_false]
      by_contra hzj
      have : j ∈ G.compSupp C := G.mem_compSupp.2 ⟨z, hz, Nat.pos_of_ne_zero hzj⟩
      rw [hC, mem_singleton] at this; exact hj this
  set k := z.1 i with hk
  have hdk : d = k * G.n i := by rw [← hzd, hzform, G.nu_single]
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, zero_mul] at hdk; omega
    · exact h
  rcases lt_trichotomy k (G.crit i) with hlt | heq | hgt
  · -- no alternative: the fiber is a single vertex
    exfalso
    have hall : ∀ y : G.fiber d, y = z := by
      intro y
      by_contra hyz
      have hy : y.1 ≠ Pi.single i k := by
        intro h; exact hyz (Subtype.ext (h.trans hzform.symm))
      have hcand : G.IsCritCand i k :=
        G.isCritCand_iff.2 ⟨hkpos, y.1, (G.mem_fiber.1 y.2).trans hdk, hy⟩
      exact Nat.find_min (G.crit_exists i) hlt hcand
    have := G.ncomp_le_one_of_reachable (d := d) (fun y y' => by rw [hall y, hall y'])
    unfold contributes at hd; omega
  · exact ⟨hzform.trans (by rw [heq]), by rw [hdk, heq]⟩
  · -- the bridge `b = (k - cᵢ) eᵢ + y` enlarges the support
    exfalso
    obtain ⟨y, hy, hyne⟩ := G.exists_alt i
    have hyi := G.alt_coord_eq_zero hy hyne
    have hy0 : y ≠ 0 := by
      intro h; rw [h, nu_zero] at hy
      have := Nat.mul_pos (G.one_le_crit i) (G.n_pos i); omega
    obtain ⟨j, hj⟩ : ∃ j, 0 < y j := by
      by_contra hc; push Not at hc
      exact hy0 (funext fun l => Nat.le_zero.1 (hc l))
    have hji : j ≠ i := by rintro rfl; omega
    let b := Pi.single i (k - G.crit i) + y
    have hb : G.nu b = d := by
      simp only [b]; rw [G.nu_add, G.nu_single, hy, hdk, ← Nat.add_mul, Nat.sub_add_cancel hgt.le]
    let b' : G.fiber d := ⟨b, G.mem_fiber.2 hb⟩
    have hbz : (G.nabla d).connectedComponentMk b' = C := by
      rw [← hz]
      apply SimpleGraph.ConnectedComponent.sound
      apply G.reachable_of_sharesVar
      refine ⟨i, ?_, ?_⟩
      · simp [b', b, hyi]; omega
      · rw [← hk]; exact hkpos
    have : j ∈ G.compSupp C := G.mem_compSupp.2 ⟨b', hbz, by simp [b', b, hji.symm, hj]⟩
    rw [hC, mem_singleton] at this
    exact hji this

/-- **Lemma 3.4.** At a contributing degree, a component with support `{i}` lives in degree
`cᵢ nᵢ`. -/
lemma degree_eq_of_singleton_comp {d : ℕ} (hd : G.contributes d) {i : Fin 4}
    {C : (G.nabla d).ConnectedComponent} (hC : G.compSupp C = {i}) :
    d = G.crit i * G.n i := by
  induction C using SimpleGraph.ConnectedComponent.ind with
  | h z => exact (G.singleton_comp_vertex hd hC z rfl).2

/-- **Lemma 3.4.** At the contributing degree `cᵢ nᵢ`, a component with support `{i}` is
`{cᵢ eᵢ}`. -/
lemma comp_eq_critVertex {i : Fin 4} (hd : G.contributes (G.crit i * G.n i))
    {C : (G.nabla _).ConnectedComponent} (hC : G.compSupp C = {i}) :
    C = (G.nabla _).connectedComponentMk (G.critVertex i) := by
  induction C using SimpleGraph.ConnectedComponent.ind with
  | h z =>
    have := (G.singleton_comp_vertex hd hC z rfl).1
    rw [show z = G.critVertex i from Subtype.ext this]

/-- **Lemma 3.5.** Under generator minimality, `cᵢ ≥ 2`. -/
lemma two_le_crit (i : Fin 4) : 2 ≤ G.crit i := by
  by_contra h
  have h1 : G.crit i = 1 := by have := G.one_le_crit i; omega
  obtain ⟨y, hy, hyne⟩ := G.exists_alt i
  have hyi := G.alt_coord_eq_zero hy hyne
  rw [h1, one_mul] at hy
  exact G.minimal' i y hyi hy

/-! ### Definition 6 and Lemma 4 -/

/-- Some component of `∇_d` has support of cardinality one. -/
def HasSingletonComp (d : ℕ) : Prop :=
  ∃ C : (G.nabla d).ConnectedComponent, (G.compSupp C).card = 1

/-- **Definition 6.** `𝓢`: contributing degrees having a singleton-support component (bounded by
`H`, which loses nothing by Lemma 0A). -/
noncomputable def singletonDegrees : Finset ℕ := by
  classical
  exact (range (G.H + 1)).filter (fun d => G.contributes d ∧ G.HasSingletonComp d)

lemma mem_singletonDegrees {d : ℕ} :
    d ∈ G.singletonDegrees ↔ d ≤ G.H ∧ G.contributes d ∧ G.HasSingletonComp d := by
  classical
  unfold singletonDegrees; simp only [mem_filter, mem_range, Nat.lt_succ_iff]

/-- Every contributing degree with a singleton-support component lies in `𝓢`
(the cutoff is harmless by Lemma 0A). -/
lemma mem_singletonDegrees_of {d : ℕ} (hd : G.contributes d) (hS : G.HasSingletonComp d) :
    d ∈ G.singletonDegrees :=
  G.mem_singletonDegrees.2 ⟨G.le_H_of_contributes hd, hd, hS⟩

/-- **Definition 6.** `σ = ∑_{d ∈ 𝓢} (c_d - 1)`. -/
noncomputable def sigma : ℕ := ∑ d ∈ G.singletonDegrees, (G.ncomp d - 1)

/-- The indices whose critical degree is `d`. -/
def critIndices (d : ℕ) : Finset (Fin 4) := univ.filter (fun i => G.crit i * G.n i = d)

/-- **Lemma 4, per-degree step.** For `d ∈ 𝓢`: `c_d - 1 ≤ r_d ≤ #{i : cᵢ nᵢ = d}`. -/
lemma ncomp_sub_one_le {d : ℕ} (hd : G.contributes d) (hS : G.HasSingletonComp d) :
    G.ncomp d - 1 ≤ (G.critIndices d).card := by
  classical
  have hdpos := G.pos_of_two_le_ncomp hd
  set K1 := (univ : Finset (G.nabla d).ConnectedComponent).filter
    (fun C => (G.compSupp C).card = 1) with hK1
  set K2 := (univ : Finset (G.nabla d).ConnectedComponent).filter
    (fun C => ¬ (G.compSupp C).card = 1) with hK2
  have hsplit : K1.card + K2.card = G.ncomp d := by
    rw [hK1, hK2, card_filter_add_card_filter_not]; rfl
  -- `r_d = #K1 ≤ #{i : cᵢ nᵢ = d}`: the singleton supports are disjoint and indexed by
  -- critical indices (Lemmas 2.1 and 3.4)
  have hK1le : K1.card ≤ (G.critIndices d).card := by
    have hdisj : (K1 : Set (G.nabla d).ConnectedComponent).PairwiseDisjoint G.compSupp :=
      fun C _ C' _ h => G.compSupp_disjoint h
    have hcard : (K1.biUnion G.compSupp).card = K1.card := by
      rw [card_biUnion hdisj]
      rw [Finset.sum_congr rfl (fun C hC => (mem_filter.1 hC).2)]
      simp [hK1]
    rw [← hcard]
    apply card_le_card
    intro i hi
    obtain ⟨C, hC, hiC⟩ := mem_biUnion.1 hi
    obtain ⟨i', hi'⟩ := card_eq_one.1 (mem_filter.1 hC).2
    rw [hi', mem_singleton] at hiC
    subst hiC
    simp only [critIndices, mem_filter, mem_univ, true_and]
    exact (G.degree_eq_of_singleton_comp hd hi').symm
  -- at most one component with support of size `≥ 2`
  have hK2le : K2.card ≤ 1 := by
    obtain ⟨C0, hC0⟩ := hS
    rw [card_le_one]
    intro C hC C' hC'
    by_contra hne
    have hC2 : 2 ≤ (G.compSupp C).card := by
      have h1 := (mem_filter.1 hC).2
      have h0 := (G.compSupp_nonempty hdpos C).card_pos
      omega
    have hC'2 : 2 ≤ (G.compSupp C').card := by
      have h1 := (mem_filter.1 hC').2
      have h0 := (G.compSupp_nonempty hdpos C').card_pos
      omega
    have hCC0 : C ≠ C0 := by rintro rfl; exact (mem_filter.1 hC).2 hC0
    have hC'C0 : C' ≠ C0 := by rintro rfl; exact (mem_filter.1 hC').2 hC0
    have hu := card_le_univ (G.compSupp C ∪ G.compSupp C' ∪ G.compSupp C0)
    rw [card_union_of_disjoint, card_union_of_disjoint (G.compSupp_disjoint hne)] at hu
    · simp only [Fintype.card_fin] at hu; omega
    · exact disjoint_union_left.2 ⟨G.compSupp_disjoint hCC0, G.compSupp_disjoint hC'C0⟩
  omega

/-- **Lemma 4.** Singleton-support degrees contribute at most four: `σ ≤ 4`. -/
theorem sigma_le_four : G.sigma ≤ 4 := by
  classical
  let f : Fin 4 → ℕ := fun i => G.crit i * G.n i
  let s := univ.filter (fun i => f i ∈ G.singletonDegrees)
  have hmaps : (s : Set (Fin 4)).MapsTo f G.singletonDegrees := fun i hi => (mem_filter.1 hi).2
  calc G.sigma = ∑ d ∈ G.singletonDegrees, (G.ncomp d - 1) := rfl
    _ ≤ ∑ d ∈ G.singletonDegrees, (G.critIndices d).card := by
      apply sum_le_sum
      intro d hd
      obtain ⟨-, hc, hS⟩ := G.mem_singletonDegrees.1 hd
      exact G.ncomp_sub_one_le hc hS
    _ = ∑ d ∈ G.singletonDegrees, (s.filter (fun i => f i = d)).card := by
      apply sum_congr rfl
      intro d hd
      congr 1
      ext i
      simp only [critIndices, s, f, mem_filter, mem_univ, true_and]
      constructor
      · intro h; exact ⟨h ▸ hd, h⟩
      · exact fun h => h.2
    _ = s.card := (card_eq_sum_card_fiberwise hmaps).symm
    _ ≤ 4 := by simpa using card_le_univ s

end GenData

end SemigroupBetti
