/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/
import SemigroupBetti.Critical

/-!
# Pair partitions, the exact decomposition of `β₁`, and the antichain property

Write-up `PROOF_B_lean_writeup.md`: Lemma 5, Definition 7, Lemma 6, Lemma 7.

A degree `d` *splits along* `K ⊆ Fin 4` (`IsSplit d K`) when `∇_d` has two distinct components
with supports `K` and `Kᶜ`. The partitions `01|23`, `02|13`, `03|12` are `IsSplit d {0,1}`,
`IsSplit d {0,2}`, `IsSplit d {0,3}`.
-/

namespace SemigroupBetti

open Finset

/-- Propagating a property along a reachability path. -/
lemma reachable_induction {V : Type*} {Γ : SimpleGraph V} (P : V → Prop)
    (hstep : ∀ x y, P x → Γ.Adj x y → P y) {x y : V} (h : Γ.Reachable x y) (hx : P x) : P y := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact hx
  | cons ha _ ih => exact ih (hstep _ _ hx ha)

namespace GenData

variable (G : GenData)

/-! ### Splitting along a pair -/

/-- `∇_d` has two distinct components with supports `K` and `Kᶜ`. -/
def IsSplit (d : ℕ) (K : Finset (Fin 4)) : Prop :=
  ∃ C C' : (G.nabla d).ConnectedComponent, C ≠ C' ∧ G.compSupp C = K ∧ G.compSupp C' = Kᶜ

lemma IsSplit.compl {d : ℕ} {K : Finset (Fin 4)} (h : G.IsSplit d K) : G.IsSplit d Kᶜ := by
  obtain ⟨C, C', hne, hC, hC'⟩ := h
  exact ⟨C', C, hne.symm, hC', by rw [compl_compl, hC]⟩

/-- A component containing a factorization positive at some index of `compSupp C` is `C`. -/
lemma comp_eq_of_mem {d : ℕ} {C : (G.nabla d).ConnectedComponent} (z : G.fiber d) {i : Fin 4}
    (hi : i ∈ G.compSupp C) (hzi : 0 < z.1 i) : (G.nabla d).connectedComponentMk z = C := by
  by_contra hne
  exact Finset.disjoint_left.1 (G.compSupp_disjoint hne) (G.supp_subset_compSupp z
    (mem_supp.2 hzi)) hi

/-- **No bridge across a split.** If `d` splits along `K`, `z` is positive somewhere in `K`, `y`
somewhere in `Kᶜ`, then no factorization of `d` shares a variable with both. -/
lemma no_bridge {d : ℕ} {K : Finset (Fin 4)} (hS : G.IsSplit d K) {z y b : Fin 4 → ℕ}
    (hz : G.nu z = d) (hy : G.nu y = d) (hb : G.nu b = d) {i j : Fin 4} (hi : i ∈ K)
    (hzi : 0 < z i) (hj : j ∉ K) (hyj : 0 < y j) (hbz : SharesVar b z) (hby : SharesVar b y) :
    False := by
  obtain ⟨C, C', hne, hC, hC'⟩ := hS
  let z' : G.fiber d := ⟨z, G.mem_fiber.2 hz⟩
  let y' : G.fiber d := ⟨y, G.mem_fiber.2 hy⟩
  have h1 : (G.nabla d).connectedComponentMk z' = C := G.comp_eq_of_mem z' (hC ▸ hi) hzi
  have h2 : (G.nabla d).connectedComponentMk y' = C' :=
    G.comp_eq_of_mem y' (by rw [hC']; exact mem_compl.2 hj) hyj
  apply hne
  rw [← h1, ← h2]
  exact SimpleGraph.ConnectedComponent.sound (G.reachable_of_bridge b hb hbz hby)

/-! ### Lemma 5 -/

/-- **Lemma 5 (full support).** A component with support `{i, j}` contains a factorization
positive at both `i` and `j`. -/
lemma exists_full_vertex {d : ℕ} {C : (G.nabla d).ConnectedComponent} {i j : Fin 4}
    (hij : i ≠ j) (hC : G.compSupp C = {i, j}) :
    ∃ z : G.fiber d, (G.nabla d).connectedComponentMk z = C ∧ 0 < z.1 i ∧ 0 < z.1 j := by
  by_contra H
  push Not at H
  obtain ⟨z0, hz0, hz0i⟩ := G.mem_compSupp.1 (show i ∈ G.compSupp C by rw [hC]; simp)
  obtain ⟨z1, hz1, hz1j⟩ := G.mem_compSupp.1 (show j ∈ G.compSupp C by rw [hC]; simp)
  have hreach : (G.nabla d).Reachable z0 z1 :=
    SimpleGraph.ConnectedComponent.exact (hz0.trans hz1.symm)
  have key := reachable_induction
    (fun x : G.fiber d => (G.nabla d).connectedComponentMk x = C ∧ 0 < x.1 i)
    (by
      rintro x y ⟨hxC, hxi⟩ hadj
      have hyC : (G.nabla d).connectedComponentMk y = C :=
        (SimpleGraph.ConnectedComponent.sound hadj.reachable).symm.trans hxC
      refine ⟨hyC, ?_⟩
      obtain ⟨-, k, hxk, hyk⟩ := hadj
      have hk : k ∈ G.compSupp C := hxC ▸ G.supp_subset_compSupp x (mem_supp.2 hxk)
      rw [hC, mem_insert, mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact hyk
      · have := H x hxC hxi; omega)
    hreach ⟨hz0, hz0i⟩
  have := H z1 hz1 key.2
  omega

/-- A component with support `K` of size two contains a factorization with support exactly `K`. -/
lemma exists_supp_eq {d : ℕ} {C : (G.nabla d).ConnectedComponent} {K : Finset (Fin 4)}
    (hK : K.card = 2) (hC : G.compSupp C = K) :
    ∃ z : G.fiber d, (G.nabla d).connectedComponentMk z = C ∧ supp z.1 = K := by
  obtain ⟨i, j, hij, rfl⟩ := card_eq_two.1 hK
  obtain ⟨z, hz, hzi, hzj⟩ := G.exists_full_vertex hij hC
  refine ⟨z, hz, Finset.Subset.antisymm (hC ▸ hz ▸ G.supp_subset_compSupp z) ?_⟩
  intro k hk
  rw [mem_insert, mem_singleton] at hk
  rcases hk with rfl | rfl <;> simpa

/-- **Lemma 5.** At a contributing degree without singleton-support components, `∇_d` has exactly
two components, and their supports form one of the partitions `01|23`, `02|13`, `03|12`. -/
theorem lemma5 {d : ℕ} (hd : G.contributes d) (hS : ¬ G.HasSingletonComp d) :
    G.ncomp d = 2 ∧ (G.IsSplit d {0, 1} ∨ G.IsSplit d {0, 2} ∨ G.IsSplit d {0, 3}) := by
  classical
  have hdpos := G.pos_of_two_le_ncomp hd
  have hcard2 : ∀ C : (G.nabla d).ConnectedComponent, 2 ≤ (G.compSupp C).card := by
    intro C
    have h0 := (G.compSupp_nonempty hdpos C).card_pos
    have h1 : (G.compSupp C).card ≠ 1 := fun h => hS ⟨C, h⟩
    omega
  have hnt : Nontrivial (G.nabla d).ConnectedComponent := by
    rw [← Fintype.one_lt_card_iff_nontrivial]; exact hd
  obtain ⟨C1, C2, h12⟩ := exists_pair_ne (G.nabla d).ConnectedComponent
  have hdisj := G.compSupp_disjoint h12
  have hu := card_le_univ (G.compSupp C1 ∪ G.compSupp C2)
  rw [card_union_of_disjoint hdisj, Fintype.card_fin] at hu
  have hc1 := hcard2 C1
  have hc2 := hcard2 C2
  have huniv : G.compSupp C1 ∪ G.compSupp C2 = univ := by
    apply eq_univ_of_card
    rw [card_union_of_disjoint hdisj, Fintype.card_fin]; omega
  have hcompl : G.compSupp C2 = (G.compSupp C1)ᶜ := by
    ext k
    rw [mem_compl]
    constructor
    · intro hk hk1; exact Finset.disjoint_left.1 hdisj hk1 hk
    · intro hk
      have : k ∈ G.compSupp C1 ∪ G.compSupp C2 := huniv ▸ mem_univ k
      rcases mem_union.1 this with h | h
      · exact absurd h hk
      · exact h
  -- every component is `C1` or `C2`
  have hall : ∀ C, C = C1 ∨ C = C2 := by
    intro C
    by_contra hC
    push Not at hC
    obtain ⟨k, hk⟩ := G.compSupp_nonempty hdpos C
    have : k ∈ G.compSupp C1 ∪ G.compSupp C2 := huniv ▸ mem_univ k
    rcases mem_union.1 this with h | h
    · exact Finset.disjoint_left.1 (G.compSupp_disjoint hC.1) hk h
    · exact Finset.disjoint_left.1 (G.compSupp_disjoint hC.2) hk h
  refine ⟨?_, ?_⟩
  · unfold ncomp
    rw [← card_univ, show (univ : Finset (G.nabla d).ConnectedComponent) = {C1, C2} by
      ext C; simp only [mem_univ, mem_insert, mem_singleton, true_iff]; exact hall C]
    exact card_pair h12
  · -- the component whose support contains `0`
    have hsplit1 : G.IsSplit d (G.compSupp C1) := ⟨C1, C2, h12, rfl, hcompl⟩
    have hsplit2 : G.IsSplit d (G.compSupp C2) := by
      rw [hcompl]; exact hsplit1.compl
    have hc1' : (G.compSupp C1).card = 2 := by omega
    have hc2' : (G.compSupp C2).card = 2 := by omega
    have key : ∀ K : Finset (Fin 4), K.card = 2 → 0 ∈ K → K = {0, 1} ∨ K = {0, 2} ∨ K = {0, 3} := by
      decide
    have h0 : (0 : Fin 4) ∈ G.compSupp C1 ∪ G.compSupp C2 := huniv ▸ mem_univ 0
    rcases mem_union.1 h0 with h | h
    · rcases key _ hc1' h with e | e | e <;> rw [e] at hsplit1 <;> simp [hsplit1]
    · rcases key _ hc2' h with e | e | e <;> rw [e] at hsplit2 <;> simp [hsplit2]

/-- If `d` splits along a pair `K` then it has a factorization with support exactly `K`. -/
lemma exists_supp_eq_of_split {d : ℕ} {K : Finset (Fin 4)} (hS : G.IsSplit d K)
    (hK : K.card = 2) : ∃ z : Fin 4 → ℕ, G.nu z = d ∧ supp z = K := by
  obtain ⟨C, -, -, hC, -⟩ := hS
  obtain ⟨z, -, hz⟩ := G.exists_supp_eq hK hC
  exact ⟨z.1, G.mem_fiber.1 z.2, hz⟩

/-! ### Definition 7 -/

/-- The pair family for the partition `K | Kᶜ`: contributing degrees `≤ H` without
singleton-support components which split along `K`. -/
noncomputable def fam (K : Finset (Fin 4)) : Finset ℕ := by
  classical
  exact (range (G.H + 1)).filter
    (fun d => G.contributes d ∧ ¬ G.HasSingletonComp d ∧ G.IsSplit d K)

lemma mem_fam {K : Finset (Fin 4)} {d : ℕ} :
    d ∈ G.fam K ↔ d ≤ G.H ∧ G.contributes d ∧ ¬ G.HasSingletonComp d ∧ G.IsSplit d K := by
  classical
  unfold fam; simp only [mem_filter, mem_range, Nat.lt_succ_iff]

/-- `𝓟` (partition `01|23`), `𝓠` (`02|13`), `ℰ` (`03|12`). -/
noncomputable def famP : Finset ℕ := G.fam {0, 1}
noncomputable def famQ : Finset ℕ := G.fam {0, 2}
noncomputable def famE : Finset ℕ := G.fam {0, 3}

/-- `P = |𝓟|`, `Q = |𝓠|`, `E = |ℰ|`. -/
noncomputable def P : ℕ := G.famP.card
noncomputable def Q : ℕ := G.famQ.card
noncomputable def E : ℕ := G.famE.card

/-- The selected factorization of `d` with support exactly `K` (a fixed choice; `0` if none). -/
noncomputable def sel (d : ℕ) (K : Finset (Fin 4)) : Fin 4 → ℕ := by
  classical
  exact if h : ∃ z : Fin 4 → ℕ, G.nu z = d ∧ supp z = K then h.choose else 0

lemma sel_spec {d : ℕ} {K : Finset (Fin 4)} (h : ∃ z : Fin 4 → ℕ, G.nu z = d ∧ supp z = K) :
    G.nu (G.sel d K) = d ∧ supp (G.sel d K) = K := by
  classical
  unfold sel; rw [dite_eq_left_of_eq_true (eq_true h)]; exact h.choose_spec

/-- The selected vectors at a split degree: `ν = d` and support `K`. -/
lemma sel_of_split {d : ℕ} {K : Finset (Fin 4)} (hS : G.IsSplit d K) (hK : K.card = 2) :
    G.nu (G.sel d K) = d ∧ supp (G.sel d K) = K :=
  G.sel_spec (G.exists_supp_eq_of_split hS hK)

lemma card_compl_of_card_two {K : Finset (Fin 4)} (hK : K.card = 2) : Kᶜ.card = 2 := by
  rw [card_compl, Fintype.card_fin, hK]

lemma sel_pos {d : ℕ} {K : Finset (Fin 4)} (hS : G.IsSplit d K) (hK : K.card = 2) {i : Fin 4}
    (hi : i ∈ K) : 0 < G.sel d K i := by
  rw [← mem_supp, (G.sel_of_split hS hK).2]; exact hi

lemma sel_eq_zero {d : ℕ} {K : Finset (Fin 4)} (hS : G.IsSplit d K) (hK : K.card = 2) {i : Fin 4}
    (hi : i ∉ K) : G.sel d K i = 0 := by
  by_contra h
  exact hi ((G.sel_of_split hS hK).2 ▸ mem_supp.2 (Nat.pos_of_ne_zero h))

/-- **Selected-vector replacement principle** (Lemma 2 applied to the selected vectors): at a
degree splitting along a pair `K`, no replacement `z - U + V` of the selected `K`-vector `z`
keeps a coordinate of `z` and gains a coordinate outside `K`. -/
lemma no_replace {d : ℕ} {K : Finset (Fin 4)} (hS : G.IsSplit d K) (hK : K.card = 2)
    {U V : Fin 4 → ℕ} (hUz : U ≤ G.sel d K) (hUV : G.nu U = G.nu V) {k j : Fin 4}
    (hk : U k < G.sel d K k) (hj : j ∉ K) (hVj : 0 < V j) : False := by
  have hz := G.sel_of_split hS hK
  have hy := G.sel_of_split hS.compl (card_compl_of_card_two hK)
  have hkK : k ∈ K := hz.2 ▸ mem_supp.2 (by omega)
  have hyj : 0 < G.sel d Kᶜ j := by rw [← mem_supp, hy.2]; exact mem_compl.2 hj
  refine G.no_bridge hS hz.1 hy.1 ((G.nu_replace hUz hUV).trans hz.1) hkK (by omega) hj hyj
    ⟨k, ?_, by omega⟩ ⟨j, ?_, hyj⟩
  · simp only [Pi.add_apply, Pi.sub_apply]; omega
  · simp only [Pi.add_apply, Pi.sub_apply]; omega

/-! ### Lemma 6 -/

lemma isSplit_exclusive {d : ℕ} {K L : Finset (Fin 4)} (hK : G.IsSplit d K) (hL : G.IsSplit d L)
    {i : Fin 4} (hiK : i ∈ K) (hiL : i ∈ L) : K = L := by
  obtain ⟨C, -, -, hC, -⟩ := hK
  obtain ⟨C', -, -, hC', -⟩ := hL
  by_contra hne
  have : C ≠ C' := by rintro rfl; exact hne (hC.symm.trans hC')
  exact Finset.disjoint_left.1 (G.compSupp_disjoint this) (hC ▸ hiK) (hC' ▸ hiL)

/-- **Lemma 6.** `β₁ = σ + P + Q + E`, and `c_d = 2` on the three pair families. -/
theorem beta1_eq : G.beta1 = G.sigma + G.P + G.Q + G.E := by
  classical
  have hpt : ∀ d ∈ range (G.H + 1), G.ncomp d - 1 =
      (if d ∈ G.singletonDegrees then G.ncomp d - 1 else 0) + (if d ∈ G.famP then 1 else 0) +
      (if d ∈ G.famQ then 1 else 0) + (if d ∈ G.famE then 1 else 0) := by
    intro d hd
    have hdH : d ≤ G.H := Nat.lt_succ_iff.1 (mem_range.1 hd)
    simp only [famP, famQ, famE, G.mem_fam, G.mem_singletonDegrees]
    by_cases hc : G.contributes d
    · by_cases hS : G.HasSingletonComp d
      · simp [hc, hS, hdH]
      · obtain ⟨h2, hsp⟩ := G.lemma5 hc hS
        have e12 : ¬ (G.IsSplit d {0, 1} ∧ G.IsSplit d {0, 2}) := fun h =>
          absurd (G.isSplit_exclusive h.1 h.2 (i := 0) (by simp) (by simp)) (by decide)
        have e13 : ¬ (G.IsSplit d {0, 1} ∧ G.IsSplit d {0, 3}) := fun h =>
          absurd (G.isSplit_exclusive h.1 h.2 (i := 0) (by simp) (by simp)) (by decide)
        have e23 : ¬ (G.IsSplit d {0, 2} ∧ G.IsSplit d {0, 3}) := fun h =>
          absurd (G.isSplit_exclusive h.1 h.2 (i := 0) (by simp) (by simp)) (by decide)
        rcases hsp with h | h | h
        · have : ¬ G.IsSplit d {0, 2} := fun h' => e12 ⟨h, h'⟩
          have : ¬ G.IsSplit d {0, 3} := fun h' => e13 ⟨h, h'⟩
          simp [*]
        · have : ¬ G.IsSplit d {0, 1} := fun h' => e12 ⟨h', h⟩
          have : ¬ G.IsSplit d {0, 3} := fun h' => e23 ⟨h, h'⟩
          simp [*]
        · have : ¬ G.IsSplit d {0, 1} := fun h' => e13 ⟨h', h⟩
          have : ¬ G.IsSplit d {0, 2} := fun h' => e23 ⟨h', h⟩
          simp [*]
    · have : G.ncomp d ≤ 1 := by unfold contributes at hc; omega
      simp [hc]; omega
  have hsub : ∀ s : Finset ℕ, s ⊆ range (G.H + 1) →
      s.card = ∑ d ∈ range (G.H + 1), (if d ∈ s then 1 else 0) := by
    intro s hs
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hs]; simp
  have hfam : ∀ K, G.fam K ⊆ range (G.H + 1) := by
    intro K d hd; exact mem_range.2 (Nat.lt_succ_of_le (G.mem_fam.1 hd).1)
  have hsig : G.sigma = ∑ d ∈ range (G.H + 1),
      (if d ∈ G.singletonDegrees then G.ncomp d - 1 else 0) := by
    have hsd : G.singletonDegrees ⊆ range (G.H + 1) := by
      intro d hd; exact mem_range.2 (Nat.lt_succ_of_le (G.mem_singletonDegrees.1 hd).1)
    rw [sigma, Finset.sum_ite_mem, Finset.inter_eq_right.2 hsd]
  rw [beta1, Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, hsig, P, Q, E, hsub G.famP (hfam _), hsub G.famQ (hfam _),
    hsub G.famE (hfam _)]

lemma ncomp_eq_two_of_mem_fam {K : Finset (Fin 4)} {d : ℕ} (h : d ∈ G.fam K) : G.ncomp d = 2 := by
  obtain ⟨-, hc, hS, -⟩ := G.mem_fam.1 h
  exact (G.lemma5 hc hS).1

/-! ### Lemma 7 -/

/-- **Lemma 7.** For a fixed side `K` (a pair), the selected `K`-vectors at distinct split degrees
are not comparable: `¬ (z_d ≤ z_{d'})`. -/
theorem sel_antichain {K : Finset (Fin 4)} (hK : K.card = 2) {d d' : ℕ} (hS : G.IsSplit d K)
    (hS' : G.IsSplit d' K) (hne : d ≠ d') : ¬ G.sel d K ≤ G.sel d' K := by
  intro hle
  have hz := G.sel_of_split hS hK
  have hz' := G.sel_of_split hS' hK
  have hKc := card_compl_of_card_two hK
  have hy := G.sel_of_split hS.compl hKc
  have hy' := G.sel_of_split hS'.compl hKc
  set z := G.sel d K
  set z' := G.sel d' K
  set y := G.sel d Kᶜ
  set y' := G.sel d' Kᶜ
  -- `δ = z' - z ≠ 0`
  have hδ : ∃ i, z i < z' i := by
    by_contra h
    push Not at h
    apply hne
    rw [← hz.1, ← hz'.1]
    congr 1
    funext i; exact le_antisymm (hle i) (h i)
  obtain ⟨i, hi⟩ := hδ
  have hiK : i ∈ K := hz'.2 ▸ mem_supp.2 (by omega)
  obtain ⟨j, hj⟩ : Kᶜ.Nonempty := card_pos.1 (by omega)
  have hyj : 0 < y j := by rw [← mem_supp, hy.2]; exact hj
  have hy'j : 0 < y' j := by rw [← mem_supp, hy'.2]; exact hj
  have hb : G.nu (z' - z + y) = d' := by
    rw [G.nu_replace hle (hz.1.trans hy.1.symm), hz'.1]
  refine G.no_bridge hS' hz'.1 hy'.1 hb hiK (by omega) (mem_compl.1 hj) hy'j
    ⟨i, ?_, by omega⟩ ⟨j, ?_, hy'j⟩
  · simp only [Pi.add_apply, Pi.sub_apply]; omega
  · simp only [Pi.add_apply, Pi.sub_apply]; omega

end GenData

end SemigroupBetti
