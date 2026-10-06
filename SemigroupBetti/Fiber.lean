/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/
import SemigroupBetti.Defs

/-!
# Fibers, factorization graphs, combinatorial `β₁`, the finite cutoff, and Lemma 2

Write-up `PROOF_B_lean_writeup.md`: Definition 3, Lemma 0 part A, Lemma 2.
-/

namespace SemigroupBetti

open Finset

namespace GenData

variable (G : GenData)

/-! ### Definition 3: fibers -/

/-- The fiber `F_d = {z ∈ ℕ⁴ : ν(z) = d}`, enumerated inside the box `{0,…,d/m}⁴`. -/
def fiber (d : ℕ) : Finset (Fin 4 → ℕ) :=
  (Fintype.piFinset fun _ => range (d / G.m + 1)).filter (fun z => G.nu z = d)

/-- Every factorization of `d` lies in the box `{0,…,d/m}⁴` (Lemma 0A, first paragraph). -/
lemma le_div_m_of_nu_eq {z : Fin 4 → ℕ} {d : ℕ} (h : G.nu z = d) (i : Fin 4) :
    z i ≤ d / G.m := by
  rw [Nat.le_div_iff_mul_le G.m_pos, mul_comm, ← h]; exact G.m_mul_le_nu z i

@[simp] lemma mem_fiber {d : ℕ} {z : Fin 4 → ℕ} : z ∈ G.fiber d ↔ G.nu z = d := by
  simp only [fiber, mem_filter, Fintype.mem_piFinset, mem_range, and_iff_right_iff_imp]
  intro h i; exact Nat.lt_succ_of_le (G.le_div_m_of_nu_eq h i)

lemma fiber_zero : G.fiber 0 = {0} := by
  ext z; simp [G.nu_eq_zero_iff]

/-! ### Definition 3: the graph `∇_d` -/

/-- The factorization graph `∇_d` on the fiber: distinct factorizations sharing a variable. -/
def nabla (d : ℕ) : SimpleGraph (G.fiber d) where
  Adj z z' := z ≠ z' ∧ SharesVar z.1 z'.1
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (d : ℕ) : DecidableRel (G.nabla d).Adj := fun z z' =>
  inferInstanceAs (Decidable (z ≠ z' ∧ SharesVar z.1 z'.1))

lemma nabla_adj {d : ℕ} {z z' : G.fiber d} :
    (G.nabla d).Adj z z' ↔ z ≠ z' ∧ SharesVar z.1 z'.1 := Iff.rfl

/-- `c_d`: the number of connected components of `∇_d` (`0` when the fiber is empty). -/
def ncomp (d : ℕ) : ℕ := Fintype.card (G.nabla d).ConnectedComponent

/-- A degree contributes when `∇_d` has at least two components (this forces `d ∈ S`). -/
def contributes (d : ℕ) : Prop := 2 ≤ G.ncomp d

instance (d : ℕ) : Decidable (G.contributes d) := inferInstanceAs (Decidable (2 ≤ _))

/-- The explicit cutoff `H = N (n₀+n₁+n₂+n₃)` with `N = n₃` (Lemma 0, §3 preamble). -/
def H : ℕ := G.n 3 * ∑ i, G.n i

/-- **Definition 3 (bounded form).** The combinatorial first Betti number
`β₁ = ∑_{d ≤ H} (c_d - 1)`; by Lemma 0A (`ncomp_le_one_of_H_lt`) no degree above `H`
contributes, and degrees with `c_d ≤ 1` add `0`. -/
def beta1 : ℕ := ∑ d ∈ range (G.H + 1), (G.ncomp d - 1)

/-- The support of a component: the union of the supports of its vertices. -/
noncomputable def compSupp {d : ℕ} (C : (G.nabla d).ConnectedComponent) : Finset (Fin 4) := by
  classical
  exact univ.filter (fun i => ∃ z : G.fiber d, (G.nabla d).connectedComponentMk z = C ∧ 0 < z.1 i)

lemma mem_compSupp {d : ℕ} {C : (G.nabla d).ConnectedComponent} {i : Fin 4} :
    i ∈ G.compSupp C ↔ ∃ z : G.fiber d, (G.nabla d).connectedComponentMk z = C ∧ 0 < z.1 i := by
  classical
  unfold compSupp; simp only [mem_filter, mem_univ, true_and]

lemma supp_subset_compSupp {d : ℕ} (z : G.fiber d) :
    supp z.1 ⊆ G.compSupp ((G.nabla d).connectedComponentMk z) := by
  intro i hi; rw [mem_supp] at hi; exact G.mem_compSupp.2 ⟨z, rfl, hi⟩

/-! ### Basic graph facts -/

lemma reachable_of_sharesVar {d : ℕ} {z y : G.fiber d} (h : SharesVar z.1 y.1) :
    (G.nabla d).Reachable z y := by
  by_cases hzy : z = y
  · subst hzy; rfl
  · exact SimpleGraph.Adj.reachable ⟨hzy, h⟩

lemma ncomp_le_one_of_reachable {d : ℕ} (h : ∀ z y : G.fiber d, (G.nabla d).Reachable z y) :
    G.ncomp d ≤ 1 := by
  unfold ncomp
  rw [Fintype.card_le_one_iff_subsingleton]
  exact ⟨SimpleGraph.ConnectedComponent.ind₂ fun v w =>
    SimpleGraph.ConnectedComponent.sound (h v w)⟩

lemma exists_not_reachable {d : ℕ} (h : 2 ≤ G.ncomp d) :
    ∃ z y : G.fiber d, ¬ (G.nabla d).Reachable z y := by
  by_contra hne
  push Not at hne
  have := G.ncomp_le_one_of_reachable hne
  omega

lemma ncomp_eq_zero_iff {d : ℕ} : G.ncomp d = 0 ↔ G.fiber d = ∅ := by
  unfold ncomp
  rw [Fintype.card_eq_zero_iff, ← Finset.isEmpty_coe_sort]
  constructor
  · intro h; exact ⟨fun v => h.false ((G.nabla d).connectedComponentMk v)⟩
  · intro h; infer_instance

lemma ncomp_pos_iff {d : ℕ} : 0 < G.ncomp d ↔ (G.fiber d).Nonempty := by
  rw [Nat.pos_iff_ne_zero, Ne, ncomp_eq_zero_iff, ← Ne, ← Finset.nonempty_iff_ne_empty]

lemma ncomp_zero : G.ncomp 0 = 1 := by
  unfold ncomp
  have : Unique (G.fiber 0) := by
    rw [fiber_zero]; exact ⟨⟨⟨0, by simp⟩⟩, fun ⟨x, hx⟩ => by simp at hx; simp [hx]⟩
  rw [Fintype.card_eq_one_iff]
  exact ⟨(G.nabla 0).connectedComponentMk default, SimpleGraph.ConnectedComponent.ind
    fun v => by rw [Subsingleton.elim v default]⟩

lemma pos_of_two_le_ncomp {d : ℕ} (h : 2 ≤ G.ncomp d) : 0 < d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [ncomp_zero] at h; omega
  · exact hd

/-! ### Lemma 2: component supports and replacement bridges -/

/-- **Lemma 2.1 (vertex form).** Vertices in different components share no variable. -/
lemma not_sharesVar_of_not_reachable {d : ℕ} {z y : G.fiber d}
    (h : ¬ (G.nabla d).Reachable z y) : ¬ SharesVar z.1 y.1 :=
  fun hs => h (G.reachable_of_sharesVar hs)

/-- **Lemma 2.1.** Distinct components of `∇_d` have disjoint supports. -/
lemma compSupp_disjoint {d : ℕ} {C C' : (G.nabla d).ConnectedComponent} (h : C ≠ C') :
    Disjoint (G.compSupp C) (G.compSupp C') := by
  rw [Finset.disjoint_left]
  intro i hi hi'
  obtain ⟨z, rfl, hz⟩ := G.mem_compSupp.1 hi
  obtain ⟨z', rfl, hz'⟩ := G.mem_compSupp.1 hi'
  exact h (SimpleGraph.ConnectedComponent.sound (G.reachable_of_sharesVar ⟨i, hz, hz'⟩))

/-- **Lemma 2.2.** At positive degree every component has nonempty support. -/
lemma compSupp_nonempty {d : ℕ} (hd : 0 < d) (C : (G.nabla d).ConnectedComponent) :
    (G.compSupp C).Nonempty := by
  induction C using SimpleGraph.ConnectedComponent.ind with
  | h z =>
    have hz0 : z.1 ≠ 0 := by
      intro h0; have := (G.mem_fiber.1 z.2); rw [h0, nu_zero] at this; omega
    obtain ⟨i, hi⟩ : ∃ i, z.1 i ≠ 0 := by
      by_contra hc; push Not at hc; exact hz0 (funext hc)
    exact ⟨i, G.mem_compSupp.2 ⟨z, rfl, Nat.pos_of_ne_zero hi⟩⟩

/-- **Lemma 2.3.** If `u ≤ x` and `ν(u) = ν(v)` then `b = x - u + v` has `ν(b) = ν(x)`. -/
lemma nu_replace {u v x : Fin 4 → ℕ} (hux : u ≤ x) (huv : G.nu u = G.nu v) :
    G.nu (x - u + v) = G.nu x := by
  rw [G.nu_add, G.nu_sub hux, huv, add_comm]

/-- **Lemma 2.4.** A factorization `b` of `d` sharing a variable with `z` and with `y` puts
`z` and `y` in the same component. -/
lemma reachable_of_bridge {d : ℕ} {z y : G.fiber d} (b : Fin 4 → ℕ) (hb : G.nu b = d)
    (hz : SharesVar b z.1) (hy : SharesVar b y.1) : (G.nabla d).Reachable z y := by
  let b' : G.fiber d := ⟨b, G.mem_fiber.2 hb⟩
  exact (G.reachable_of_sharesVar (z := b') hz).symm.trans (G.reachable_of_sharesVar hy)

/-- **Lemma 2.4 (as stated).** With `u ≤ x`, `ν(u) = ν(v)`, `ν(x) = d`, if `b = x - u + v`
shares variables with vertices of two components then the components coincide. -/
lemma comp_eq_of_replace {d : ℕ} {u v x : Fin 4 → ℕ} (hux : u ≤ x) (huv : G.nu u = G.nu v)
    (hx : G.nu x = d) {z y : G.fiber d} (hz : SharesVar (x - u + v) z.1)
    (hy : SharesVar (x - u + v) y.1) :
    (G.nabla d).connectedComponentMk z = (G.nabla d).connectedComponentMk y :=
  SimpleGraph.ConnectedComponent.sound
    (G.reachable_of_bridge _ ((G.nu_replace hux huv).trans hx) hz hy)

/-! ### Lemma 0, part A: the finite cutoff -/

/-- Core of Lemma 0A: a factorization with a coordinate exceeding `N = n₃` is connected to
every other factorization of the same degree. -/
lemma reachable_of_coord_gt {d : ℕ} (z y : G.fiber d) {i : Fin 4} (hzi : G.n 3 < z.1 i) :
    (G.nabla d).Reachable z y := by
  have hz := G.mem_fiber.1 z.2
  have hy := G.mem_fiber.1 y.2
  -- some coordinate `j` of `y` is positive
  obtain ⟨j, hj⟩ : ∃ j, 0 < y.1 j := by
    by_contra hc; push Not at hc
    have : y.1 = 0 := funext fun k => Nat.le_zero.1 (hc k)
    rw [this, nu_zero] at hy
    have := G.nu_pos_of_pos (z := z.1) (i := i) (by omega)
    omega
  by_cases hzj : 0 < z.1 j
  · exact G.reachable_of_sharesVar ⟨j, hzj, hj⟩
  have hij : i ≠ j := by rintro rfl; omega
  have hnj := G.n_le_n_three j
  -- the bridge `b = z - nⱼ eᵢ + nᵢ eⱼ`
  have hle : Pi.single i (G.n j) ≤ z.1 := by
    intro k
    by_cases hk : k = i
    · subst hk; simp; omega
    · simp [hk]
  have heq : G.nu (Pi.single i (G.n j)) = G.nu (Pi.single j (G.n i)) := by
    rw [G.nu_single, G.nu_single, mul_comm]
  refine G.reachable_of_bridge (z.1 - Pi.single i (G.n j) + Pi.single j (G.n i))
    ((G.nu_replace hle heq).trans hz) ⟨i, ?_, by omega⟩ ⟨j, ?_, hj⟩
  · simp [hij]; omega
  · simp [hij.symm, G.n_pos i]

/-- **Lemma 0A.** At a contributing degree every coordinate of every factorization is at
most `N = n₃`. -/
lemma coord_le_of_contributes {d : ℕ} (h : G.contributes d) (z : G.fiber d) (i : Fin 4) :
    z.1 i ≤ G.n 3 := by
  by_contra hc
  push Not at hc
  obtain ⟨y, y', hyy'⟩ := G.exists_not_reachable h
  exact hyy' (((G.reachable_of_coord_gt z y hc).symm).trans (G.reachable_of_coord_gt z y' hc))

/-- **Lemma 0A.** Every contributing degree satisfies `d ≤ H`. -/
lemma le_H_of_contributes {d : ℕ} (h : G.contributes d) : d ≤ G.H := by
  obtain ⟨z, -, -⟩ := G.exists_not_reachable h
  rw [← G.mem_fiber.1 z.2, nu, H, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_right _ (G.coord_le_of_contributes h z i)

/-- **Lemma 0A (cutoff form).** Above `H`, `∇_d` has at most one component. -/
lemma ncomp_le_one_of_H_lt {d : ℕ} (h : G.H < d) : G.ncomp d ≤ 1 := by
  by_contra hc
  push Not at hc
  have := G.le_H_of_contributes (d := d) hc
  omega

/-- The bounded definition of `β₁` agrees with any larger cutoff. -/
lemma beta1_eq_sum_of_le {K : ℕ} (hK : G.H ≤ K) :
    G.beta1 = ∑ d ∈ range (K + 1), (G.ncomp d - 1) := by
  unfold beta1
  rw [← Finset.sum_subset (Finset.range_subset_range.2 (by omega : G.H + 1 ≤ K + 1))]
  intro d hd hd'
  simp only [mem_range] at hd hd'
  have := G.ncomp_le_one_of_H_lt (d := d) (by omega)
  omega

end GenData

end SemigroupBetti
