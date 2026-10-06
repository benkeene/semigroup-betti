/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/
module

public import SemigroupBetti.Fiber

/-!
# The algebraic bridge: `μ(I) ≤ β₁`

Write-up `PROOF_B_lean_writeup.md`, §2, Definition 4 and Lemma 0 (parts B–F, in the
"explicit generating set" form).

Let `I = ker (K[X₀,…,X₃] → K[t], Xᵢ ↦ t^{nᵢ})`.  For every degree `d ≤ H` with nonempty
fiber we fix a base component `C₀` of `∇_d` and a representative `rep C` of every component,
and take the binomials `X^{rep C} - X^{rep C₀}`, `C ≠ C₀`.  There are at most
`∑_{d ≤ H} (c_d - 1) = β₁` of them, and they generate `I`:

* every binomial `X^z - X^{z'}` with `ν z = ν z'` lies in their span, by strong induction on
  the degree (an edge of `∇_d` factors as `Xᵢ · (binomial of smaller degree)`; a path is a sum of
  edges; different components are linked through the chosen representatives; above `H` the
  graph is connected by Lemma 0A);
* every element of `I` is a `K`-combination of such binomials (coefficient sums vanish on
  each fiber).

Main results: `GenData.toricKer_eq_span`, `GenData.spanRank_toricKer_le_beta1`.
Also `GenData.ofChallenge`: the conversion from the hypotheses of `Challenge.lean`.
-/

@[expose] public section

namespace SemigroupBetti

open Finset MvPolynomial

section Mono

variable (K : Type*) [Field K]

/-- The monomial `X^z` for `z : Fin 4 → ℕ`. -/
noncomputable def mono (z : Fin 4 → ℕ) : MvPolynomial (Fin 4) K :=
  monomial (Finsupp.equivFunOnFinite.symm z) 1

/-- The toric map `K[X₀,…,X₃] → K[t]`, `Xᵢ ↦ t^{nᵢ}`. -/
noncomputable def toricMap (n : Fin 4 → ℕ) : MvPolynomial (Fin 4) K →ₐ[K] Polynomial K :=
  aeval (fun i => (Polynomial.X : Polynomial K) ^ n i)

variable {K}

lemma mono_coe (s : Fin 4 →₀ ℕ) : mono K ⇑s = monomial s 1 := by
  simp [mono]

lemma toricMap_monomial (n : Fin 4 → ℕ) (s : Fin 4 →₀ ℕ) (c : K) :
    toricMap K n (monomial s c) = Polynomial.C c * Polynomial.X ^ (∑ i, s i * n i) := by
  rw [toricMap, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp_rw [← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum, Polynomial.algebraMap_eq]
  congr 2
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma X_mul_mono (i : Fin 4) (u : Fin 4 → ℕ) :
    (X i : MvPolynomial (Fin 4) K) * mono K u = mono K (u + Pi.single i 1) := by
  rw [mono, mono, X, monomial_mul_monomial, one_mul]
  have : Finsupp.single i 1 + Finsupp.equivFunOnFinite.symm u =
      Finsupp.equivFunOnFinite.symm (u + Pi.single i 1) := by
    refine Finsupp.ext fun j => ?_
    by_cases h : j = i
    · subst h; simp [add_comm]
    · simp [h]
  rw [this]

end Mono

namespace GenData

variable (G : GenData) (K : Type*) [Field K]

lemma toricMap_mono (z : Fin 4 → ℕ) : toricMap K G.n (mono K z) = Polynomial.X ^ G.nu z := by
  rw [mono, toricMap_monomial]; simp [nu]

/-- The toric ideal, written exactly as in `Challenge.lean` (`SemigroupBetti.toricIdeal K G.n`
unfolds to this). -/
noncomputable abbrev toricKer : Ideal (MvPolynomial (Fin 4) K) :=
  RingHom.ker (MvPolynomial.aeval (fun i => (Polynomial.X : Polynomial K) ^ G.n i)).toRingHom

lemma mem_toricKer {f : MvPolynomial (Fin 4) K} : f ∈ G.toricKer K ↔ toricMap K G.n f = 0 :=
  RingHom.mem_ker

lemma mono_sub_mem_toricKer {z z' : Fin 4 → ℕ} (h : G.nu z = G.nu z') :
    mono K z - mono K z' ∈ G.toricKer K := by
  rw [mem_toricKer, map_sub, toricMap_mono, toricMap_mono, h, sub_self]

/-! ### Representatives, base components, and the generating binomials -/

/-- A chosen representative factorization of a component of `∇_d`. -/
noncomputable def rep {d : ℕ} (C : (G.nabla d).ConnectedComponent) : Fin 4 → ℕ :=
  (Quot.out C : G.fiber d).1

lemma nu_rep {d : ℕ} (C : (G.nabla d).ConnectedComponent) : G.nu (G.rep C) = d :=
  G.mem_fiber.1 (Quot.out C).2

lemma rep_mk {d : ℕ} (C : (G.nabla d).ConnectedComponent) :
    (G.nabla d).connectedComponentMk (⟨G.rep C, (Quot.out C).2⟩ : G.fiber d) = C :=
  Quot.out_eq C

open Classical in
/-- The chosen binomials of degree `d`: `X^{rep C} - X^{rep C₀}` for `C ≠ C₀`, where `C₀` is
a fixed base component (none if the fiber is empty). -/
noncomputable def genSet (d : ℕ) : Finset (MvPolynomial (Fin 4) K) :=
  if h : Nonempty (G.nabla d).ConnectedComponent then
    (univ.erase (Classical.choice h)).image
      (fun C => mono K (G.rep C) - mono K (G.rep (Classical.choice h)))
  else ∅

open Classical in
/-- All chosen binomials, over the degrees `d ≤ H`. -/
noncomputable def binomGens : Finset (MvPolynomial (Fin 4) K) :=
  (range (G.H + 1)).biUnion (G.genSet K)

lemma card_genSet_le (d : ℕ) : #(G.genSet K d) ≤ G.ncomp d - 1 := by
  classical
  unfold genSet
  split_ifs with h
  · refine (card_image_le).trans ?_
    rw [card_erase_of_mem (mem_univ _), card_univ, ncomp]
  · simp

lemma card_binomGens_le : #(G.binomGens K) ≤ G.beta1 := by
  classical
  exact (card_biUnion_le).trans (sum_le_sum fun d _ => G.card_genSet_le K d)

lemma binomGens_subset_toricKer : (G.binomGens K : Set (MvPolynomial (Fin 4) K)) ⊆ G.toricKer K := by
  classical
  intro p hp
  simp only [binomGens, coe_biUnion, coe_range, Set.mem_iUnion, mem_coe] at hp
  obtain ⟨d, -, hp⟩ := hp
  unfold genSet at hp
  split_ifs at hp with h
  · obtain ⟨C, -, rfl⟩ := mem_image.1 hp
    apply G.mono_sub_mem_toricKer
    rw [G.nu_rep, G.nu_rep]
  · simp at hp

/-! ### Every equal-degree binomial lies in the span -/

/-- Edge step (write-up Lemma 0C): if `z, z'` of degree `d` share a variable `i`, then
`X^z - X^{z'} = Xᵢ (X^{z-eᵢ} - X^{z'-eᵢ})`, and the inner binomial has degree `d - nᵢ < d`. -/
lemma sub_mem_of_sharesVar {J : Ideal (MvPolynomial (Fin 4) K)} {d : ℕ}
    (IH : ∀ e < d, ∀ z z' : Fin 4 → ℕ, G.nu z = e → G.nu z' = e → mono K z - mono K z' ∈ J)
    {z z' : Fin 4 → ℕ} (hz : G.nu z = d) (hz' : G.nu z' = d) (h : SharesVar z z') :
    mono K z - mono K z' ∈ J := by
  obtain ⟨i, hi, hi'⟩ := h
  have key : ∀ y : Fin 4 → ℕ, 0 < y i → y = (y - Pi.single i 1) + Pi.single i 1 := by
    intro y hy; ext j
    by_cases hj : j = i
    · subst hj; simp; omega
    · simp [hj]
  have hdeg : ∀ y : Fin 4 → ℕ, 0 < y i → G.nu y = G.nu (y - Pi.single i 1) + G.n i := by
    intro y hy
    conv_lhs => rw [key y hy]
    rw [G.nu_add, G.nu_single, one_mul]
  rw [key z hi, key z' hi', ← X_mul_mono, ← X_mul_mono, ← mul_sub]
  refine J.mul_mem_left _ (IH (G.nu (z - Pi.single i 1)) ?_ _ _ rfl ?_)
  · have := hdeg z hi; have := G.n_pos i; omega
  · have := hdeg z hi; have := hdeg z' hi'; omega

/-- Path step (write-up Lemma 0D). -/
lemma sub_mem_of_reachable {J : Ideal (MvPolynomial (Fin 4) K)} {d : ℕ}
    (IH : ∀ e < d, ∀ z z' : Fin 4 → ℕ, G.nu z = e → G.nu z' = e → mono K z - mono K z' ∈ J)
    {x y : G.fiber d} (h : (G.nabla d).Reachable x y) : mono K x.1 - mono K y.1 ∈ J := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => simp
  | @cons u v w hadj _ ih =>
    rw [← sub_add_sub_cancel _ (mono K v.1) _]
    exact add_mem (G.sub_mem_of_sharesVar K IH (G.mem_fiber.1 u.2) (G.mem_fiber.1 v.2) hadj.2) ih

/-- Base-component step (write-up Lemma 0D/0F): the chosen binomials link any two
representatives at a degree `d ≤ H`. -/
lemma rep_sub_rep_mem {d : ℕ} (hd : d ≤ G.H) (C C' : (G.nabla d).ConnectedComponent) :
    mono K (G.rep C) - mono K (G.rep C') ∈ Ideal.span (G.binomGens K : Set _) := by
  classical
  have h : Nonempty (G.nabla d).ConnectedComponent := ⟨C⟩
  have base : ∀ D : (G.nabla d).ConnectedComponent, mono K (G.rep D) - mono K (G.rep (Classical.choice h)) ∈
      Ideal.span (G.binomGens K : Set _) := by
    intro D
    by_cases hD : D = Classical.choice h
    · rw [hD, sub_self]; exact zero_mem _
    · apply Ideal.subset_span
      simp only [binomGens, coe_biUnion, coe_range, Set.mem_iUnion, mem_coe, Set.mem_Iio]
      refine ⟨d, by omega, ?_⟩
      unfold genSet
      simp only [h, ↓reduceDIte]
      exact mem_image.2 ⟨D, mem_erase.2 ⟨hD, mem_univ _⟩, rfl⟩
  rw [← sub_sub_sub_cancel_right _ _ (mono K (G.rep (Classical.choice h)))]
  exact sub_mem (base C) (base C')

/-- **Lemma 0 (B–F), binomial form.** Every binomial `X^z - X^{z'}` with `ν z = ν z'` lies in
the ideal spanned by the chosen binomials. -/
lemma mono_sub_mem_span (d : ℕ) : ∀ z z' : Fin 4 → ℕ, G.nu z = d → G.nu z' = d →
    mono K z - mono K z' ∈ Ideal.span (G.binomGens K : Set _) := by
  induction d using Nat.strong_induction_on with
  | _ d IH =>
  intro z z' hz hz'
  obtain ⟨x, hx⟩ : ∃ x : G.fiber d, x.1 = z := ⟨⟨z, G.mem_fiber.2 hz⟩, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : G.fiber d, y.1 = z' := ⟨⟨z', G.mem_fiber.2 hz'⟩, rfl⟩
  subst hx hy
  by_cases hr : (G.nabla d).Reachable x y
  · exact G.sub_mem_of_reachable K IH hr
  · set Cx := (G.nabla d).connectedComponentMk x
    set Cy := (G.nabla d).connectedComponentMk y
    have hne : Cx ≠ Cy := fun h => hr (SimpleGraph.ConnectedComponent.exact h)
    have hd : d ≤ G.H := G.le_H_of_contributes (by
      unfold contributes ncomp
      exact Fintype.one_lt_card_iff.2 ⟨Cx, Cy, hne⟩)
    have h1 : mono K x.1 - mono K (G.rep Cx) ∈ Ideal.span (G.binomGens K : Set _) :=
      G.sub_mem_of_reachable K IH (x := x) (y := ⟨G.rep Cx, (Quot.out Cx).2⟩)
        (SimpleGraph.ConnectedComponent.exact (G.rep_mk Cx).symm)
    have h2 : mono K (G.rep Cy) - mono K y.1 ∈ Ideal.span (G.binomGens K : Set _) :=
      G.sub_mem_of_reachable K IH (x := ⟨G.rep Cy, (Quot.out Cy).2⟩) (y := y)
        (SimpleGraph.ConnectedComponent.exact (G.rep_mk Cy))
    have h3 := G.rep_sub_rep_mem K hd Cx Cy
    have : mono K x.1 - mono K y.1 = (mono K x.1 - mono K (G.rep Cx)) +
        (mono K (G.rep Cx) - mono K (G.rep Cy)) + (mono K (G.rep Cy) - mono K y.1) := by ring
    rw [this]
    exact add_mem (add_mem h1 h3) h2

/-! ### The kernel is spanned by equal-degree binomials -/

open Classical in
/-- A chosen factorization of `d` (junk `0` when the fiber is empty). -/
noncomputable def root (d : ℕ) : Fin 4 → ℕ :=
  if h : (G.fiber d).Nonempty then h.choose else 0

lemma nu_root (z : Fin 4 → ℕ) : G.nu (G.root (G.nu z)) = G.nu z := by
  have h : (G.fiber (G.nu z)).Nonempty := ⟨z, G.mem_fiber.2 rfl⟩
  rw [root]; simp only [h, ↓reduceDIte]
  exact G.mem_fiber.1 h.choose_spec

/-- **Lemma 0B.** An element of the kernel has zero coefficient sum on every fiber. -/
lemma coeff_sum_eq_zero {f : MvPolynomial (Fin 4) K} (hf : f ∈ G.toricKer K) (d : ℕ) :
    ∑ s ∈ f.support.filter (fun s : Fin 4 →₀ ℕ => G.nu ⇑s = d), f.coeff s = 0 := by
  have hφ := (G.mem_toricKer K).1 hf
  rw [f.as_sum, map_sum] at hφ
  have := congrArg (fun p : Polynomial K => p.coeff d) hφ
  simp only [toricMap_monomial, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_zero] at this
  rw [Finset.sum_filter]
  simpa [nu, eq_comm] using this

lemma toricKer_le_span : G.toricKer K ≤ Ideal.span (G.binomGens K : Set _) := by
  intro f hf
  set J := Ideal.span (G.binomGens K : Set (MvPolynomial (Fin 4) K))
  have hsplit : f = ∑ s ∈ f.support, C (f.coeff s) * (mono K s - mono K (G.root (G.nu s))) +
      ∑ s ∈ f.support, C (f.coeff s) * mono K (G.root (G.nu s)) := by
    rw [← sum_add_distrib]
    simp_rw [← mul_add, sub_add_cancel, mono_coe, C_mul_monomial, mul_one]
    exact f.as_sum
  have hzero : ∑ s ∈ f.support, C (f.coeff s) * mono K (G.root (G.nu s)) = 0 := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun s : Fin 4 →₀ ℕ => G.nu s)
      (t := f.support.image (fun s : Fin 4 →₀ ℕ => G.nu s)) (fun s hs => mem_image_of_mem _ hs)]
    refine Finset.sum_eq_zero fun d _ => ?_
    have : ∀ s ∈ f.support.filter (fun s : Fin 4 →₀ ℕ => G.nu ⇑s = d),
        C (f.coeff s) * mono K (G.root (G.nu s)) = C (f.coeff s) * mono K (G.root d) := by
      intro s hs; rw [(mem_filter.1 hs).2]
    rw [Finset.sum_congr rfl this, ← Finset.sum_mul, ← map_sum, G.coeff_sum_eq_zero K hf d,
      map_zero, zero_mul]
  rw [hsplit, hzero, add_zero]
  exact J.sum_mem fun s _ => J.mul_mem_left _
    (G.mono_sub_mem_span K (G.nu s) s _ rfl (G.nu_root s))

/-! ### Main theorems -/

/-- **Lemma 0F.** The toric ideal is generated by the chosen binomials. -/
theorem toricKer_eq_span : G.toricKer K = Ideal.span (G.binomGens K : Set _) :=
  le_antisymm (G.toricKer_le_span K) (Ideal.span_le.2 (G.binomGens_subset_toricKer K))

/-- **Bridge (inequality half of Lemma 0).** `μ(I) ≤ β₁`, with `μ` = `Submodule.spanRank`. -/
theorem spanRank_toricKer_le_beta1 :
    (RingHom.ker (MvPolynomial.aeval (R := K)
      (fun i => (Polynomial.X : Polynomial K) ^ G.n i)).toRingHom).spanRank ≤
      (G.beta1 : Cardinal) := by
  change (G.toricKer K).spanRank ≤ _
  rw [G.toricKer_eq_span K]
  calc (Ideal.span (G.binomGens K : Set (MvPolynomial (Fin 4) K))).spanRank
      ≤ Cardinal.mk (G.binomGens K : Set (MvPolynomial (Fin 4) K)) :=
        Submodule.spanRank_span_le_card _
    _ = (#(G.binomGens K) : Cardinal) := Cardinal.mk_coe_finset
    _ ≤ (G.beta1 : Cardinal) := Nat.cast_le.2 (G.card_binomGens_le K)

/-- The bridge for an arbitrary generator vector `n` equal to `G.n` (avoids rewriting `G.n`
under the dependent `G.beta1`). With `n` and `toricIdeal` from `Challenge.lean` this reads
`(toricIdeal K n).spanRank ≤ G.beta1` (definitional unfolding). -/
theorem spanRank_le_beta1_of_n_eq {n : Fin 4 → ℕ} (hn : G.n = n) :
    (RingHom.ker (MvPolynomial.aeval (R := K)
      (fun i => (Polynomial.X : Polynomial K) ^ n i)).toRingHom).spanRank ≤
      (G.beta1 : Cardinal) := by
  subst hn; exact G.spanRank_toricKer_le_beta1 K

end GenData

/-! ### From the hypotheses of `Challenge.lean` to `GenData` -/

namespace GenData

/-- Build `GenData` from the hypotheses of the statements of record (`Challenge.lean`):
`0 < n 0`, `StrictMono n`, `Finset.univ.gcd n = 1`, and minimal generation (the body of
`SemigroupBetti.MinimallyGenerates n`). -/
def ofChallenge (n : Fin 4 → ℕ) (hpos : 0 < n 0) (hmono : StrictMono n)
    (hgcd : Finset.univ.gcd n = 1)
    (hmin : ∀ i : Fin 4, n i ∉ AddSubmonoid.closure (n '' {j | j ≠ i})) : GenData :=
  have h01 : n 0 < n 1 := hmono (by decide)
  have h12 : n 1 < n 2 := hmono (by decide)
  have h23 : n 2 < n 3 := hmono (by decide)
  have hgens : gens (n 0) (n 1 - n 0) (n 2 - n 0) (n 3 - n 0) = n := by
    funext i; fin_cases i <;> simp [gens] <;> omega
  { m := n 0
    a := n 1 - n 0
    b := n 2 - n 0
    w := n 3 - n 0
    m_pos := hpos
    a_pos := by omega
    a_lt_b := by omega
    b_lt_w := by omega
    gcd_eq_one := by
      set g := Nat.gcd (n 0) (Nat.gcd (n 1 - n 0) (Nat.gcd (n 2 - n 0) (n 3 - n 0)))
      have h0 : g ∣ n 0 := Nat.gcd_dvd_left _ _
      have ha : g ∣ n 1 - n 0 := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
      have hb : g ∣ n 2 - n 0 :=
        (Nat.gcd_dvd_right _ _).trans ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _))
      have hw : g ∣ n 3 - n 0 :=
        (Nat.gcd_dvd_right _ _).trans ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _))
      have hall : ∀ i ∈ (Finset.univ : Finset (Fin 4)), g ∣ n i := by
        intro i _
        fin_cases i
        · exact h0
        · have : n 1 = n 0 + (n 1 - n 0) := by omega
          simpa [← this] using Nat.dvd_add h0 ha
        · have : n 2 = n 0 + (n 2 - n 0) := by omega
          simpa [← this] using Nat.dvd_add h0 hb
        · have : n 3 = n 0 + (n 3 - n 0) := by omega
          simpa [← this] using Nat.dvd_add h0 hw
      have := Finset.dvd_gcd hall
      rw [hgcd] at this
      exact Nat.dvd_one.1 this
    minimal := by
      intro i z hzi heq
      rw [hgens] at heq
      apply hmin i
      rw [← heq]
      refine AddSubmonoid.sum_mem _ fun j _ => ?_
      by_cases hj : j = i
      · subst hj; rw [hzi, zero_mul]; exact zero_mem _
      · rw [← smul_eq_mul]
        exact AddSubmonoid.nsmul_mem _ (AddSubmonoid.subset_closure (Set.mem_image_of_mem n (show j ∈ {j | j ≠ i} from hj))) _ }

section
variable (n : Fin 4 → ℕ) (hpos : 0 < n 0) (hmono : StrictMono n)
  (hgcd : Finset.univ.gcd n = 1)
  (hmin : ∀ i : Fin 4, n i ∉ AddSubmonoid.closure (n '' {j | j ≠ i}))

lemma ofChallenge_n : (ofChallenge n hpos hmono hgcd hmin).n = n := by
  have h01 : n 0 < n 1 := hmono (by decide)
  have h12 : n 1 < n 2 := hmono (by decide)
  have h23 : n 2 < n 3 := hmono (by decide)
  funext i; fin_cases i <;> simp [GenData.n, gens, ofChallenge] <;> omega

lemma ofChallenge_w : (ofChallenge n hpos hmono hgcd hmin).w = n 3 - n 0 := rfl

/-- `W = w / gcd(a, b, w)` is the `normalizedWidth` of `Challenge.lean` (unfolded). -/
lemma ofChallenge_W : (ofChallenge n hpos hmono hgcd hmin).W =
    (n 3 - n 0) / Nat.gcd (n 1 - n 0) (Nat.gcd (n 2 - n 0) (n 3 - n 0)) := rfl

end

end GenData

end SemigroupBetti
