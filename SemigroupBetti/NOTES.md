# SemigroupBetti development notes (Stage 1: Definitions 1–6, Lemmas 0A, 1–4)

Source: `agents/shared/claim_0003/PROOF_B_lean_writeup.md`. Everything lives in namespace
`SemigroupBetti.GenData` with `(G : GenData)` explicit. Sorry count: **0**. Axioms of the main
lemmas: `propext, Classical.choice, Quot.sound` only.

Build: `lake build` (the lake-free helper scripts `build_direct.sh`/`check.sh`/`mk.sh` used during
development were removed on 2026-10-06 when the project moved to Lean v4.35.0-rc4 and the module system).

## Defs.lean — Definitions 1–2, Lemma 1
- `gens m a b w = ![m, m+a, m+b, m+w]`; `structure GenData` (fields `m a b w`, `m_pos`, `a_pos`,
  `a_lt_b`, `b_lt_w`, `gcd_eq_one : gcd m (gcd a (gcd b w)) = 1`,
  `minimal : ∀ i z, z i = 0 → ∑ j, z j * gens m a b w j ≠ gens m a b w i`).
- `G.n`, `G.g`, `G.A`, `G.B`, `G.W`, `G.nu`, `G.omega`; top-level `len`, `supp`, `SharesVar`
  (decidable). `e_i`-multiples are written `Pi.single i k`.
- `nu_eq_len_add_omega : G.nu z = G.m * len z + G.omega z`; `n_strictMono`, `n_mono`,
  `m_le_n`, `n_pos`, `n_le_n_three`; `nu_add`, `nu_single`, `nu_sub (h : x ≤ y) :
  ν y = ν x + ν (y - x)`, `single_le_nu`, `m_mul_le_nu`, `nu_eq_zero_iff`, `nu_pos_of_pos`.
- Lemma 1: `g_dvd_a/b/w`, `g_pos`, `one_le_g`, `a_eq : a = g*A` (and `b_eq`, `w_eq`), `A_pos`,
  `one_le_A`, `A_lt_B`, `B_lt_W`, `two_le_B`, `three_le_W`, `two_le_W_sub_A : 2 ≤ W - A`,
  `gcd_ABW : gcd A (gcd B W) = 1`, `gcd_m_g : gcd m g = 1`, `W_le_w`, `n_eq_normalized`.

## Fiber.lean — Definition 3, Lemma 0A, Lemma 2
- `fiber d` = filter of `piFinset (fun _ => range (d / m + 1))` by `ν z = d`;
  `mem_fiber : z ∈ G.fiber d ↔ G.nu z = d`; `fiber_zero : G.fiber 0 = {0}`.
- `nabla d : SimpleGraph (G.fiber d)`, `Adj z z' ↔ z ≠ z' ∧ SharesVar z.1 z'.1` (`nabla_adj`).
- `ncomp d := Fintype.card (G.nabla d).ConnectedComponent` (computable Mathlib instance from
  decidable reachability). `contributes d := 2 ≤ ncomp d` (implies `d ∈ S`).
- `H := n 3 * ∑ i, n i`; `beta1 := ∑ d ∈ range (H+1), (ncomp d - 1)`.
- `compSupp C` (noncomputable, classical) = union of vertex supports; `mem_compSupp`,
  `supp_subset_compSupp`.
- Graph helpers: `reachable_of_sharesVar`, `ncomp_le_one_of_reachable`, `exists_not_reachable`,
  `ncomp_eq_zero_iff : ncomp d = 0 ↔ fiber d = ∅`, `ncomp_pos_iff`, `ncomp_zero : ncomp 0 = 1`,
  `pos_of_two_le_ncomp`.
- Lemma 2: `not_sharesVar_of_not_reachable` (2.1 vertex form), `compSupp_disjoint (C ≠ C')`
  (2.1), `compSupp_nonempty (0 < d)` (2.2), `nu_replace (u ≤ x) (ν u = ν v) : ν (x - u + v) = ν x`
  (2.3), `reachable_of_bridge` and `comp_eq_of_replace` (2.4).
- Lemma 0A: `reachable_of_coord_gt` (core), `coord_le_of_contributes : z.1 i ≤ n 3`,
  `le_H_of_contributes : d ≤ H`, `ncomp_le_one_of_H_lt : H < d → ncomp d ≤ 1`,
  `beta1_eq_sum_of_le` (any larger cutoff gives the same sum).

## Critical.lean — Definition 5, Lemma 3, Definition 6, Lemma 4
- `IsCritCand i k := 1 ≤ k ∧ ∃ y ∈ fiber (k * n i), y ≠ Pi.single i k` (decidable; the write-up's
  `∃ y ∈ ℕ⁴` is recovered by `isCritCand_iff`); `crit i := Nat.find (crit_exists i)`.
- Lemma 3: `one_le_crit`, `crit_le_n (j ≠ i)`, `crit_spec`, `exists_alt` (3.1);
  `alt_coord_eq_zero` (3.2); `critVertex`, `critVertex_not_adj`, `eq_critVertex_of_reachable`,
  `compSupp_critVertex = {i}` (3.3); `singleton_comp_vertex`, `degree_eq_of_singleton_comp`,
  `comp_eq_critVertex` (3.4); `two_le_crit` (3.5, uses `minimal`).
- Definition 6: `HasSingletonComp d`, `singletonDegrees` (filter of `range (H+1)`),
  `mem_singletonDegrees`, `mem_singletonDegrees_of`, `sigma`, `critIndices d`.
- Lemma 4: `ncomp_sub_one_le : ncomp d - 1 ≤ #(critIndices d)` and `sigma_le_four : sigma ≤ 4`.

## Deviations from the write-up
- `𝓑`, `𝓢` are bounded by `range (H+1)`; Lemma 0A (`le_H_of_contributes`) shows nothing is lost.
- Lemma 4 counting is organized as `c_d - 1 ≤ r_d ≤ #{i : cᵢ nᵢ = d}` per degree and then
  `∑_{d∈𝓢} #{i : cᵢnᵢ = d} ≤ 4` by fiberwise counting, instead of an injection from the sigma type
  `{(D,C)} → Fin 4`. `r_d` is not a separate definition (it is `#K1` inside the proof); `#K1` is
  bounded via the disjoint union of singleton supports (Lemma 2.1) landing in `critIndices d`
  (Lemma 3.4).
- Lemma 0A cutoff form proved as `H < d → ncomp d ≤ 1`, plus the write-up's form `d ≤ H` for
  contributing `d` and the coordinate bound `zᵢ ≤ N`.
- Lemma 3.4 is given in a vertex form (every vertex of the component is `cᵢ eᵢ` and `d = cᵢnᵢ`)
  and a component form at degree `cᵢ nᵢ` (avoids casting between fiber types).


## Bridge.lean — Definition 4, Lemma 0 (B–F): `μ(I) ≤ β₁` (inequality half)
Sorry count: **0**. Axioms: `propext, Classical.choice, Quot.sound`. Imports only `SemigroupBetti.Fiber`
(not `Challenge`); the ideal is written out exactly as `SemigroupBetti.toricIdeal K n` unfolds.
- `mono K z := monomial (Finsupp.equivFunOnFinite.symm z) 1` (the monomial `X^z`, `z : Fin 4 → ℕ`);
  `toricMap K n := aeval (fun i => X ^ n i)`; `mono_coe`, `toricMap_monomial`, `X_mul_mono`,
  `GenData.toricMap_mono : toricMap K G.n (mono K z) = X ^ G.nu z`.
- `GenData.toricKer K` (abbrev) `= RingHom.ker (aeval (fun i => X ^ G.n i)).toRingHom`; `mem_toricKer`,
  `mono_sub_mem_toricKer (ν z = ν z')`.
- `rep C := (Quot.out C).1` (component representative), `nu_rep`, `rep_mk`.
- `genSet K d` = `{X^{rep C} - X^{rep C₀} : C ≠ C₀}` with `C₀ = Classical.choice` (empty if no component);
  `binomGens K = (range (H+1)).biUnion genSet`; `card_genSet_le : #genSet d ≤ ncomp d - 1`,
  `card_binomGens_le : #binomGens ≤ beta1`, `binomGens_subset_toricKer`.
- Lemma 0C/0D in binomial form: `sub_mem_of_sharesVar` (edge = `Xᵢ ·` lower-degree binomial),
  `sub_mem_of_reachable` (walk induction), `rep_sub_rep_mem (d ≤ H)`, and
  `mono_sub_mem_span d : ν z = d → ν z' = d → X^z - X^{z'} ∈ span binomGens` (strong induction on `d`;
  non-reachable pairs force `contributes d`, hence `d ≤ H` by `le_H_of_contributes`).
- Lemma 0B: `root d` (chosen factorization), `nu_root`, `coeff_sum_eq_zero` (kernel elements have zero
  coefficient sum on each fiber), `toricKer_le_span` (`f = ∑ c_s (X^s - X^{root ν s}) + 0`).
- **Main:** `GenData.toricKer_eq_span : toricKer K = Ideal.span binomGens`;
  `GenData.spanRank_toricKer_le_beta1 : (RingHom.ker (aeval (R := K) (fun i => X ^ G.n i)).toRingHom).spanRank ≤ G.beta1`;
  `GenData.spanRank_le_beta1_of_n_eq (hn : G.n = n)` — same for any `n = G.n` (use this in Solution.lean;
  `rw [ofChallenge_n]` fails because `beta1` depends on `G`).
- `GenData.ofChallenge n hpos hmono hgcd hmin : GenData` (hypotheses exactly as in Challenge.lean; `hmin`
  is the body of `MinimallyGenerates n`, so `MinimallyGenerates n` is accepted definitionally) with
  `ofChallenge_n : G.n = n`, `ofChallenge_w : G.w = n 3 - n 0` (rfl),
  `ofChallenge_W : G.W = (n 3 - n 0) / gcd (n 1 - n 0) (gcd (n 2 - n 0) (n 3 - n 0))` (rfl; this is
  `normalizedWidth n` by `rfl`, checked in a scratch file importing Challenge).
- Mathlib facts used: `MvPolynomial.aeval_monomial`, `Finsupp.prod_fintype`, `Finset.prod_pow_eq_pow_sum`,
  `MvPolynomial.monomial_mul`, `C_mul_monomial`, `as_sum`, `Polynomial.finsetSum_coeff`,
  `Polynomial.coeff_C_mul_X_pow`, `Finset.sum_fiberwise_of_maps_to`, `SimpleGraph.ConnectedComponent.exact`,
  `Quot.out_eq`, `Fintype.one_lt_card_iff`, `Submodule.spanRank_span_le_card`, `Cardinal.mk_coe_finset`,
  `Finset.card_biUnion_le`, `Finset.dvd_gcd`, `AddSubmonoid.nsmul_mem`/`sum_mem`/`subset_closure`.
- Deviation: no graded-module or quotient `I/𝔪I` is built; Lemma 0F is done as "explicit generating set"
  by strong induction on the degree directly on binomials, which only needs 0B and the edge factorization.
- TODO(bridge, optional): the reverse inequality `beta1 ≤ spanRank` (Lemma 0E/0G). Not needed for the
  Challenge statements. Route if wanted: component-sum map `Φ : R →ₗ[K] (Σ d ≤ H, components) → K`;
  `Φ` kills `Xᵢ·g` for `g ∈ I` (the shifted vertices `u + eᵢ` all share `i`, so lie in one component,
  and the fiber sum of `g` is 0); then for a finite generating set `s`, `Φ(I) ⊆ span_K Φ(s)`
  (`p = p(0) + (p - p(0))`, `p - p(0) ∈ 𝔪`), while `Φ(binomGens)` is linearly independent
  (`δ_C - δ_{C₀}`), giving `beta1 ≤ #s`; infinite `s` are trivial.

# Stage 2: Definitions 7–8, Lemmas 5–13

Files: `Partition.lean`, `Identities.lean`, `Antichain.lean`, `Arith.lean` (no edits to
Defs/Fiber/Critical). Sorry count in these files: **0**; `beta1_le_two_W_of_ne` uses only
`propext, Classical.choice, Quot.sound`.

## Partition.lean — Lemma 5, Definition 7, Lemma 6, Lemma 7
- `reachable_induction` (top level): propagate a predicate along a reachability path.
- `IsSplit d K := ∃ C C', C ≠ C' ∧ compSupp C = K ∧ compSupp C' = Kᶜ`; `IsSplit.compl`;
  `comp_eq_of_mem`.
- `no_bridge`: if `d` splits along `K`, `z` (ν = d) positive at some `i ∈ K`, `y` (ν = d) positive at
  some `j ∉ K`, then no `b` with `ν b = d` shares a variable with both (Lemma 2 + split).
- Lemma 5: `exists_full_vertex` (component with support `{i,j}` contains a vertex positive at
  both), `exists_supp_eq`, and
  `lemma5 : contributes d → ¬ HasSingletonComp d →
     ncomp d = 2 ∧ (IsSplit d {0,1} ∨ IsSplit d {0,2} ∨ IsSplit d {0,3})`.
- Definition 7: `fam K` = filter of `range (H+1)` by `contributes ∧ ¬HasSingletonComp ∧ IsSplit d K`;
  `famP = fam {0,1}`, `famQ = fam {0,2}`, `famE = fam {0,3}`; `P Q E` their cards; `mem_fam`.
  Selection: `sel d K` = `Classical.choose` of `∃ z, ν z = d ∧ supp z = K` (else `0`); `sel_spec`,
  `sel_of_split` (ν = d, supp = K when `IsSplit d K`, `#K = 2`), `sel_pos`, `sel_eq_zero`.
  Since any factorization with support exactly `K` lies in the `K`-component, the choice need not
  name the component.
- `no_replace`: Lemma 2 replacement applied to selected vectors (`U ≤ sel d K`, `ν U = ν V`,
  `U k < sel d K k`, `j ∉ K`, `0 < V j` ⟹ False). Used for Lemmas 9 and 12.
- Lemma 6: `isSplit_exclusive`, `beta1_eq : beta1 = sigma + P + Q + E`,
  `ncomp_eq_two_of_mem_fam`.
- Lemma 7: `sel_antichain (#K = 2) (IsSplit d K) (IsSplit d' K) (d ≠ d') : ¬ sel d K ≤ sel d' K`
  (stated for any pair side `K`; the complementary side is `Kᶜ`).

## Identities.lean — Definition 8, Lemma 8, Lemma 9
- `s = A`, `t = W - B`, `dg = gcd s t` (write-up's lowercase `d`), `p = t / dg`, `q = s / dg`,
  `R = min B (W - A)`. Facts: `s_pos t_pos dg_pos p_pos q_pos dg_mul_p dg_mul_q dg_mul_p_add_q
  p_add_q_eq p_add_q_le W_eq_B_add_t R_eq (R = W - max s t) two_le_R p_mul_A (p A = q t)`.
- Lemma 8: vectors `U1 V1 U2 V2 U3 V3` (as `![…]`); `identity1/2/3 : ν U = ν V ∧ len U = len V ∧
  len U = B / W - A / p + q`. Helpers `nu_vec`, `len_vec`.
- Lemma 9: `sel_one_bounds (IsSplit d K) (#K = 2) (1 ∈ K) : 1 ≤ sel d K 1 ∧ sel d K 1 ≤ B - 1`,
  `sel_two_bounds (… 2 ∈ K) : 1 ≤ sel d K 2 ∧ sel d K 2 ≤ W - A - 1`. The six table rows are
  handled uniformly over the side `K` (a `decide` over all 2-subsets of `Fin 4` supplies the kept
  index and the gained index), instead of six explicit cases.

## Antichain.lean — Lemmas 10–12
- Lemma 11 (top level): `IsPairAntichain T` (∀ x y ∈ T, x ≤ y coordinatewise → x = y);
  `fst_inj`, `snd_inj`, `rank_le : #{y ∈ T | y.1 ≤ x.1} ≤ x.1`,
  `corank_le : x ∈ T → #{y ∈ T | x.1 ≤ y.1} ≤ x.2`,
  `exists_rank : 1 ≤ r ≤ #T → ∃ x ∈ T, r ≤ x.1 ∧ #T + 1 - r ≤ x.2`.
  Reformulation: the sorted enumeration is replaced by ranks (`rank x = #{y | y.1 ≤ x.1}`); the
  rank map `T → [1,#T]` is shown bijective, and the `r`-th member's bounds `u_r ≥ r`,
  `v_r ≥ k+1-r` are proved directly by injecting into `Icc` (no list induction needed).
- Lemma 10: `sel_coord_injOn`, `card_le_of_coord`, `isSplit_of_mem_fam`, `P_le : P ≤ R - 1`,
  `Q_le : Q ≤ R - 1`.
- Lemma 12: `isSplit12_of_mem_famE`, `not_dominates_pq` (exclusion step), `pairsE` (image of `ℰ`
  under `d ↦ (u, v)` of the interior vector), `sel12_le_iff`, `pairsE_injOn`, `card_pairsE`,
  `pairsE_antichain`, `pairsE_pos`, `E_le : E ≤ p + q - 1`.

## Arith.lean — Lemma 13
- `beta1_le_general : beta1 ≤ 4 + 2 (R-1) + (p+q-1)`,
  `general_bound_eq : 4 + 2(R-1) + (p+q-1) = 2W - 2 max s t + (s+t)/dg + 1` (in ℕ; valid since
  `R ≥ 2`, `p,q ≥ 1`), `dg_eq_s_of_s_eq_t`, `st_eq_one_one_iff : (s,t) = (1,1) ↔ A = 1 ∧ B = W - 1`,
  `beta1_le_two_W_of_ne : (s,t) ≠ (1,1) → beta1 ≤ 2 W`.


# Stage 3: Lemmas 14–16, main theorem, Solution

Files: `Exceptional.lean`, `Main.lean`, `Solution.lean`. Sorry count over `SemigroupBetti/*.lean`
and `Solution.lean`: **0**. `#print axioms` for `SemigroupBetti.beta1_le_two_mul_normalizedWidth`
and `SemigroupBetti.beta1_le_two_mul_width` (from `Solution`): `propext, Classical.choice,
Quot.sound`.

## Exceptional.lean — Lemmas 14–16
- Generic helpers on a pair side `K = {i,k}`: `sel_le_of_coords`, `pairsOf F K i k` (selected
  `(i,k)`-coordinate pairs; `pairsOf_injOn`, `card_pairsOf`, `pairsOf_antichain`, `pairsOf_pos`),
  `exists_coord_eq` (saturation: an injection of a family of size `c` into `[1,c]` hits every value).
- Exceptional-case facts under `hA : A = 1`, `hB : B = W - 1`: `exc_R : R = W - 1`, `exc_p`, `exc_q`
  (`p = q = 1`), `exc_U2 : U2 = Pi.single 2 (W-1)`, `exc_V2 : V2 = ![0,1,0,W-2]`,
  `exc_nu_V2 : ν(0,1,0,W-2) = (W-1) n₂`, `exc_coprime : Coprime n₃ n₂` (via `n₃ = n₂ + g`,
  `gcd m g = 1`).
- `sideP_split : d ∈ 𝓟 → IsSplit d {2,3}`, `sideQ_split : d ∈ 𝓠 → IsSplit d {1,3}`.
- **Lemma 14** `lemma14 (hA) (hB) (hP : P = W - 2) : crit 2 = W - 1`.
- **Lemma 15** `lemma15 (hA) (hB) (hQ : Q = W - 2) : (∃ D ∈ 𝓠, sel D {1,3} 1 = 1) ∧
  ∀ D ∈ 𝓠, sel D {1,3} 1 = 1 → sel D {1,3} = ![0,1,0,W-2]`.
- **Lemma 16** `lemma16_PQ (hA) (hB) : P + Q ≤ 2W - 5`, `beta1_le_two_W_exceptional (hA) (hB) :
  beta1 ≤ 2W`.

## Main.lean
- `GenData.beta1_le_two_W : G.beta1 ≤ 2 * G.W` (split on `(s,t) = (1,1)` via `st_eq_one_one_iff`);
  `GenData.beta1_le_two_w : G.beta1 ≤ 2 * G.w`.

## Solution.lean
- Follows the erdos266 convention: it does **not** import `Challenge`; it restates verbatim the
  `SemigroupBetti` namespace of `Challenge.lean` (definitions `toricIdeal`, `MinimallyGenerates`,
  `normalizedWidth`, and the two theorems with identical names and statements — checked by `diff`,
  only the proof bodies differ) and proves the theorems by
  `GenData.ofChallenge` + `spanRank_le_beta1_of_n_eq` + `beta1_le_two_W` / `beta1_le_two_w`.
  Importing `Challenge` would make the theorem names clash; renaming them would break
  `comparator.json`.

## Deviations (Stage 3)
- Lemma 15's "the one with u = 1 is exactly (0,1,0,W-2)" is stated as existence plus a universal
  statement over all `𝓠` degrees with `u = 1` (uniqueness of that degree also follows from
  `sel_coord_injOn` but is not needed).
- Lemma 11 is used through `corank_le` (the member with `u = 1` has `v ≥ #T`), not via an
  enumeration.

## Remaining sorry: none (Stages 1–3). Optional: reverse bridge inequality `beta1 ≤ spanRank`.
