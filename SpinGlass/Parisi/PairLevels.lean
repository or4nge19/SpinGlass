/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.Parisi.BranchAverages

/-!
# The pair average by levels, and its truncations

The Gibbs pair average `⟨θ(q_{(α,γ)})⟩_t` on `Σ_N × A_M` is a pair average over the branches with
the weights `u*_α exp F_t(α)` (`sum_wGibbs_pair_eq`). Decomposing `θ(q_{(α,γ)})` along the
levels, `θ(q_{(α,γ)}) = ∑_{r ≤ k} θ(q_{r+1}) (1_{(α,γ) ≥ r} − 1_{(α,γ) ≥ r+1})`
(`sum_theta_levels`), it becomes a combination of the **truncated pair fractions**
`truncPair r = Q_r^M / (S^M)²` (`treeBoundIntegrand_eq_levelBound`), where `Q_r^M` and `S^M` are
the prefix sums of squares and the cascade sum restricted to the branches of the truncated tree.

As `M → ∞` these converge to the cascade pair fractions `gibbsPair r = Q_r / S²` of the full
cascade (`tendsto_truncPair`, by monotone convergence of the branch sums), for every sample with
`0 < S < ∞`. The bound of the interpolation for the truncated tree therefore converges, by
dominated convergence, to the bound `guerraBound` for the whole cascade
(`tendsto_guerraTruncBound`, `tendsto_integral_guerraTruncBound`).
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable section

variable (N k : ℕ)
variable {T : Type*} [MeasurableSpace T]

/-! ### The prefix indicator on the truncated branches -/

omit N in
lemma truncBranchCoe_apply_eq_iff {M : ℕ} (α γ : TruncBranch k M) (i : Fin k) :
    truncBranchCoe k M α i = truncBranchCoe k M γ i ↔ α i = γ i := by
  simp only [truncBranchCoe, Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2⟩
    ext
    · exact_mod_cast h1
    · exact_mod_cast h2
  · rintro h
    rw [h]
    exact ⟨rfl, rfl⟩

omit N in
/-- On the truncated tree, `1_{(α,γ) ≥ r}` is `1` exactly when `r ≤ branchLevel α γ`. -/
lemma prefixEq_truncBranchCoe {M : ℕ} (r : ℕ) (α γ : TruncBranch k M) :
    prefixEq k r (truncBranchCoe k M α) (truncBranchCoe k M γ)
      = if r ≤ branchLevel α γ then 1 else 0 := by
  unfold prefixEq
  simp_rw [truncBranchCoe_apply_eq_iff]
  congr 1
  apply propext
  rcases r with _ | s
  · simp
  · constructor
    · rintro ⟨hs, h⟩
      have hb : branchNode k M α ⟨s, by omega⟩ = branchNode k M γ ⟨s, by omega⟩ := by
        rw [branchNode_eq_iff']
        intro i hi
        exact h i (by have := Fin.le_def.1 hi; simp only at this; omega)
      rw [branchNode_eq_iff_lt_branchLevel] at hb
      simp only at hb
      omega
    · intro hs
      have hk : s + 1 ≤ k := hs.trans (branchLevel_le α γ)
      refine ⟨hk, fun i hi => ?_⟩
      have hb : branchNode k M α ⟨s, by omega⟩ = branchNode k M γ ⟨s, by omega⟩ := by
        rw [branchNode_eq_iff_lt_branchLevel]
        simp only
        omega
      rw [branchNode_eq_iff'] at hb
      exact hb i (Fin.le_def.2 (by simp only; omega))

omit N in
/-- **The level decomposition** `θ(q_{L+1}) = ∑_{r ≤ k} θ(q_{r+1}) (1_{r ≤ L} − 1_{r+1 ≤ L})`. -/
lemma sum_theta_levels (θ : ℕ → ℝ) {L : ℕ} (hL : L ≤ k) :
    ∑ r ∈ Finset.range (k + 1), θ r * ((if r ≤ L then (1 : ℝ) else 0)
      - (if r + 1 ≤ L then (1 : ℝ) else 0)) = θ L := by
  have h : ∀ r, θ r * ((if r ≤ L then (1 : ℝ) else 0) - (if r + 1 ≤ L then (1 : ℝ) else 0))
      = if r = L then θ L else 0 := by
    intro r
    by_cases hr : r = L
    · subst hr
      simp
    · rcases lt_or_gt_of_ne hr with h1 | h1
      · simp [h1.le, Nat.succ_le_of_lt h1, hr]
      · simp [not_le.2 h1, hr, show ¬ (r + 1 ≤ L) by omega]
  simp_rw [h]
  rw [Finset.sum_eq_single L (fun r _ hr => by simp [hr])
    (fun hL' => absurd (Finset.mem_range.2 (by omega)) hL')]
  simp

/-! ### The truncated and the full pair fractions -/

/-- The cascade pair fraction `Q_r / S²` of the sample `(w, z)` for the function `G` of the marks
along the branches: `⟨1_{(α,γ) ≥ r}⟩` for the weights `u*_α G(z_α)`. -/
def gibbsPair (r : ℕ) (G : (Fin k → T) → ℝ≥0∞) (w : CascadeWeights k)
    (z : CascadeMarks T k) : ℝ :=
  (cascadeSq k r G (cascadeZip k (w, z)) * (cascadeSum k G (cascadeZip k (w, z)))⁻¹ ^ 2).toReal

lemma gibbsPair_nonneg (r : ℕ) (G : (Fin k → T) → ℝ≥0∞) (w : CascadeWeights k)
    (z : CascadeMarks T k) : 0 ≤ gibbsPair k r G w z :=
  ENNReal.toReal_nonneg

lemma gibbsPair_le_one (r : ℕ) {G : (Fin k → T) → ℝ≥0∞} (hG : Measurable G)
    (w : CascadeWeights k) (z : CascadeMarks T k) : gibbsPair k r G w z ≤ 1 := by
  unfold gibbsPair
  have := ENNReal.toReal_mono ENNReal.one_ne_top
    (cascadeSq_mul_inv_sq_le_one k r hG (cascadeZip k (w, z)))
  rwa [ENNReal.toReal_one] at this

/-- The pair fraction restricted to the branches of the tree truncated at `M`. -/
def truncPair (M r : ℕ) (G : (Fin k → T) → ℝ≥0∞) (w : CascadeWeights k)
    (z : CascadeMarks T k) : ℝ :=
  ((∑ α : TruncBranch k M, ∑ γ : TruncBranch k M,
      prefixEq k r (truncBranchCoe k M α) (truncBranchCoe k M γ)
        * (branchWeight k w (truncBranchCoe k M α) * branchWeight k w (truncBranchCoe k M γ)
          * (G (branchMarks k z (truncBranchCoe k M α)) * G (branchMarks k z (truncBranchCoe k M γ)))))
    * (∑ α : TruncBranch k M,
        branchWeight k w (truncBranchCoe k M α) * G (branchMarks k z (truncBranchCoe k M α)))⁻¹ ^ 2).toReal

omit [MeasurableSpace T] in
lemma truncPair_nonneg (M r : ℕ) (G : (Fin k → T) → ℝ≥0∞) (w : CascadeWeights k)
    (z : CascadeMarks T k) : 0 ≤ truncPair k M r G w z :=
  ENNReal.toReal_nonneg

omit [MeasurableSpace T] in
lemma truncPair_le_one (M r : ℕ) (G : (Fin k → T) → ℝ≥0∞) (w : CascadeWeights k)
    (z : CascadeMarks T k) : truncPair k M r G w z ≤ 1 := by
  unfold truncPair
  set S := ∑ α : TruncBranch k M,
    branchWeight k w (truncBranchCoe k M α) * G (branchMarks k z (truncBranchCoe k M α)) with hS
  have hQ : (∑ α : TruncBranch k M, ∑ γ : TruncBranch k M,
      prefixEq k r (truncBranchCoe k M α) (truncBranchCoe k M γ)
        * (branchWeight k w (truncBranchCoe k M α) * branchWeight k w (truncBranchCoe k M γ)
          * (G (branchMarks k z (truncBranchCoe k M α)) * G (branchMarks k z (truncBranchCoe k M γ)))))
      ≤ S * S := by
    rw [hS, Finset.sum_mul_sum]
    refine Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun γ _ => ?_
    calc prefixEq k r (truncBranchCoe k M α) (truncBranchCoe k M γ)
          * (branchWeight k w (truncBranchCoe k M α) * branchWeight k w (truncBranchCoe k M γ)
            * (G (branchMarks k z (truncBranchCoe k M α)) * G (branchMarks k z (truncBranchCoe k M γ))))
        ≤ 1 * (branchWeight k w (truncBranchCoe k M α) * branchWeight k w (truncBranchCoe k M γ)
            * (G (branchMarks k z (truncBranchCoe k M α))
              * G (branchMarks k z (truncBranchCoe k M γ)))) :=
          mul_le_mul' (prefixEq_le_one k r _ _) le_rfl
      _ = _ := by rw [one_mul, mul_mul_mul_comm]
  have h1 : (∑ α : TruncBranch k M, ∑ γ : TruncBranch k M,
      prefixEq k r (truncBranchCoe k M α) (truncBranchCoe k M γ)
        * (branchWeight k w (truncBranchCoe k M α) * branchWeight k w (truncBranchCoe k M γ)
          * (G (branchMarks k z (truncBranchCoe k M α)) * G (branchMarks k z (truncBranchCoe k M γ)))))
      * S⁻¹ ^ 2 ≤ 1 := by
    calc _ ≤ S * S * (S⁻¹ * S⁻¹) := by rw [sq]; exact mul_le_mul' hQ le_rfl
      _ = (S * S⁻¹) * (S * S⁻¹) := by ring
      _ ≤ 1 * 1 := mul_le_mul' (ENNReal.mul_inv_le_one _) (ENNReal.mul_inv_le_one _)
      _ = 1 := one_mul 1
  have := ENNReal.toReal_mono ENNReal.one_ne_top h1
  rwa [ENNReal.toReal_one] at this

/-! ### Monotone convergence of the pair fractions -/

omit N in
/-- Monotone convergence of double branch sums. -/
lemma tendsto_sum_sum_truncBranch (f : (Fin k → ℕ × ℕ) → (Fin k → ℕ × ℕ) → ℝ≥0∞) :
    Tendsto (fun M => ∑ α : TruncBranch k M, ∑ γ : TruncBranch k M,
      f (truncBranchCoe k M α) (truncBranchCoe k M γ)) atTop (𝓝 (∑' α, ∑' γ, f α γ)) := by
  classical
  have hsum : ∀ M, (∑ α : TruncBranch k M, ∑ γ : TruncBranch k M,
      f (truncBranchCoe k M α) (truncBranchCoe k M γ))
      = ∑ q ∈ truncFinset k M ×ˢ truncFinset k M, f q.1 q.2 := by
    intro M
    rw [Finset.sum_product]
    rw [sum_truncBranch_eq k M fun α => ∑ γ : TruncBranch k M, f α (truncBranchCoe k M γ)]
    refine Finset.sum_congr rfl fun α _ => ?_
    exact sum_truncBranch_eq k M fun γ => f α γ
  simp_rw [hsum]
  rw [← ENNReal.tsum_prod, ENNReal.tsum_eq_iSup_sum' (fun M => truncFinset k M ×ˢ truncFinset k M)]
  · exact tendsto_atTop_iSup fun M M' hM => Finset.sum_le_sum_of_subset
      (Finset.product_subset_product (truncFinset_mono k hM) (truncFinset_mono k hM))
  · intro t
    obtain ⟨M, hM⟩ := exists_subset_truncFinset k (t.image Prod.fst ∪ t.image Prod.snd)
    refine ⟨M, fun q hq => ?_⟩
    rw [Finset.mem_product]
    exact ⟨hM (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hq)),
      hM (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hq))⟩

/-- **The truncated pair fractions converge to the pair fraction of the cascade** whenever
`0 < S < ∞`. -/
theorem tendsto_truncPair (r : ℕ) {G : (Fin k → T) → ℝ≥0∞} (hG : Measurable G)
    (w : CascadeWeights k) (z : CascadeMarks T k)
    (hS0 : cascadeSum k G (cascadeZip k (w, z)) ≠ 0)
    (hS : cascadeSum k G (cascadeZip k (w, z)) ≠ ∞) :
    Tendsto (fun M => truncPair k M r G w z) atTop (𝓝 (gibbsPair k r G w z)) := by
  have hQ := tendsto_sum_sum_truncBranch k fun α γ => prefixEq k r α γ
    * (branchWeight k w α * branchWeight k w γ * (G (branchMarks k z α) * G (branchMarks k z γ)))
  have hSM := tendsto_sum_truncBranch k fun α => branchWeight k w α * G (branchMarks k z α)
  rw [← cascadeSum_cascadeZip k hG] at hSM
  rw [← cascadeSq_cascadeZip k r hG] at hQ
  have hQfin : cascadeSq k r G (cascadeZip k (w, z)) ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hS hS) (cascadeSq_le_sq k r hG _)
  have hinv : (cascadeSum k G (cascadeZip k (w, z)))⁻¹ ^ 2 ≠ ∞ :=
    ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 hS0)
  have hmul : Tendsto (fun M => (∑ α : TruncBranch k M, ∑ γ : TruncBranch k M,
      prefixEq k r (truncBranchCoe k M α) (truncBranchCoe k M γ)
        * (branchWeight k w (truncBranchCoe k M α) * branchWeight k w (truncBranchCoe k M γ)
          * (G (branchMarks k z (truncBranchCoe k M α)) * G (branchMarks k z (truncBranchCoe k M γ)))))
      * (∑ α : TruncBranch k M,
        branchWeight k w (truncBranchCoe k M α) * G (branchMarks k z (truncBranchCoe k M α)))⁻¹ ^ 2)
      atTop (𝓝 (cascadeSq k r G (cascadeZip k (w, z))
        * (cascadeSum k G (cascadeZip k (w, z)))⁻¹ ^ 2)) :=
    ENNReal.Tendsto.mul hQ (Or.inr hinv) (ENNReal.Tendsto.pow (tendsto_inv_iff.2 hSM)) (Or.inr hQfin)
  have hfin : cascadeSq k r G (cascadeZip k (w, z)) * (cascadeSum k G (cascadeZip k (w, z)))⁻¹ ^ 2
      ≠ ∞ := ENNReal.mul_ne_top hQfin hinv
  exact (ENNReal.tendsto_toReal hfin).comp hmul

/-- **Proposition 14.3.3 for the pair fraction**, under the product of the weights law and the
marks law: `𝔼 ⟨1_{(α,γ) ≥ r}⟩ = 1 - m_r` for every branch weight `G` with `𝔼 G < ∞` in the sense
of (14.4). This is the generic core of Talagrand's (14.76) and of its coupled version (14.137). -/
theorem integral_gibbsPair_eq [Nonempty T] (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {G : (Fin k → T) → ℝ≥0∞} (hG : Measurable G)
    (hGpos : ∀ zs, 0 < G zs) (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1)
    (hfin : cascadeRec k ms μs G ≠ ∞) (r : ℕ) :
    ∫ q, gibbsPair k r G q.1 q.2 ∂(cascadeWeightsLaw k ms).prod (cascadeMarksLaw k μs)
      = 1 - mExt ms r := by
  have hQm : Measurable fun ω : CascadeSpace T k =>
      cascadeSq k r G ω * (cascadeSum k G ω)⁻¹ ^ 2 :=
    (measurable_cascadeSq k r hG).mul ((measurable_cascadeSum k hG).inv.pow_const 2)
  have hae : ∀ᵐ ω ∂cascadeLaw k ms μs, cascadeSq k r G ω * (cascadeSum k G ω)⁻¹ ^ 2 < ∞ :=
    Filter.Eventually.of_forall fun ω =>
      lt_of_le_of_lt (cascadeSq_mul_inv_sq_le_one k r hG ω) ENNReal.one_lt_top
  have e1 : (∫ ω, (cascadeSq k r G ω * (cascadeSum k G ω)⁻¹ ^ 2).toReal ∂cascadeLaw k ms μs)
      = ∫ q, gibbsPair k r G q.1 q.2 ∂(cascadeWeightsLaw k ms).prod (cascadeMarksLaw k μs) := by
    rw [cascadeLaw_eq_map_cascadeZip]
    exact integral_map (measurable_cascadeZip k).aemeasurable
      (ENNReal.measurable_toReal.comp hQm).aestronglyMeasurable
  have hnn : (0 : ℝ) ≤ 1 - mExt ms r := by
    have := mExt_le_one (ms := ms) (fun i => (hlt i).le) r
    linarith
  rw [← e1, integral_toReal hQm.aemeasurable hae,
    lintegral_cascadeSq_mul_inv_sq k ms μs hG hGpos hsm hpos hlt hfin r,
    ENNReal.toReal_ofReal hnn]

/-! ### The bound by levels -/

/-- The integrand of the bound in terms of the pair fractions:
`(1/2) c₀ + (1/2) ∑_{r ≤ k} θ_r (pf r − pf (r+1))`. -/
def levelBound (c₀ : ℝ) (θ pf : ℕ → ℝ) : ℝ :=
  (1 / 2) * c₀ + (1 / 2) * ∑ r ∈ Finset.range (k + 1), θ r * (pf r - pf (r + 1))

omit N in
lemma abs_levelBound_le (c₀ : ℝ) (θ pf : ℕ → ℝ) (h0 : ∀ r, 0 ≤ pf r) (h1 : ∀ r, pf r ≤ 1) :
    |levelBound k c₀ θ pf| ≤ (1 / 2) * |c₀| + (1 / 2) * ∑ r ∈ Finset.range (k + 1), |θ r| := by
  unfold levelBound
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun r _ => ?_)) (by norm_num)
    rw [abs_mul]
    refine mul_le_of_le_one_right (abs_nonneg _) (abs_sub_le_iff.2 ⟨?_, ?_⟩)
    · linarith [h1 r, h0 (r + 1)]
    · linarith [h1 (r + 1), h0 r]

omit N in
lemma tendsto_levelBound (c₀ : ℝ) (θ : ℕ → ℝ) {pf : ℕ → ℕ → ℝ} {pfl : ℕ → ℝ}
    (h : ∀ r, Tendsto (fun M => pf M r) atTop (𝓝 (pfl r))) :
    Tendsto (fun M => levelBound k c₀ θ (pf M)) atTop (𝓝 (levelBound k c₀ θ pfl)) := by
  unfold levelBound
  refine tendsto_const_nhds.add (tendsto_const_nhds.mul (tendsto_finsetSum _ fun r _ => ?_))
  exact tendsto_const_nhds.mul ((h r).sub (h (r + 1)))

/-! ### The truncated bound integrand by levels -/

omit N in
/-- The finite-sum algebra of the level decomposition:
`(∑_{α,γ} X_{αγ} θ(L_{αγ})) / D² = ∑_r θ_r (A_r/D² − A_{r+1}/D²)`, `A_r = ∑_{L_{αγ} ≥ r} X_{αγ}`. -/
lemma sum_pair_levels_div {A : Type*} [Fintype A] (X : A → A → ℝ) (L : A → A → ℕ)
    (hL : ∀ α γ, L α γ ≤ k) (θ : ℕ → ℝ) (D : ℝ) :
    (∑ α, ∑ γ, X α γ * θ (L α γ)) / D ^ 2
      = ∑ r ∈ Finset.range (k + 1), θ r
          * ((∑ α, ∑ γ, (if r ≤ L α γ then (1 : ℝ) else 0) * X α γ) / D ^ 2
            - (∑ α, ∑ γ, (if r + 1 ≤ L α γ then (1 : ℝ) else 0) * X α γ) / D ^ 2) := by
  have hlev : ∀ α γ, X α γ * θ (L α γ) / D ^ 2 = ∑ r ∈ Finset.range (k + 1),
      θ r * ((if r ≤ L α γ then (1 : ℝ) else 0) * X α γ / D ^ 2
        - (if r + 1 ≤ L α γ then (1 : ℝ) else 0) * X α γ / D ^ 2) := by
    intro α γ
    rw [← sum_theta_levels k θ (hL α γ), Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  simp_rw [Finset.sum_div, hlev, ← Finset.sum_sub_distrib, Finset.mul_sum]
  conv_lhs => enter [2, α]; rw [Finset.sum_comm]
  exact Finset.sum_comm

omit [MeasurableSpace T] in
/-- **The trace-bound integrand by levels, for weights `u_α c_x` on `X × A_M`**: if the branch
weight `G` restricted to the truncated branches is the partial partition function
`Z_α(c) = ∑_x c_x e^{-H(x,α)}` and `u_α` is the truncated cascade weight, then for any function
`θ` of the level `(α, γ)`,

`(1/2) c₀ + (1/2) ⟨θ((α,γ))⟩_H = levelBound c₀ θ (r ↦ truncPair_r)`.

The one-dimensional scheme is the case `c = 1` (`treeBoundIntegrand_eq_levelBound`); the coupled
copies take `c = 1_{R_{1,2} = u}`. -/
theorem treeBoundIntegrand_prod_eq_levelBound {X : Type*} [Fintype X] (M : ℕ)
    (c : X → ℝ) (H : FiniteGibbs.EnergySpace (X × TruncBranch k M)) (c₀ : ℝ) (θ : ℕ → ℝ)
    (w : CascadeWeights k) (hw : ∀ α, branchWeight k w α ≠ ∞) (z : CascadeMarks T k)
    (G : (Fin k → T) → ℝ≥0∞)
    (hG : ∀ α : TruncBranch k M, G (branchMarks k z (truncBranchCoe k M α))
      = ENNReal.ofReal (wCondZ c H α))
    (hZnn : ∀ α : TruncBranch k M, 0 ≤ wCondZ c H α) :
    treeBoundIntegrand (fun p : X × TruncBranch k M => truncWt k M w p.2 * c p.1) c₀
        (fun x y => θ (branchLevel x.2 y.2)) H
      = levelBound k c₀ θ (fun r => truncPair k M r G w z) := by
  classical
  unfold treeBoundIntegrand levelBound
  congr 1
  have hpair := sum_wGibbs_prod_pair (truncWt k M w) c H (fun a b => θ (branchLevel a b))
  beta_reduce at hpair ⊢
  rw [hpair]
  congr 1
  set u : TruncBranch k M → ℝ := truncWt k M w with hu
  set Z : TruncBranch k M → ℝ := fun α => wCondZ c H α with hZ
  set D : ℝ := ∑ α, u α * Z α with hD
  set pe : ℕ → TruncBranch k M → TruncBranch k M → ℝ :=
    fun r α γ => if r ≤ branchLevel α γ then (1 : ℝ) else 0 with hpe
  have hwfin : ∀ α : TruncBranch k M, branchWeight k w (truncBranchCoe k M α) ≠ ∞ :=
    fun α => hw _
  have hu' : ∀ α : TruncBranch k M, (branchWeight k w (truncBranchCoe k M α)).toReal = u α :=
    fun α => rfl
  have hDeq : (∑ α : TruncBranch k M,
      branchWeight k w (truncBranchCoe k M α) * ENNReal.ofReal (Z α)).toReal = D := by
    rw [hD, ENNReal.toReal_sum fun α _ => ENNReal.mul_ne_top (hwfin α) ENNReal.ofReal_ne_top]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hZnn α), hu']
  have hQeq : ∀ r, (∑ α : TruncBranch k M, ∑ γ : TruncBranch k M,
      (if r ≤ branchLevel α γ then (1 : ℝ≥0∞) else 0)
        * (branchWeight k w (truncBranchCoe k M α) * branchWeight k w (truncBranchCoe k M γ)
          * (ENNReal.ofReal (Z α) * ENNReal.ofReal (Z γ)))).toReal
      = ∑ α, ∑ γ, pe r α γ * (u α * Z α * (u γ * Z γ)) := by
    intro r
    have hfin : ∀ α γ : TruncBranch k M, (if r ≤ branchLevel α γ then (1 : ℝ≥0∞) else 0)
        * (branchWeight k w (truncBranchCoe k M α) * branchWeight k w (truncBranchCoe k M γ)
          * (ENNReal.ofReal (Z α) * ENNReal.ofReal (Z γ))) ≠ ∞ := fun α γ =>
      ENNReal.mul_ne_top (by split_ifs <;> simp)
        (ENNReal.mul_ne_top (ENNReal.mul_ne_top (hwfin α) (hwfin γ))
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top))
    rw [ENNReal.toReal_sum fun α _ => ENNReal.sum_ne_top.2 fun γ _ => hfin α γ]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [ENNReal.toReal_sum fun γ _ => hfin α γ]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (hZnn α), ENNReal.toReal_ofReal (hZnn γ), hu', hu']
    congr 1
    · rw [hpe]
      beta_reduce
      split_ifs <;> simp
    · ring
  have htp : ∀ r, truncPair k M r G w z
      = (∑ α, ∑ γ, pe r α γ * (u α * Z α * (u γ * Z γ))) / D ^ 2 := by
    intro r
    unfold truncPair
    simp_rw [hG, prefixEq_truncBranchCoe]
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv, hQeq, hDeq, div_eq_mul_inv,
      inv_pow]
  simp_rw [htp]
  exact sum_pair_levels_div k (fun α γ => u α * Z α * (u γ * Z γ)) (fun α γ => branchLevel α γ)
    (fun α γ => branchLevel_le α γ) θ D

/-- **Talagrand's reduction of `⟨θ(q_{(α,γ)})⟩_t` to the cascade pair fractions** (the computation
leading to (14.76)), for the truncated tree: the integrand of the bound is `levelBound` evaluated
at the truncated pair fractions of `exp F_t`. -/
theorem treeBoundIntegrand_eq_levelBound (M : ℕ) (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (c₀ t h : ℝ)
    (w : CascadeWeights k) (hw : ∀ α, branchWeight k w α ≠ ∞)
    (ω : EnergySpace N × MarksSpace N k) :
    treeBoundIntegrand (branchWt (N := N) (truncWt k M w)) c₀
        (fun x y => parisiTheta ξ (treeOverlap qs x.2 y.2)) (truncHam N k M t h ω)
      = levelBound k c₀ (fun r => parisiTheta ξ (qExt qs (r + 1)))
          (fun r => truncPair k M r (hamG N k t h ω.1 ω.2.1) w ω.2.2) := by
  rw [branchWt_eq]
  refine (treeBoundIntegrand_prod_eq_levelBound k M (fun _ : Config N => (1 : ℝ))
    (truncHam N k M t h ω) c₀ (fun r => parisiTheta ξ (qExt qs (r + 1))) w hw ω.2.2
    (hamG N k t h ω.1 ω.2.1) (fun α => ?_) (fun α => ?_)).symm.symm
  · show ENNReal.ofReal (branchZX N k t h ω.1 ω.2.1 (branchMarks k ω.2.2 (truncBranchCoe k M α)))
      = _
    rw [wCondZ_truncHam, branchZ_eq]
  · rw [wCondZ_truncHam]
    exact (branchZ_pos N k t h ω.1 ω.2 _).le

/-! ### The bound for the whole cascade -/

/-- **The bound of Guerra's interpolation for the whole cascade at time `t`**:
`𝔼 [(1/2)(ξ(1) − ξ'(q_{k+1})) + (1/2) ∑_{r ≤ k} θ(q_{r+1}) (⟨1_{(α,γ) ≥ r}⟩_t − ⟨1_{(α,γ) ≥ r+1}⟩_t)]`,
the expectation being over the disorder `H_N` and the marks, at fixed weights `w`. -/
def guerraBound (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (h : ℝ) (w : CascadeWeights k) (t : ℝ) : ℝ :=
  ∫ ω, levelBound k (ξ 1 - deriv ξ (qs (Fin.last k))) (fun r => parisiTheta ξ (qExt qs (r + 1)))
      (fun r => gibbsPair k r (hamG N k t h ω.1 ω.2.1) w ω.2.2)
    ∂(gaussField N (overlapCovMatrix N ξ)).prod
      (marksLaw N k (parisiVar ξ qs 0) fun p => parisiVar ξ qs (p.val + 1))

/-- The branch partition function as an uncurried function of `(t, H, z₀)` and the marks. -/
lemma measurable_uncurry_hamG (h : ℝ) :
    Measurable (Function.uncurry fun a : ℝ × EnergySpace N × (Fin N → ℝ) =>
      hamG N k a.1 h a.2.1 a.2.2) := by
  have := measurable_hamG N k h
  unfold Function.uncurry
  exact this

/-- Joint measurability of the cascade sum of `exp F_t` in `(t, H, z₀)` and the sample. -/
lemma measurable_cascadeSum_hamG (h : ℝ) :
    Measurable fun q : (ℝ × EnergySpace N × (Fin N → ℝ)) × CascadeSpace (Fin N → ℝ) k =>
      cascadeSum k (hamG N k q.1.1 h q.1.2.1 q.1.2.2) q.2 := by
  have := measurable_cascadeSum_prod k (measurable_uncurry_hamG N k h)
  exact this

lemma measurable_cascadeSq_hamG (r : ℕ) (h : ℝ) :
    Measurable fun q : (ℝ × EnergySpace N × (Fin N → ℝ)) × CascadeSpace (Fin N → ℝ) k =>
      cascadeSq k r (hamG N k q.1.1 h q.1.2.1 q.1.2.2) q.2 := by
  have := measurable_cascadeSq_prod k r (measurable_uncurry_hamG N k h)
  exact this

/-- Joint measurability of the pair fraction in `(t, H, z₀, w, z)`. -/
lemma measurable_gibbsPair_hamG (r : ℕ) (h : ℝ) :
    Measurable fun q : (ℝ × EnergySpace N × (Fin N → ℝ)) × (CascadeWeights k × CascadeMarks (Fin N → ℝ) k) =>
      gibbsPair k r (hamG N k q.1.1 h q.1.2.1 q.1.2.2) q.2.1 q.2.2 := by
  unfold gibbsPair
  have hm : Measurable fun q : (ℝ × EnergySpace N × (Fin N → ℝ))
      × (CascadeWeights k × CascadeMarks (Fin N → ℝ) k) => (q.1, cascadeZip k q.2) :=
    measurable_fst.prodMk ((measurable_cascadeZip k).comp measurable_snd)
  have h1 := (measurable_cascadeSq_hamG N k r h).comp hm
  have h2 := (measurable_cascadeSum_hamG N k h).comp hm
  simp only [Function.comp_def] at h1 h2
  exact (h1.mul (h2.inv.pow_const 2)).ennreal_toReal

lemma measurable_gibbsPair_hamG' (r : ℕ) (t h : ℝ) (w : CascadeWeights k) :
    Measurable fun ω : EnergySpace N × MarksSpace N k =>
      gibbsPair k r (hamG N k t h ω.1 ω.2.1) w ω.2.2 := by
  have hm : Measurable fun ω : EnergySpace N × MarksSpace N k =>
      ((t, ω.1, ω.2.1), (w, ω.2.2)) :=
    (measurable_const.prodMk (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
      (measurable_const.prodMk (measurable_snd.comp measurable_snd))
  have := (measurable_gibbsPair_hamG N k r h).comp hm
  simp only [Function.comp_def] at this
  exact this

/-- Measurability of the cascade sum of `exp F_t` in the disorder and the marks. -/
lemma measurable_cascadeSum_hamG' (t h : ℝ) (w : CascadeWeights k) :
    Measurable fun ω : EnergySpace N × MarksSpace N k =>
      cascadeSum k (hamG N k t h ω.1 ω.2.1) (cascadeZip k (w, ω.2.2)) := by
  have hm : Measurable fun ω : EnergySpace N × MarksSpace N k =>
      ((t, ω.1, ω.2.1), cascadeZip k (w, ω.2.2)) :=
    (measurable_const.prodMk (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
      ((measurable_cascadeZip k).comp (measurable_const.prodMk (measurable_snd.comp measurable_snd)))
  have := (measurable_cascadeSum_hamG N k h).comp hm
  simp only [Function.comp_def] at this
  exact this

/-- For weights of positive total mass, the cascade sum of `exp F_t` is positive. -/
lemma cascadeSum_hamG_ne_zero (t h : ℝ) (H : EnergySpace N) (z₀ : Fin N → ℝ) (w : CascadeWeights k)
    (hW0 : weightSum k w ≠ 0) (z : CascadeMarks (Fin N → ℝ) k) :
    cascadeSum k (hamG N k t h H z₀) (cascadeZip k (w, z)) ≠ 0 := by
  rw [cascadeSum_cascadeZip k (measurable_hamG' N k t h H z₀)]
  intro hzero
  rw [ENNReal.tsum_eq_zero] at hzero
  refine hW0 (ENNReal.tsum_eq_zero.2 fun α => ?_)
  rcases mul_eq_zero.1 (hzero α) with h0 | h0
  · exact h0
  · exact absurd h0 (hamG_pos N k t h H z₀ _).ne'

/-- For weights of finite total mass, the cascade sum of `exp F_t` is almost surely finite. -/
lemma ae_cascadeSum_hamG_lt_top (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (t h : ℝ)
    (w : CascadeWeights k) (hW : weightSum k w ≠ ∞) :
    ∀ᵐ ω ∂(gaussField N (overlapCovMatrix N ξ)).prod
        (marksLaw N k (parisiVar ξ qs 0) fun p => parisiVar ξ qs (p.val + 1)),
      cascadeSum k (hamG N k t h ω.1 ω.2.1) (cascadeZip k (w, ω.2.2)) < ∞ := by
  set vs : Fin k → ℝ≥0 := fun p => parisiVar ξ qs (p.val + 1) with hvs
  have hmeas := measurable_cascadeSum_hamG' N k t h w
  rw [Measure.ae_prod_iff_ae_ae (measurableSet_lt hmeas measurable_const)]
  refine Filter.Eventually.of_forall fun H => ?_
  unfold marksLaw
  have hmeas' : Measurable fun z : MarksSpace N k =>
      cascadeSum k (hamG N k t h H z.1) (cascadeZip k (w, z.2)) := by
    have := hmeas.comp (measurable_const.prodMk measurable_id : Measurable fun z : MarksSpace N k => (H, z))
    simp only [Function.comp_def] at this
    exact this
  rw [Measure.ae_prod_iff_ae_ae (measurableSet_lt hmeas' measurable_const)]
  refine Filter.Eventually.of_forall fun z₀ => ?_
  have hmeas'' : Measurable fun z : CascadeMarks (Fin N → ℝ) k =>
      cascadeSum k (hamG N k t h H z₀) (cascadeZip k (w, z)) := by
    have := (measurable_cascadeSum k (measurable_hamG' N k t h H z₀)).comp
      ((measurable_cascadeZip k).comp (measurable_const.prodMk measurable_id :
        Measurable fun z : CascadeMarks (Fin N → ℝ) k => (w, z)))
    simp only [Function.comp_def] at this
    exact this
  refine ae_lt_top hmeas'' ?_
  rw [lintegral_cascadeSum_cascadeZip k (gaussianMarks N k vs) w (measurable_hamG' N k t h H z₀)]
  exact ENNReal.mul_ne_top hW (lintegral_hamG_ne_top N k vs t h H z₀)

omit N in
/-- For weights of positive finite total mass, the truncated trees eventually carry a branch of
positive weight. -/
lemma exists_truncWt_ne_zero (w : CascadeWeights k) (hW0 : weightSum k w ≠ 0)
    (hW : weightSum k w ≠ ∞) :
    ∃ M₀, ∀ M, M₀ ≤ M → ∃ β : TruncBranch k M, truncWt k M w β ≠ 0 := by
  obtain ⟨α₀, hα₀⟩ : ∃ α₀, branchWeight k w α₀ ≠ 0 := by
    by_contra hcon
    exact hW0 (ENNReal.tsum_eq_zero.2 fun α => by simpa using fun h => hcon ⟨α, h⟩)
  obtain ⟨M₀, hM₀⟩ := exists_subset_truncFinset k {α₀}
  refine ⟨M₀, fun M hM => ?_⟩
  have hmem : α₀ ∈ truncFinset k M := truncFinset_mono k hM (hM₀ (Finset.mem_singleton_self _))
  rw [mem_truncFinset_iff] at hmem
  refine ⟨fun i => (⟨(α₀ i).1, (hmem i).1⟩, ⟨(α₀ i).2, (hmem i).2⟩), ?_⟩
  have hcoe : truncBranchCoe k M (fun i => (⟨(α₀ i).1, (hmem i).1⟩, ⟨(α₀ i).2, (hmem i).2⟩)) = α₀ := by
    funext i
    rfl
  unfold truncWt
  rw [hcoe]
  exact ENNReal.toReal_ne_zero.2 ⟨hα₀, ne_top_of_le_ne_top hW (branchWeight_le_weightSum k w α₀)⟩

/-- **The truncated bounds converge to the bound for the whole cascade**, at every time `t`. -/
theorem tendsto_guerraTruncBound (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (h : ℝ) (w : CascadeWeights k)
    (hW0 : weightSum k w ≠ 0) (hW : weightSum k w ≠ ∞) (t : ℝ) :
    Tendsto (fun M => guerraTruncBound N k M ξ qs h w t) atTop (𝓝 (guerraBound N k ξ qs h w t)) := by
  obtain ⟨M₀, hM₀⟩ := exists_truncWt_ne_zero k w hW0 hW
  set c₀ := ξ 1 - deriv ξ (qs (Fin.last k)) with hc₀
  set θ : ℕ → ℝ := fun r => parisiTheta ξ (qExt qs (r + 1)) with hθ
  have hw : ∀ α, branchWeight k w α ≠ ∞ :=
    fun α => ne_top_of_le_ne_top hW (branchWeight_le_weightSum k w α)
  have hF : ∀ M (ω : EnergySpace N × MarksSpace N k),
      treeBoundIntegrand (branchWt (N := N) (truncWt k M w)) c₀
        (fun x y => parisiTheta ξ (treeOverlap qs x.2 y.2)) (truncHam N k M t h ω)
      = levelBound k c₀ θ (fun r => truncPair k M r (hamG N k t h ω.1 ω.2.1) w ω.2.2) :=
    fun M ω => treeBoundIntegrand_eq_levelBound N k M ξ qs c₀ t h w hw ω
  unfold guerraTruncBound guerraBound
  refine tendsto_integral_filter_of_dominated_convergence
    (fun _ => (1 / 2) * |c₀| + (1 / 2) * ∑ r ∈ Finset.range (k + 1), |θ r|) ?_ ?_
    (integrable_const _) ?_
  · filter_upwards [Filter.eventually_ge_atTop M₀] with M hM
    obtain ⟨β, hβ⟩ := hM₀ M hM
    have hm := (continuous_treeBoundIntegrand (branchWt (N := N) (truncWt k M w))
      (fun x => truncWt_nonneg k M w x.2) ⟨(fun _ => true, β), hβ⟩ c₀
      (fun x y => parisiTheta ξ (treeOverlap qs x.2 y.2))).measurable.comp
        (measurable_truncHam N k M t h)
    simp only [Function.comp_def] at hm
    exact hm.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun M => Filter.Eventually.of_forall fun ω => ?_
    rw [hF M ω, Real.norm_eq_abs]
    exact abs_levelBound_le k c₀ θ _ (fun r => truncPair_nonneg k M r _ w _)
      (fun r => truncPair_le_one k M r _ w _)
  · filter_upwards [ae_cascadeSum_hamG_lt_top N k ξ qs t h w hW] with ω hω
    refine (tendsto_levelBound k c₀ θ fun r => tendsto_truncPair k r
      (measurable_hamG' N k t h ω.1 ω.2.1) w ω.2.2
      (cascadeSum_hamG_ne_zero N k t h ω.1 ω.2.1 w hW0 ω.2.2) hω.ne).congr fun M => ?_
    exact (hF M ω).symm

/-- The integrated truncated bounds converge to the integrated bound for the whole cascade. -/
theorem tendsto_integral_guerraTruncBound (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (h : ℝ)
    (w : CascadeWeights k) (hW0 : weightSum k w ≠ 0) (hW : weightSum k w ≠ ∞) :
    Tendsto (fun M => ∫ t in (0 : ℝ)..1, guerraTruncBound N k M ξ qs h w t) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, guerraBound N k ξ qs h w t)) := by
  obtain ⟨M₀, hM₀⟩ := exists_truncWt_ne_zero k w hW0 hW
  set c₀ := ξ 1 - deriv ξ (qs (Fin.last k)) with hc₀
  set θ : ℕ → ℝ := fun r => parisiTheta ξ (qExt qs (r + 1)) with hθ
  have hw : ∀ α, branchWeight k w α ≠ ∞ :=
    fun α => ne_top_of_le_ne_top hW (branchWeight_le_weightSum k w α)
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ => (1 / 2) * |c₀| + (1 / 2) * ∑ r ∈ Finset.range (k + 1), |θ r|) ?_ ?_
    intervalIntegrable_const ?_
  · filter_upwards [Filter.eventually_ge_atTop M₀] with M hM
    obtain ⟨β, hβ⟩ := hM₀ M hM
    exact (continuous_guerraTruncBound N k M ξ qs h w ⟨β, hβ⟩).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun M => Filter.Eventually.of_forall fun t _ => ?_
    unfold guerraTruncBound
    refine (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun ω => ?_)).trans
      (by rw [probReal_univ, mul_one])
    rw [treeBoundIntegrand_eq_levelBound N k M ξ qs c₀ t h w hw ω, Real.norm_eq_abs]
    exact abs_levelBound_le k c₀ θ _ (fun r => truncPair_nonneg k M r _ w _)
      (fun r => truncPair_le_one k M r _ w _)
  · exact Filter.Eventually.of_forall fun t _ => tendsto_guerraTruncBound N k ξ qs h w hW0 hW t

end

end SpinGlass
