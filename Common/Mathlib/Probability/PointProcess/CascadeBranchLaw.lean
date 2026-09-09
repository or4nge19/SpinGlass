/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Common.Mathlib.Probability.PointProcess.CascadeNodeMarks
import Common.Mathlib.Probability.PointProcess.CascadeBranches
import Common.Mathlib.Probability.PointProcess.CascadeIdentities

/-!
# The marks along a branch, the weight sum, and one-branch averages

For a `k`-level cascade with independent marks, the marks `(z_{1,α}, …, z_{k,α})` along any
fixed branch `α` are distributed as the product `μ₁ ⊗ ⋯ ⊗ μ_k`
(`cascadeMarksLaw_map_branchMarks`): they are finitely many distinct coordinates of the
infinite product of the node marks, and the marginal of an infinite product along an injective
finite family of coordinates is the finite product (`Measure.infinitePi_map_comp_injective`).

Consequently, for fixed weights, `𝔼_z ∑_α u*_α g(z_α) = (∑_α u*_α) · 𝔼 g`
(`lintegral_cascadeSum_cascadeZip`), and for the normalized weights `v_α = u*_α / ∑ u*_γ`,
`𝔼 ∑_α v_α g(z_α) = 𝔼 g` — the marks of a branch chosen according to the cascade weights have
the law of the marks (`lintegral_cascadeSum_div_cascadeSum_one`, Talagrand Vol. II, (14.10)).

We also record that the total weight `W = ∑_α u*_α` of a cascade with `0 < m₁ < ⋯ < m_k < 1`
is almost surely positive and finite (`ae_weightSum_ne_zero_ne_top`).
-/

open MeasureTheory Set Filter Function
open scoped ENNReal Topology

universe u

namespace MeasureTheory.Measure

variable {ι T : Type*} [MeasurableSpace T]

/-- **The marginal of an infinite product along an injective finite family of coordinates** is
the finite product of the corresponding factors. -/
theorem infinitePi_map_comp_injective {κ : Type*} [Fintype κ] (μ : ι → Measure T)
    [∀ i, IsProbabilityMeasure (μ i)] {e : κ → ι} (he : Injective e) :
    (infinitePi μ).map (fun x p => x (e p)) = Measure.pi fun p => μ (e p) := by
  classical
  set I : Finset ι := Finset.univ.map ⟨e, he⟩ with hI
  have hrange : Set.range e = (I : Set ι) := by
    ext i
    simp [hI]
  let eqv : κ ≃ I := (Equiv.ofInjective e he).trans (Equiv.setCongr hrange)
  have heqv : ∀ p, ((eqv p : I) : ι) = e p := fun p => rfl
  have hcomp : (fun x : ι → T => fun p => x (e p))
      = (fun y : I → T => fun p => y (eqv p)) ∘ I.restrict := by
    funext x p
    simp [Finset.restrict_def, heqv]
  have hg : Measurable fun y : I → T => fun p => y (eqv p) :=
    measurable_pi_lambda _ fun p => measurable_pi_apply _
  rw [hcomp, ← Measure.map_map hg (Finset.measurable_restrict I), infinitePi_map_restrict]
  have hpres := measurePreserving_piCongrLeft (μ := fun i : I => μ i)
    (α := fun _ : I => T) eqv
  have hsymm : (fun y : I → T => fun p => y (eqv p))
      = (MeasurableEquiv.piCongrLeft (fun _ : I => T) eqv).symm := by
    funext y
    exact (funext fun p => (Equiv.piCongrLeft_symm_apply _ eqv y p).symm)
  rw [hsymm, ← hpres.map_eq, MeasurableEquiv.map_symm_map]
  rfl

end MeasureTheory.Measure

namespace ProbabilityTheory

variable {T : Type u} [MeasurableSpace T]

/-! ### The marks along a branch -/

lemma measurable_branchMarks (k : ℕ) (α : Fin k → ℕ × ℕ) :
    Measurable fun z : CascadeMarks T k => branchMarks k z α := by
  have h : (fun z : CascadeMarks T k => branchMarks k z α)
      = (fun x : CascadeNode k → T => fun p => x ⟨p, branchPrefix α p⟩) ∘ nodeMarks k := by
    funext z p
    exact branchMarks_eq_nodeMark k z α p
  rw [h]
  exact (measurable_pi_lambda _ fun p => measurable_pi_apply _).comp (measurable_nodeMarks k)

/-- **The marks along a branch are distributed as `μ₁ ⊗ ⋯ ⊗ μ_k`.** -/
theorem cascadeMarksLaw_map_branchMarks (k : ℕ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] (α : Fin k → ℕ × ℕ) :
    (cascadeMarksLaw k μs).map (fun z => branchMarks k z α) = Measure.pi μs := by
  have he : Injective fun p : Fin k => (⟨p, branchPrefix α p⟩ : CascadeNode k) :=
    fun p q h => congrArg Sigma.fst h
  have h : (fun z : CascadeMarks T k => branchMarks k z α)
      = (fun x : CascadeNode k → T => fun p => x ⟨p, branchPrefix α p⟩) ∘ nodeMarks k := by
    funext z p
    exact branchMarks_eq_nodeMark k z α p
  rw [h, ← Measure.map_map (measurable_pi_lambda _ fun p => measurable_pi_apply _)
    (measurable_nodeMarks k), cascadeMarksLaw_map_nodeMarks,
    Measure.infinitePi_map_comp_injective _ he]

/-! ### The total weight -/

omit [MeasurableSpace T] in
lemma measurable_branchWeight : ∀ (k : ℕ) (α : Fin k → ℕ × ℕ),
    Measurable fun w : CascadeWeights k => branchWeight k w α
  | 0, _ => measurable_const
  | k + 1, α => by
    have h1 : Measurable fun w : CascadeWeights (k + 1) => (w.1 (α 0).1).2 :=
      measurable_snd.comp ((measurable_pi_apply _).comp measurable_fst)
    have h2 : Measurable fun w : CascadeWeights (k + 1) => (w.1 (α 0).1).1 (α 0).2 :=
      (measurable_pi_apply _).comp (measurable_fst.comp ((measurable_pi_apply _).comp measurable_fst))
    have h3 : Measurable fun w : CascadeWeights (k + 1) =>
        branchWeight k (w.2 (α 0).1 (α 0).2) (Fin.tail α) :=
      (measurable_branchWeight k (Fin.tail α)).comp
        ((measurable_pi_apply _).comp ((measurable_pi_apply _).comp measurable_snd))
    exact (Measurable.ite (h1 measurableSet_Ioi) (ENNReal.measurable_ofReal.comp h2)
      measurable_const).mul h3

/-- The total weight `W = ∑_α u*_α` of a cascade sample of weights. -/
noncomputable def weightSum (k : ℕ) (w : CascadeWeights k) : ℝ≥0∞ := ∑' α, branchWeight k w α

omit [MeasurableSpace T] in
lemma measurable_weightSum (k : ℕ) : Measurable (weightSum k) :=
  Measurable.tsum fun α => measurable_branchWeight k α

lemma cascadeSum_one_cascadeZip (k : ℕ) (w : CascadeWeights k) (z : CascadeMarks T k) :
    cascadeSum k (fun _ => 1) (cascadeZip k (w, z)) = weightSum k w := by
  rw [cascadeSum_cascadeZip k measurable_const]
  simp [weightSum]

omit [MeasurableSpace T] in
lemma weightSum_zero (w : CascadeWeights 0) : weightSum 0 w = 1 := by
  rw [weightSum, tsum_fintype, Finset.univ_unique, Finset.sum_singleton]
  rfl

omit [MeasurableSpace T] in
lemma branchWeight_le_weightSum (k : ℕ) (w : CascadeWeights k) (α : Fin k → ℕ × ℕ) :
    branchWeight k w α ≤ weightSum k w := ENNReal.le_tsum α

omit [MeasurableSpace T] in
lemma prefixEq_le_one (k r : ℕ) (α γ : Fin k → ℕ × ℕ) : prefixEq k r α γ ≤ 1 := by
  unfold prefixEq
  split_ifs <;> simp

/-! ### One-branch averages -/

/-- **The marks average of a cascade sum with fixed weights**:
`𝔼_z ∑_α u*_α g(z_α) = (∑_α u*_α) · ∫ g dμ₁ ⊗ ⋯ ⊗ μ_k`. -/
theorem lintegral_cascadeSum_cascadeZip (k : ℕ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] (w : CascadeWeights k) {g : (Fin k → T) → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ z, cascadeSum k g (cascadeZip k (w, z)) ∂cascadeMarksLaw k μs
      = weightSum k w * ∫⁻ x, g x ∂Measure.pi μs := by
  simp_rw [cascadeSum_cascadeZip k hg]
  have hm : ∀ α, AEMeasurable (fun z : CascadeMarks T k => branchWeight k w α * g (branchMarks k z α))
      (cascadeMarksLaw k μs) := fun α =>
    (measurable_const.mul (hg.comp (measurable_branchMarks k α))).aemeasurable
  rw [lintegral_tsum hm, weightSum, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun α => ?_
  have hgm : Measurable fun z : CascadeMarks T k => g (branchMarks k z α) :=
    hg.comp (measurable_branchMarks k α)
  rw [lintegral_const_mul _ hgm, ← lintegral_map hg (measurable_branchMarks k α),
    cascadeMarksLaw_map_branchMarks]

/-- **The marks of a branch chosen according to the weights have the law of the marks**:
for any law `Pw` of the weights under which the total weight is a.s. positive and finite,
`𝔼 ∑_α v_α g(z_α) = ∫ g dμ₁ ⊗ ⋯ ⊗ μ_k`, where `v_α = u*_α / ∑_γ u*_γ`. -/
theorem lintegral_cascadeSum_div_cascadeSum_one_prod (k : ℕ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] (Pw : Measure (CascadeWeights k)) [IsProbabilityMeasure Pw]
    (hae : ∀ᵐ w ∂Pw, weightSum k w ≠ 0 ∧ weightSum k w ≠ ∞) {g : (Fin k → T) → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ q, cascadeSum k g (cascadeZip k q) / cascadeSum k (fun _ => 1) (cascadeZip k q)
        ∂Pw.prod (cascadeMarksLaw k μs)
      = ∫⁻ x, g x ∂Measure.pi μs := by
  have hmeas : Measurable fun q : CascadeWeights k × CascadeMarks T k =>
      cascadeSum k g (cascadeZip k q) / cascadeSum k (fun _ => 1) (cascadeZip k q) :=
    ((measurable_cascadeSum k hg).comp (measurable_cascadeZip k)).div
      ((measurable_cascadeSum k measurable_const).comp (measurable_cascadeZip k))
  rw [lintegral_prod _ hmeas.aemeasurable]
  have hinner : ∀ w : CascadeWeights k, (∫⁻ z, cascadeSum k g (cascadeZip k (w, z))
      / cascadeSum k (fun _ => 1) (cascadeZip k (w, z)) ∂cascadeMarksLaw k μs)
      = weightSum k w * (∫⁻ x, g x ∂Measure.pi μs) * (weightSum k w)⁻¹ := by
    intro w
    simp_rw [cascadeSum_one_cascadeZip, div_eq_mul_inv]
    have hm : Measurable fun z : CascadeMarks T k => cascadeSum k g (cascadeZip k (w, z)) :=
      (measurable_cascadeSum k hg).comp
        ((measurable_cascadeZip k).comp (measurable_const.prodMk measurable_id))
    rw [lintegral_mul_const _ hm, lintegral_cascadeSum_cascadeZip k μs w hg]
  simp_rw [hinner]
  have hae' : ∀ᵐ w ∂Pw, weightSum k w * (∫⁻ x, g x ∂Measure.pi μs) * (weightSum k w)⁻¹
      = ∫⁻ x, g x ∂Measure.pi μs := by
    filter_upwards [hae] with w hw
    rw [mul_right_comm, ENNReal.mul_inv_cancel hw.1 hw.2, one_mul]
  rw [lintegral_congr_ae hae', lintegral_const, measure_univ, mul_one]

/-! ### The total weight is almost surely positive and finite -/

/-- For `0 < m₁ < ⋯ < m_k < 1` the total weight of the cascade is almost surely positive and
finite. -/
theorem ae_weightSum_ne_zero_ne_top (k : ℕ) (ms : Fin k → ℝ) (hsm : StrictMono ms)
    (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1) :
    ∀ᵐ w ∂cascadeWeightsLaw k ms, weightSum k w ≠ 0 ∧ weightSum k w ≠ ∞ := by
  classical
  -- work with the cascade with trivial marks
  let μs : Fin k → Measure PUnit.{1} := fun _ => Measure.dirac PUnit.unit
  have hS : Measurable (cascadeSum (T := PUnit.{1}) k fun _ => 1) :=
    measurable_cascadeSum k measurable_const
  -- positivity
  have hpos' : ∀ᵐ ω ∂cascadeLaw k ms μs, 0 < cascadeSum (T := PUnit.{1}) k (fun _ => 1) ω :=
    ae_cascadeSum_pos k ms μs measurable_const (fun _ => one_pos) hpos
  -- finiteness, from the finite moment of Proposition 14.2.2
  have hfin' : ∀ᵐ ω ∂cascadeLaw k ms μs, cascadeSum (T := PUnit.{1}) k (fun _ => 1) ω < ∞ := by
    cases k with
    | zero =>
      exact Filter.Eventually.of_forall fun ω => by simp
    | succ k =>
      have hm₀ : 0 < ms 0 / 2 := by linarith [hpos 0]
      have hsm' : StrictMono (Fin.cons (ms 0 / 2) ms : Fin (k + 2) → ℝ) := by
        rw [Fin.strictMono_cons]
        exact ⟨fun j => lt_of_lt_of_le (by linarith [hpos 0]) (hsm.monotone (Fin.zero_le j)), hsm⟩
      have hmom := lintegral_cascadeSum_rpow (k + 1) ms μs (G := fun _ => 1) measurable_const
        hm₀ hsm' hlt
      rw [cascadeRec_one _ _ _ hpos, ENNReal.one_rpow, one_mul] at hmom
      have hne : ∫⁻ ω, cascadeSum (T := PUnit.{1}) (k + 1) (fun _ => 1) ω ^ (ms 0 / 2)
          ∂cascadeLaw (k + 1) ms μs ≠ ∞ := by
        rw [hmom]
        exact (cascadeConst_pos_ne_top (k + 1) hm₀ hsm' hlt).2
      filter_upwards [ae_lt_top (hS.pow_const _) hne] with ω hω
      exact lt_top_iff_ne_top.2 fun h => hω.ne ((ENNReal.rpow_eq_top_iff_of_pos hm₀).2 h)
  have hjoint := hpos'.and hfin'
  have hmeasS : MeasurableSet {ω : CascadeSpace PUnit.{1} k |
      0 < cascadeSum k (fun _ => 1) ω ∧ cascadeSum k (fun _ => 1) ω < ∞} :=
    (measurableSet_lt measurable_const hS).inter (measurableSet_lt hS measurable_const)
  rw [cascadeLaw_eq_map_cascadeZip, ae_map_iff (measurable_cascadeZip k).aemeasurable hmeasS]
    at hjoint
  have hW : ∀ q : CascadeWeights k × CascadeMarks PUnit.{1} k,
      cascadeSum k (fun _ => 1) (cascadeZip k q) = weightSum k q.1 := fun q =>
    cascadeSum_one_cascadeZip k q.1 q.2
  have hfst : ((cascadeWeightsLaw k ms).prod (cascadeMarksLaw k μs)).map Prod.fst
      = cascadeWeightsLaw k ms := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hmeasW : MeasurableSet {w : CascadeWeights k | weightSum k w ≠ 0 ∧ weightSum k w ≠ ∞} :=
    ((measurable_weightSum k) (measurableSet_singleton 0)).compl.inter
      ((measurable_weightSum k) (measurableSet_singleton ∞)).compl
  have h' : ∀ᵐ q ∂(cascadeWeightsLaw k ms).prod (cascadeMarksLaw k μs),
      weightSum k q.1 ≠ 0 ∧ weightSum k q.1 ≠ ∞ := by
    filter_upwards [hjoint] with q hq
    rw [hW] at hq
    exact ⟨hq.1.ne', hq.2.ne⟩
  have h'' := (ae_map_iff measurable_fst.aemeasurable hmeasW).2 h'
  rwa [hfst] at h''

end ProbabilityTheory
