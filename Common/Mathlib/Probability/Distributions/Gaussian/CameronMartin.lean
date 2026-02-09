/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Common.Mathlib.Probability.Distributions.Gaussian.CompletionResultsToBeMoved
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.CovarianceBilinDual
import Mathlib.Topology.Algebra.Module.ClosedSubmodule

/-!
# Cameron–Martin space

For a (Borel) Gaussian measure `μ` on a real Banach space `E`, the **Cameron–Martin space** is a
separable Hilbert space canonically associated to `μ`. Its image in `E` describes the directions
along which `μ` is quasi-invariant under translations (Cameron–Martin theorem).

In this file we construct the Cameron–Martin space under the minimal hypothesis of a finite
second moment, encoded as a typeclass `HasTwoMoments μ`.

We use the RKHS construction: we embed `StrongDual ℝ E` into `Lp ℝ 2 μ` via the centered map
\(L \mapsto (x \mapsto L(x - \int y\, dμ(y)))\), take the closure of its range, and inherit the
Hilbert structure from `Lp`.

## Main definitions

* `HasTwoMoments μ`: a finite measure with `MemLp id 2 μ`.
* `cameronMartin μ`: the closure of the range of `StrongDual.centeredToLp μ` in `Lp ℝ 2 μ`.
* `cmOfDual μ L`: inclusion of the dual space `StrongDual ℝ E` into the Cameron–Martin space.
* `cmCoe`: the continuous linear map from the Cameron-Martin space
  to the initial space `E`. It is injective and its range is the subspace of `E` of points
  `y` such that `⨆ (L : StrongDual ℝ E) (_ : Var[L; μ] ≤ 1), L y` is finite.
* `cmOfBounded`: the inverse of `cmCoe`, which takes a point `y : E` with bounded
  Cameron-Martin norm and returns a point of `cameronMartin μ`.

## Main statements

* `range_cmCoe`: the range of `cmCoe` is the set `{y : E | ∃ M, ∀ L, Var[L; μ] ≤ 1 → L y ≤ M}`.
* `cmCoe_cmOfBounded` and `cmOfBounded_cmCoe`: the two maps `cmCoe` and `cmOfBounded` are inverses
  of each other.

* `norm_cameronMartin_eq_ciSup`: for `x` in the Cameron-Martin space,
  `‖x‖ = ⨆ (L) (_ : Var[L; μ] ≤ 1), L (cmCoe x)`.
* `norm_cmOfBounded`: for `y` in `E` with bounded Cameron-Martin norm,
  `‖cmOfBounded μ y‖ = ⨆ (L) (_ : Var[L; μ] ≤ 1), L y`.

## Implementation notes

We build the Cameron-Martin space for any finite measure with a finite second moment, not only for
Gaussian measures. We do so only because we can write the definition with that weaker hypothesis:
we are not aware of any use of the Cameron-Martin space for non-Gaussian measures.

## References

* V. I. Bogachev, *Gaussian Measures*, AMS, 1998.
* H.-H. Kuo, *Gaussian Measures in Banach Spaces*, LNM 463, Springer, 1975.

## Tags

Gaussian measure, Cameron–Martin space, RKHS

-/

--@[expose] public section

open MeasureTheory ProbabilityTheory NormedSpace UniformSpace
open scoped MeasureTheory ProbabilityTheory ENNReal NNReal Real Topology InnerProductSpace

variable {M R F : Type*} [Ring R] [NormedAddCommGroup M] [Module R M]
    [CompleteSpace M] [UniformContinuousConstSMul R M]
    [UniformSpace F] [AddCommGroup F] [Module R F] [T2Space F] [CompleteSpace F]
    {s : Submodule R M}

namespace ProbabilityTheory

/-- A finite measure `μ` has a finite second moment, encoded as `MemLp id 2 μ`.

This is the minimal hypothesis needed to define `cameronMartin μ` via the RKHS construction. -/
class HasTwoMoments {E : Type*} {_ : MeasurableSpace E} [ENorm E] [TopologicalSpace E]
    (μ : Measure E) extends IsFiniteMeasure μ where
  memLp_two : MemLp id 2 μ

lemma memLp_two_id {E : Type*} {_ : MeasurableSpace E} [ENorm E] [TopologicalSpace E]
    {μ : Measure E} [HasTwoMoments μ] : MemLp id 2 μ := HasTwoMoments.memLp_two

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace E]
  {μ : Measure E} {p : ℝ≥0∞} [Fact (1 ≤ p)] {y : E}

instance [SecondCountableTopology E] [IsGaussian μ] : HasTwoMoments μ where
  memLp_two := IsGaussian.memLp_id μ 2 (by simp)

lemma _root_.ContinuousLinearMap.memLp_two {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {_ : MeasurableSpace E}
    {μ : Measure E} [HasTwoMoments μ] (L : StrongDual ℝ E) :
    MemLp L 2 μ := L.comp_memLp' memLp_two_id

/-!
### `StrongDual.centeredToLp` (no stubs)

In the pinned `mathlib`, the basic map from the dual into `Lp` is called `StrongDual.toLp`
and lives in `Mathlib.Probability.Moments.CovarianceBilinDual`.

For the Cameron–Martin construction we need the *centered* map
\(L \mapsto (x \mapsto L (x - \mu[id]))\) into `Lp ℝ 2 μ`.
We implement it as `StrongDual.toLp μ 2` minus the constant function `L (μ[id])`.
-/

namespace StrongDual

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace E] {μ : Measure E}

-- Needed to use `StrongDual.toLp μ 2`.
instance instFact_one_le_two : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by simp⟩

/-- Centered map from the dual to `Lp`, at `p = 2`.

This is the honest definition \(L \mapsto (x \mapsto L(x - \mu[id]))\), implemented as
`StrongDual.toLp μ 2` minus the constant function `L (μ[id])`. -/
noncomputable
def centeredToLp (μ : Measure E) [IsFiniteMeasure μ] :
    _root_.StrongDual ℝ E →L[ℝ] Lp ℝ 2 μ :=
  (_root_.StrongDual.toLp μ 2) -
    (ContinuousLinearMap.smulRight (ContinuousLinearMap.apply ℝ ℝ (∫ x : E, x ∂μ))
      (Lp.const 2 μ (1 : ℝ)))

omit [CompleteSpace E] in
/-- Pointwise a.e. formula for `StrongDual.centeredToLp`. -/
lemma centeredToLp_apply [IsFiniteMeasure μ] (h : MemLp id 2 μ) (L : _root_.StrongDual ℝ E) :
    (StrongDual.centeredToLp (E := E) μ L : E → ℝ) =ᵐ[μ] fun x ↦ L x - L (∫ y : E, y ∂μ) := by
  have h_toLp :
      ((StrongDual.toLp (μ := μ) 2 L : Lp ℝ 2 μ) : E → ℝ) =ᵐ[μ] fun x ↦ L x := by
    simp [StrongDual.toLp_apply (μ := μ) (p := (2 : ℝ≥0∞)) h]
    simpa using (MemLp.coeFn_toLp (h.continuousLinearMap_comp L))
  -- The constant term is a.e. the constant function `L (∫ y, y ∂μ)`.
  let c : ℝ := L (∫ y : E, y ∂μ)
  have h_one : ((AEEqFun.const E (1 : ℝ) : E →ₘ[μ] ℝ) : E → ℝ) =ᵐ[μ] fun _ => (1 : ℝ) := by
    simpa [Function.const] using (AEEqFun.coeFn_const (μ := μ) (α := E) (b := (1 : ℝ)))
  have h_const :
      (((ContinuousLinearMap.smulRight (ContinuousLinearMap.apply ℝ ℝ (∫ y : E, y ∂μ))
              (Lp.const 2 μ (1 : ℝ))) L : Lp ℝ 2 μ) : E → ℝ)
        =ᵐ[μ] fun _ => c := by
    have h_smul :
        (((ContinuousLinearMap.smulRight (ContinuousLinearMap.apply ℝ ℝ (∫ y : E, y ∂μ))
                (Lp.const 2 μ (1 : ℝ))) L : Lp ℝ 2 μ) : E → ℝ)
          =ᵐ[μ] fun x : E => c • ((Lp.const 2 μ (1 : ℝ) : Lp ℝ 2 μ) : E → ℝ) x := by
      simpa [c, ContinuousLinearMap.smulRight_apply] using
        (Lp.coeFn_smul (c := (ContinuousLinearMap.apply ℝ ℝ (∫ y : E, y ∂μ)) L)
          (f := (Lp.const 2 μ (1 : ℝ) : Lp ℝ 2 μ)))
    filter_upwards [h_smul, h_one] with x hx hx1
    simpa [hx1, c] using hx
  have h_sub :
      ((StrongDual.centeredToLp (E := E) μ L : Lp ℝ 2 μ) : E → ℝ)
        =ᵐ[μ] fun x => L x - c := by
    have hxSub :
        ((StrongDual.centeredToLp (E := E) μ L : Lp ℝ 2 μ) : E → ℝ)
          =ᵐ[μ]
            ((StrongDual.toLp (μ := μ) 2 L : Lp ℝ 2 μ) : E → ℝ)
              - (((ContinuousLinearMap.smulRight (ContinuousLinearMap.apply ℝ ℝ (∫ y : E, y ∂μ))
                    (Lp.const 2 μ (1 : ℝ))) L : Lp ℝ 2 μ) : E → ℝ) := by
      simpa [StrongDual.centeredToLp, Pi.sub_apply] using
        (Lp.coeFn_sub (StrongDual.toLp (μ := μ) 2 L)
          ((ContinuousLinearMap.smulRight (ContinuousLinearMap.apply ℝ ℝ (∫ y : E, y ∂μ))
            (Lp.const 2 μ (1 : ℝ))) L))
    filter_upwards [hxSub, h_toLp, h_const] with x hx hxLp hxC
    have hxLp' :
        ((StrongDual.toLp (μ := μ) 2 L : Lp ℝ 2 μ) : E → ℝ) x = L x := by
      simpa using hxLp
    have hxC' :
        ((c • (Lp.const 2 μ (1 : ℝ)) : Lp ℝ 2 μ) : E → ℝ) x = c := by
      simpa [c, ContinuousLinearMap.smulRight_apply] using hxC
    simpa [Pi.sub_apply, hxLp', hxC', c] using hx
  simpa [c, Pi.sub_apply] using h_sub

/-- The `L²` inner product of centered dual functionals is the covariance bilinear form. -/
lemma centeredToLp_two_inner [IsFiniteMeasure μ] (h : MemLp id 2 μ) (L₁ L₂ : _root_.StrongDual ℝ E) :
    ⟪StrongDual.centeredToLp (E := E) μ L₁, StrongDual.centeredToLp (E := E) μ L₂⟫_ℝ =
      covarianceBilinDual μ L₁ L₂ := by
  have h1 := centeredToLp_apply (μ := μ) h L₁
  have h2 := centeredToLp_apply (μ := μ) h L₂
  have hinter :
      ⟪StrongDual.centeredToLp (E := E) μ L₁, StrongDual.centeredToLp (E := E) μ L₂⟫_ℝ
        =
        ∫ x : E,
          ((StrongDual.centeredToLp (E := E) μ L₂ : Lp ℝ 2 μ) : E → ℝ) x *
            ((StrongDual.centeredToLp (E := E) μ L₁ : Lp ℝ 2 μ) : E → ℝ) x ∂μ := by
    simp [L2.inner_def, RCLike.inner_apply, conj_trivial]
  have hmul :
      (fun x : E =>
          ((StrongDual.centeredToLp (E := E) μ L₂ : Lp ℝ 2 μ) : E → ℝ) x *
            ((StrongDual.centeredToLp (E := E) μ L₁ : Lp ℝ 2 μ) : E → ℝ) x)
        =ᵐ[μ] fun x : E =>
          (L₂ x - L₂ (∫ y : E, y ∂μ)) * (L₁ x - L₁ (∫ y : E, y ∂μ)) := by
    filter_upwards [h1, h2] with x hx1 hx2
    simp [hx1, hx2]
  have hinter' :
      ⟪StrongDual.centeredToLp (E := E) μ L₁, StrongDual.centeredToLp (E := E) μ L₂⟫_ℝ
        = ∫ x : E, (L₂ x - L₂ (∫ y : E, y ∂μ)) * (L₁ x - L₁ (∫ y : E, y ∂μ)) ∂μ := by
    refine hinter.trans ?_
    exact integral_congr_ae hmul
  have hmean (L : StrongDual ℝ E) : μ[L] = L (∫ x : E, x ∂μ) :=
    L.integral_comp_comm (h.integrable (by simp))
  have hcov := covarianceBilinDual_apply (μ := μ) (h := h) L₁ L₂
  have hcov' :
      covarianceBilinDual μ L₁ L₂
        =
        ∫ x : E, (L₁ x - L₁ (∫ y : E, y ∂μ)) * (L₂ x - L₂ (∫ y : E, y ∂μ)) ∂μ := by
    simpa [hmean] using hcov
  have hswap :
      (∫ x : E, (L₁ x - L₁ (∫ y : E, y ∂μ)) * (L₂ x - L₂ (∫ y : E, y ∂μ)) ∂μ)
        =
        ∫ x : E, (L₂ x - L₂ (∫ y : E, y ∂μ)) * (L₁ x - L₁ (∫ y : E, y ∂μ)) ∂μ := by
    refine integral_congr_ae ?_
    refine ae_of_all _ (fun x => by simp [mul_comm])
  have : ∫ x : E, (L₂ x - L₂ (∫ y : E, y ∂μ)) * (L₁ x - L₁ (∫ y : E, y ∂μ)) ∂μ
      = covarianceBilinDual μ L₁ L₂ := by
    simpa [hswap] using hcov'.symm
  simpa [hinter'] using this

/-- The `L²` norm of `StrongDual.centeredToLp μ L` squares to the variance `Var[L; μ]`. -/
lemma sq_norm_centeredToLp_two [IsFiniteMeasure μ] (h : MemLp id 2 μ) (L : _root_.StrongDual ℝ E) :
    ‖StrongDual.centeredToLp (E := E) μ L‖ ^ 2 = Var[L; μ] := by
  have hinner := centeredToLp_two_inner (μ := μ) (h := h) L L
  calc
    ‖StrongDual.centeredToLp (E := E) μ L‖ ^ 2
        = ⟪StrongDual.centeredToLp (E := E) μ L, StrongDual.centeredToLp (E := E) μ L⟫_ℝ := by
            simp
    _ = covarianceBilinDual μ L L := hinner
    _ = Var[L; μ] := covarianceBilinDual_self_eq_variance (μ := μ) h L

end StrongDual

section CameronMartinSpace

/-- The Cameron–Martin space associated to a measure `μ` with finite second moment.

It is the closure of the range of the centered embedding
`StrongDual.centeredToLp μ : StrongDual ℝ E →L[ℝ] Lp ℝ 2 μ`, viewed as a submodule of `Lp`. -/
noncomputable
def cameronMartin (μ : Measure E) [HasTwoMoments μ] : Submodule ℝ (Lp ℝ 2 μ) :=
  (LinearMap.range (StrongDual.centeredToLp (E := E) μ).toLinearMap).topologicalClosure

variable [HasTwoMoments μ]

noncomputable
instance :
    Coe (LinearMap.range (StrongDual.centeredToLp (E := E) μ).toLinearMap) (cameronMartin μ) :=
  ⟨fun x => coeClosure (s := LinearMap.range (StrongDual.centeredToLp (E := E) μ).toLinearMap) x⟩

noncomputable
instance instCoeFun : CoeFun (cameronMartin μ) (fun _ ↦ E → ℝ) := ⟨fun f ↦ (f : E → ℝ)⟩

noncomputable instance : NormedAddCommGroup (cameronMartin μ) := by
  unfold cameronMartin
  infer_instance

noncomputable instance : InnerProductSpace ℝ (cameronMartin μ) := by
  unfold cameronMartin
  infer_instance

noncomputable instance : CompleteSpace (cameronMartin μ) := by
  unfold cameronMartin
  infer_instance

instance [SecondCountableTopology E] (μ : Measure E) [HasTwoMoments μ] :
    SecondCountableTopology (cameronMartin μ) := by
  have : Fact (2 ≠ ∞) := ⟨by simp⟩
  exact TopologicalSpace.Subtype.secondCountableTopology _

/-- Inclusion from the StrongDual into the Cameron-Martin space, as a linear map. -/
noncomputable
def cmOfDual (μ : Measure E) [HasTwoMoments μ] : StrongDual ℝ E →ₗ[ℝ] cameronMartin μ :=
  (coeClosureCLM _).toLinearMap.comp ((StrongDual.centeredToLp (E := E) μ).toLinearMap.rangeRestrict)

noncomputable
instance : Coe (StrongDual ℝ E) (cameronMartin μ) := ⟨cmOfDual μ⟩

omit [CompleteSpace E] in
lemma cmOfDual_apply (L : StrongDual ℝ E) :
    cmOfDual μ L = (⟨StrongDual.centeredToLp (E := E) μ L, LinearMap.mem_range.mpr ⟨L, rfl⟩⟩ :
        LinearMap.range (StrongDual.centeredToLp (E := E) μ).toLinearMap) := rfl

lemma cmOfDual_inner (L₁ L₂ : StrongDual ℝ E) :
    ⟪cmOfDual μ L₁, cmOfDual μ L₂⟫_ℝ = covarianceBilinDual μ L₁ L₂ := by
  simpa [cmOfDual_apply, Submodule.coe_inner] using
    (StrongDual.centeredToLp_two_inner (μ := μ) (h := memLp_two_id) L₁ L₂)

lemma norm_cmOfDual (L : StrongDual ℝ E) : ‖cmOfDual μ L‖ = √Var[L; μ] := by
  rw [norm_eq_sqrt_real_inner, cmOfDual_inner, covarianceBilinDual_self_eq_variance memLp_two_id]

lemma sq_norm_cmOfDual (L : StrongDual ℝ E) : ‖cmOfDual μ L‖ ^ 2 = Var[L; μ] := by
  rw [← real_inner_self_eq_norm_sq, cmOfDual_inner,
    covarianceBilinDual_self_eq_variance memLp_two_id]

omit [CompleteSpace E] in
/-- `cmOfDual` has dense range in the Cameron–Martin space. -/
lemma denseRange_cmOfDual (μ : Measure E) [HasTwoMoments μ] :
    DenseRange (fun L : StrongDual ℝ E => (cmOfDual (μ := μ) L : cameronMartin μ)) := by
  let s : Submodule ℝ (Lp ℝ 2 μ) :=
    LinearMap.range (StrongDual.centeredToLp (E := E) μ).toLinearMap
  have hg : DenseRange (coeClosureCLM s) := denseRange_coeClosureCLM s
  have hf :
      DenseRange (fun L : StrongDual ℝ E =>
        ((StrongDual.centeredToLp (E := E) μ).toLinearMap.rangeRestrict L : s)) := by
    refine (Function.Surjective.denseRange ?_)
    rintro ⟨x, hx⟩
    rcases LinearMap.mem_range.mp hx with ⟨L, rfl⟩
    exact ⟨L, rfl⟩
  have hcomp :
      DenseRange ((coeClosureCLM s) ∘ fun L : StrongDual ℝ E =>
        ((StrongDual.centeredToLp (E := E) μ).toLinearMap.rangeRestrict L : s)) :=
    DenseRange.comp (g := coeClosureCLM s)
      (f := fun L : StrongDual ℝ E =>
        ((StrongDual.centeredToLp (E := E) μ).toLinearMap.rangeRestrict L : s))
      hg hf (coeClosureCLM s).continuous
  simpa [cmOfDual, cameronMartin, s, Function.comp] using hcomp

end CameronMartinSpace

section cmOfBounded

/-! We build a map from the elements of `E` with finite Cameron-Martin norm to
the Cameron-Martin space. -/

variable [HasTwoMoments μ]

namespace CameronMartinAux -- namespace for auxiliary definitions and lemmas

/-- For an `L²` function `x` in the range of `StrongDual.centeredToLp μ`, evaluate `x` at `y : E`.

This is done by picking `L : StrongDual ℝ E` mapping to `x` and returning `L y`. It is an
auxiliary definition for `cmEval`. -/
noncomputable
def evalL2 (μ : Measure E) [HasTwoMoments μ] (y : E)
    (x : LinearMap.range (StrongDual.centeredToLp (E := E) μ).toLinearMap) : ℝ :=
  (LinearMap.mem_range.mp x.2).choose y

lemma norm_eval_le_norm_centeredToLp_mul (hy : ∃ M, ∀ L : StrongDual ℝ E, Var[L; μ] ≤ 1 → L y ≤ M)
    (L : StrongDual ℝ E) :
    ‖L y‖ ≤ ‖StrongDual.centeredToLp (E := E) μ L‖
      * ⨆ (L' : StrongDual ℝ E) (_ : Var[L'; μ] ≤ 1), L' y := by
  simp_rw [← StrongDual.sq_norm_centeredToLp_two (μ := μ) memLp_two_id,
    sq_le_one_iff_abs_le_one, abs_norm] at hy ⊢
  exact norm_eval_le_norm_mul_ciSup (StrongDual.centeredToLp (E := E) μ).toLinearMap hy L

lemma norm_evalL2_le (hy : ∃ M, ∀ L : StrongDual ℝ E, Var[L; μ] ≤ 1 → L y ≤ M)
    (x : LinearMap.range (StrongDual.centeredToLp (E := E) μ).toLinearMap) :
    ‖evalL2 μ y x‖ ≤ ‖x‖ * ⨆ (L : StrongDual ℝ E) (_ : Var[L; μ] ≤ 1), L y := by
  simp only [AddSubgroupClass.coe_norm]
  conv_rhs => rw [← (LinearMap.mem_range.mp x.2).choose_spec]
  exact norm_eval_le_norm_centeredToLp_mul hy (LinearMap.mem_range.mp x.2).choose

lemma eval_eq_of_centeredToLp_eq (hy : ∃ M, ∀ L : StrongDual ℝ E, Var[L; μ] ≤ 1 → L y ≤ M)
    (L L' : StrongDual ℝ E)
    (hL : StrongDual.centeredToLp (E := E) μ L = StrongDual.centeredToLp (E := E) μ L') :
    L y = L' y := by
  rw [← sub_eq_zero, ← Pi.sub_apply, ← norm_eq_zero]
  suffices ‖⇑(L - L') y‖ = 0 by simpa
  refine le_antisymm ?_ (by positivity)
  refine (norm_eval_le_norm_centeredToLp_mul hy _ (μ := μ)).trans ?_
  simp [hL]

lemma evalL2_eq (hy : ∃ M, ∀ L : StrongDual ℝ E, Var[L; μ] ≤ 1 → L y ≤ M)
    (x : LinearMap.range (StrongDual.centeredToLp (E := E) μ).toLinearMap)
    {L : StrongDual ℝ E}
    (hL : StrongDual.centeredToLp (E := E) μ L = (x : Lp ℝ 2 μ)) :
    evalL2 μ y x = L y := by
  rw [evalL2]
  refine eval_eq_of_centeredToLp_eq hy (LinearMap.mem_range.mp x.2).choose L ?_
  have hchoose :
      StrongDual.centeredToLp (E := E) μ (LinearMap.mem_range.mp x.2).choose = (x : Lp ℝ 2 μ) := by
    simpa using (LinearMap.mem_range.mp x.2).choose_spec
  calc
    StrongDual.centeredToLp (E := E) μ (LinearMap.mem_range.mp x.2).choose = (x : Lp ℝ 2 μ) := hchoose
    _ = StrongDual.centeredToLp (E := E) μ L := by simpa using hL.symm

lemma evalL2_centeredToLp_eq (hy : ∃ M, ∀ L : StrongDual ℝ E, Var[L; μ] ≤ 1 → L y ≤ M)
    (L : StrongDual ℝ E) :
    evalL2 μ y
        ⟨StrongDual.centeredToLp (E := E) μ L, LinearMap.mem_range.mpr ⟨L, rfl⟩⟩ = L y :=
  evalL2_eq hy _ (by simp)

end CameronMartinAux

open CameronMartinAux

/-- Evaluation functional on the Cameron–Martin space.

Given `y : E` with bounded Cameron–Martin norm (i.e. `∃ M, ∀ L, Var[L; μ] ≤ 1 → L y ≤ M`),
`cmEval μ y hy` is the continuous linear functional on `cameronMartin μ` obtained by extending
evaluation from the dense range of `StrongDual.centeredToLp μ`.

It satisfies `cmEval μ y hy (cmOfDual μ L) = L y`. -/
noncomputable
def cmEval (μ : Measure E) [HasTwoMoments μ] (y : E)
    (hy : ∃ M, ∀ L : StrongDual ℝ E, Var[L; μ] ≤ 1 → L y ≤ M) :
    StrongDual ℝ (cameronMartin μ) :=
  closureExtensionCLM (LinearMap.range (StrongDual.centeredToLp (E := E) μ).toLinearMap) <|
  LinearMap.mkContinuous
    { toFun x := evalL2 μ y x
      map_add' x₁ x₂ := by
        obtain ⟨L₁, hL₁⟩ := LinearMap.mem_range.mp x₁.2
        obtain ⟨L₂, hL₂⟩ := LinearMap.mem_range.mp x₂.2
        rw [evalL2_eq hy x₁ hL₁, evalL2_eq hy x₂ hL₂, evalL2_eq hy (x₁ + x₂) (L := L₁ + L₂)]
        · simp
        · have hL₁' : StrongDual.centeredToLp (E := E) μ L₁ = (x₁ : Lp ℝ 2 μ) := by
            simpa using hL₁
          have hL₂' : StrongDual.centeredToLp (E := E) μ L₂ = (x₂ : Lp ℝ 2 μ) := by
            simpa using hL₂
          calc
            StrongDual.centeredToLp (E := E) μ (L₁ + L₂)
                = StrongDual.centeredToLp (E := E) μ L₁ + StrongDual.centeredToLp (E := E) μ L₂ := by
                    simp
            _ = (x₁ : Lp ℝ 2 μ) + (x₂ : Lp ℝ 2 μ) := by simp [hL₁', hL₂']
            _ = (x₁ + x₂ : LinearMap.range (StrongDual.centeredToLp (E := E) μ).toLinearMap) := rfl
      map_smul' r x := by
        obtain ⟨L, hL⟩ := LinearMap.mem_range.mp x.2
        rw [evalL2_eq hy x hL, evalL2_eq hy (r • x) (L := r • L)]
        · simp
        · have hL' : StrongDual.centeredToLp (E := E) μ L = (x : Lp ℝ 2 μ) := by
            simpa using hL
          calc
            StrongDual.centeredToLp (E := E) μ (r • L) = r • StrongDual.centeredToLp (E := E) μ L := by
              simp
            _ = r • (x : Lp ℝ 2 μ) := by simp [hL']
            _ = (r • x : LinearMap.range (StrongDual.centeredToLp (E := E) μ).toLinearMap) := rfl }
    (⨆ (L' : StrongDual ℝ E) (_ : Var[L'; μ] ≤ 1), L' y) fun x ↦ by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, AddSubgroupClass.coe_norm]
    rw [mul_comm]
    exact norm_evalL2_le hy x

lemma cmEval_cmOfDual (hy : ∃ M, ∀ L : StrongDual ℝ E, Var[L; μ] ≤ 1 → L y ≤ M)
    (L : StrongDual ℝ E) :
    cmEval μ y hy (cmOfDual μ L) = L y := by
  rw [cmOfDual_apply, cmEval]
  unfold cameronMartin
  simp only [closureExtensionCLM_coe, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
  rw [evalL2_centeredToLp_eq hy]

/-- Map `E → cameronMartin μ` defined for points with bounded Cameron–Martin norm.

If `y : E` has bounded Cameron–Martin norm, `cmOfBounded μ y` is the element corresponding to the
evaluation functional at `y`. Otherwise it is defined to be `0`. -/
noncomputable
def cmOfBounded (μ : Measure E) [HasTwoMoments μ] (y : E)
    [Decidable (∃ M, ∀ L : StrongDual ℝ E, Var[L; μ] ≤ 1 → L y ≤ M)] :
    cameronMartin μ :=
  if hy : ∃ M, ∀ L : StrongDual ℝ E, Var[L; μ] ≤ 1 → L y ≤ M
    then (InnerProductSpace.toDual ℝ (cameronMartin μ)).symm (cmEval μ y hy)
    else 0

variable [Decidable (∃ M, ∀ L : StrongDual ℝ E, Var[L; μ] ≤ 1 → L y ≤ M)]

lemma cmOfBounded_def (hy : ∃ M, ∀ L : StrongDual ℝ E, Var[L; μ] ≤ 1 → L y ≤ M) :
    cmOfBounded μ y = (InnerProductSpace.toDual ℝ (cameronMartin μ)).symm (cmEval μ y hy) := by
  simp [cmOfBounded, hy]

lemma cmEval_apply (hy : ∃ M, ∀ L : StrongDual ℝ E, Var[L; μ] ≤ 1 → L y ≤ M) (x : cameronMartin μ) :
    cmEval μ y hy x = ⟪x, cmOfBounded μ y⟫_ℝ := by
  rw [cmOfBounded_def hy, real_inner_comm, InnerProductSpace.toDual_symm_apply]

end cmOfBounded

section CmCoe

/-! We build an injective continuous linear map from the Cameron-Martin space to the elements
of `E` with finite Cameron-Martin norm. This is an inverse of `CameronMartin.cmOfBounded`. -/

variable [SecondCountableTopology E] [HasTwoMoments μ]

namespace CameronMartinAux -- namespace for auxiliary definitions and lemmas

/-- From `x` in the range of `StrongDual.centeredToLp μ`, build a point of `E` by
`∫ y, L (y - ∫ z, z ∂μ) • (y - ∫ z, z ∂μ) ∂μ` for an arbitrary `L : StrongDual ℝ E` with
`StrongDual.centeredToLp μ L = x`.
This is an auxiliary definition for `CameronMartin.cmCoe`. -/
noncomputable
def toInit (μ : Measure E) [IsFiniteMeasure μ]
    (x : LinearMap.range (StrongDual.centeredToLp (E := E) μ).toLinearMap) : E :=
  ∫ y, (LinearMap.mem_range.mp x.2).choose (y - ∫ z, z ∂μ) • (y - ∫ z, z ∂μ) ∂μ

omit [CompleteSpace E] [SecondCountableTopology E] in
lemma toInit_eq (x : LinearMap.range (StrongDual.centeredToLp (E := E) μ).toLinearMap) {L : StrongDual ℝ E}
    (hL : StrongDual.centeredToLp (E := E) μ L = x) :
    toInit μ x = ∫ y, L (y - ∫ z, z ∂μ) • (y - ∫ z, z ∂μ) ∂μ :=
  calc toInit μ x
  _ = ∫ y, x.1 y • (y - ∫ z, z ∂μ) ∂μ := by
    rw [toInit]
    conv_rhs => rw [← (LinearMap.mem_range.mp x.2).choose_spec]
    refine integral_congr_ae ?_
    filter_upwards [StrongDual.centeredToLp_apply memLp_two_id (LinearMap.mem_range.mp x.2).choose]
      with y hy
    simp [hy]
  _ = ∫ y, StrongDual.centeredToLp (E := E) μ L y • (y - ∫ z, z ∂μ) ∂μ := by rw [hL]
  _ = ∫ y, L (y - ∫ z, z ∂μ) • (y - ∫ z, z ∂μ) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [StrongDual.centeredToLp_apply memLp_two_id L] with y hy
    simp [hy]

lemma apply_toInit (x : LinearMap.range (StrongDual.centeredToLp (E := E) μ).toLinearMap) (L : StrongDual ℝ E) :
    L (toInit μ x)
      = ∫ y, (LinearMap.mem_range.mp x.2).choose (y - ∫ z, z ∂μ) * L (y - ∫ z, z ∂μ) ∂μ := by
  rw [toInit, ← L.integral_comp_comm]
  · simp
  rw [← integrable_norm_iff (by fun_prop)]
  simp only [map_sub, norm_smul]
  refine MemLp.integrable_mul (p := 2) (q := 2) ?_ ?_
  · rw [memLp_norm_iff (by fun_prop)]
    exact (ContinuousLinearMap.memLp_two _).sub (memLp_const _)
  · rw [memLp_norm_iff (by fun_prop)]
    exact MemLp.sub memLp_two_id (memLp_const _)

lemma apply_toInit_eq_inner (x : LinearMap.range (StrongDual.centeredToLp (E := E) μ).toLinearMap)
    (L : StrongDual ℝ E) :
    L (toInit μ x) = ⟪StrongDual.centeredToLp (E := E) μ L, x⟫_ℝ := by
  rw [← (LinearMap.mem_range.mp x.2).choose_spec, L2.inner_def, apply_toInit]
  simp only [RCLike.inner_apply, conj_trivial]
  refine integral_congr_ae ?_
  filter_upwards [StrongDual.centeredToLp_apply memLp_two_id L,
    StrongDual.centeredToLp_apply memLp_two_id (LinearMap.mem_range.mp x.2).choose]
    with y hy₁ hy₂
  simp [hy₁, hy₂]

lemma norm_toInit_le (x : LinearMap.range (StrongDual.centeredToLp (E := E) μ).toLinearMap) :
    ‖toInit μ x‖ ≤ ‖StrongDual.centeredToLp (E := E) μ‖ * ‖x‖ := by
  refine norm_le_dual_bound ℝ _ (by positivity) fun L ↦ ?_
  calc ‖L (toInit μ x)‖
  _ = ‖⟪StrongDual.centeredToLp (E := E) μ L, x⟫_ℝ‖ := by rw [apply_toInit_eq_inner]
  _ ≤ ‖StrongDual.centeredToLp (E := E) μ L‖ * ‖x‖ :=
    norm_inner_le_norm ((StrongDual.centeredToLp (E := E) μ) L) x
  _ ≤ ‖StrongDual.centeredToLp (E := E) μ‖ * ‖L‖ * ‖x‖ := by
    gcongr
    exact (StrongDual.centeredToLp (E := E) μ).le_opNorm L
  _ = ‖StrongDual.centeredToLp (E := E) μ‖ * ‖x‖ * ‖L‖ := by ring

end CameronMartinAux

open CameronMartinAux

/-- Continuous linear map `cameronMartin μ →L[ℝ] E` associated to `μ`.

This map is injective (see `cmCoe_injective`), so it identifies the Cameron–Martin space with a
subspace of `E` endowed with the Cameron–Martin norm. -/
noncomputable
def cmCoe {μ : Measure E} [HasTwoMoments μ] : cameronMartin μ →L[ℝ] E :=
  closureExtensionCLM (LinearMap.range (StrongDual.centeredToLp (E := E) μ).toLinearMap) <|
  LinearMap.mkContinuous
    { toFun x := toInit μ x
      map_add' x y := by
        refine (eq_iff_forall_dual_eq (𝕜 := ℝ)).mpr fun L ↦ ?_
        simp_rw [map_add, apply_toInit_eq_inner, Submodule.coe_add, inner_add_right]
      map_smul' r x := by
        refine (eq_iff_forall_dual_eq (𝕜 := ℝ)).mpr fun L ↦ ?_
        simp_rw [map_smul, apply_toInit_eq_inner, Submodule.coe_smul, inner_smul_right]
        simp }
    ‖StrongDual.centeredToLp (E := E) μ‖ norm_toInit_le

lemma apply_cmCoe_eq_inner (x : cameronMartin μ) (L : StrongDual ℝ E) :
    L (cmCoe x) = ⟪cmOfDual μ L, x⟫_ℝ := by
  -- Work on `s := range (centeredToLp)` and use density of `s` in its closure.
  let s : Submodule ℝ (Lp ℝ 2 μ) := LinearMap.range (StrongDual.centeredToLp (E := E) μ).toLinearMap
  have hfun :
      (fun z : s.topologicalClosure => L (cmCoe (μ := μ) z))
        = fun z : s.topologicalClosure => ⟪(cmOfDual μ L : s.topologicalClosure), z⟫_ℝ := by
    refine funext_topologicalClosure
      (s := s)
      (hf := ((L : StrongDual ℝ E).comp (cmCoe (μ := μ))).continuous)
      (hg := (continuous_const.inner continuous_id))
      ?_
    intro a
    have hcm : cmCoe (μ := μ) (coeClosureCLM s a) = toInit μ a := by
      simpa [cmCoe, closureExtensionCLM, coeClosureCLM, LinearMap.mkContinuous_apply] using
        (closureExtensionCLM_coe (s := s)
          (f := LinearMap.mkContinuous
            { toFun x := toInit μ x
              map_add' x y := by
                refine (eq_iff_forall_dual_eq (𝕜 := ℝ)).mpr fun L ↦ ?_
                simp_rw [map_add, apply_toInit_eq_inner, Submodule.coe_add, inner_add_right]
              map_smul' r x := by
                refine (eq_iff_forall_dual_eq (𝕜 := ℝ)).mpr fun L ↦ ?_
                simp_rw [map_smul, apply_toInit_eq_inner, Submodule.coe_smul, inner_smul_right]
                simp }
            ‖StrongDual.centeredToLp (E := E) μ‖ norm_toInit_le) a)
    have hleft : L (cmCoe (μ := μ) (coeClosureCLM s a)) = L (toInit μ a) := by simp [hcm]
    have hright :
        ⟪(cmOfDual μ L : s.topologicalClosure), coeClosureCLM s a⟫_ℝ
          = ⟪StrongDual.centeredToLp (E := E) μ L, a⟫_ℝ := by
      simp [Submodule.coe_inner]
      have hcoe :
          ((cmOfDual μ L : cameronMartin μ) : Lp ℝ 2 μ) = StrongDual.centeredToLp (E := E) μ L := by
        simp [cmOfDual, cameronMartin, coeClosureCLM, coeClosure]
      have ha : ((coeClosureCLM s a : s.topologicalClosure) : Lp ℝ 2 μ) = (a : Lp ℝ 2 μ) := by
        rfl
      simp [hcoe, ha]
    simpa [hleft, hright] using (apply_toInit_eq_inner (μ := μ) (x := a) L)
  simpa [cameronMartin, s] using congrArg (fun f => f x) hfun

lemma eq_zero_of_cmCoe_eq_zero {x : cameronMartin μ}
    (h : cmCoe x = 0) :
    x = 0 := by
  -- Let `K` be the range of `cmOfDual`. This is dense in the Cameron–Martin space.
  let K : Submodule ℝ (cameronMartin μ) := LinearMap.range (cmOfDual (μ := μ))
  have hK_dense : Dense (K : Set (cameronMartin μ)) := by
    have hd : DenseRange (fun L : StrongDual ℝ E => (cmOfDual (μ := μ) L : cameronMartin μ)) :=
      denseRange_cmOfDual (E := E) (μ := μ)
    have h_dense_range : Dense (Set.range fun L : StrongDual ℝ E => (cmOfDual (μ := μ) L : cameronMartin μ)) := by
      refine dense_iff_closure_eq.2 ?_
      ext z
      constructor
      · intro _; simp
      · intro _; exact hd z
    have hKset :
        (K : Set (cameronMartin μ))
          = Set.range fun L : StrongDual ℝ E => (cmOfDual (μ := μ) L : cameronMartin μ) := by
      ext z
      simp [K, LinearMap.mem_range]
    simpa [hKset] using h_dense_range
  have h_inner : ∀ v : K, ⟪(v : cameronMartin μ), x⟫_ℝ = 0 := by
    intro v
    rcases v.2 with ⟨L, hLv⟩
    have hL0 : L (cmCoe x) = 0 := by simp [h]
    have hinner : ⟪cmOfDual μ L, x⟫_ℝ = 0 := by
      have := apply_cmCoe_eq_inner (μ := μ) (x := x) L
      simpa [hL0] using this.symm
    simpa [hLv] using hinner
  exact Dense.eq_zero_of_inner_right (K := K) hK_dense h_inner

lemma cmCoe_injective : Function.Injective (cmCoe (μ := μ)) := by
  intro x y hxy
  have hsub : cmCoe (μ := μ) (x - y) = 0 := by
    simp [map_sub, hxy]
  have : x - y = 0 := eq_zero_of_cmCoe_eq_zero (μ := μ) (x := x - y) hsub
  exact sub_eq_zero.mp this

/-- Any point of the Cameron-Martin space has finite Cameron-Martin norm
`⨆ L (_ : Var[L; μ] ≤ 1), L x` (when seen as a point of the initial space). -/
lemma apply_cmCoe_le_norm (x : cameronMartin μ)
    {L : StrongDual ℝ E} (hL : Var[L; μ] ≤ 1) :
    L (cmCoe x) ≤ ‖x‖ := by
  have hnorm : ‖cmOfDual μ L‖ ≤ 1 := by
    have hsq : ‖cmOfDual μ L‖ ^ 2 ≤ 1 := by
      simpa [(sq_norm_cmOfDual (μ := μ) L).symm] using
        (show Var[L; μ] ≤ 1 from by simpa using hL)
    have habs : |‖cmOfDual μ L‖| ≤ 1 :=
      (sq_le_one_iff_abs_le_one (a := ‖cmOfDual μ L‖)).1 hsq
    simpa [abs_norm] using habs
  calc
    L (cmCoe x) = ⟪cmOfDual μ L, x⟫_ℝ := apply_cmCoe_eq_inner (μ := μ) (x := x) L
    _ ≤ ‖cmOfDual μ L‖ * ‖x‖ := real_inner_le_norm _ _
    _ ≤ 1 * ‖x‖ := by gcongr
    _ = ‖x‖ := by simp

end CmCoe

variable [SecondCountableTopology E] [HasTwoMoments μ]
  [Decidable (∃ M, ∀ L : StrongDual ℝ E, Var[L; μ] ≤ 1 → L y ≤ M)]

@[simp]
lemma cmCoe_cmOfBounded (hy : ∃ M, ∀ L : StrongDual ℝ E, Var[L; μ] ≤ 1 → L y ≤ M) :
    cmCoe (cmOfBounded μ y) = y := by
  refine (eq_iff_forall_dual_eq (𝕜 := ℝ)).mpr fun L ↦ ?_
  have h1 : L (cmCoe (cmOfBounded μ y)) = ⟪cmOfDual μ L, cmOfBounded μ y⟫_ℝ :=
    apply_cmCoe_eq_inner (μ := μ) (x := cmOfBounded μ y) L
  have h2 : ⟪cmOfDual μ L, cmOfBounded μ y⟫_ℝ = L y := by
    have : cmEval μ y hy (cmOfDual μ L) = ⟪cmOfDual μ L, cmOfBounded μ y⟫_ℝ := by
      simp [cmEval_apply (μ := μ) (y := y) hy]
    simpa [this] using (cmEval_cmOfDual (μ := μ) (y := y) hy L)
  simp [h1, h2]

@[simp]
lemma cmOfBounded_cmCoe (x : cameronMartin μ)
    [Decidable (∃ M, ∀ L : StrongDual ℝ E, Var[L; μ] ≤ 1 → L (cmCoe x) ≤ M)] :
    cmOfBounded μ (cmCoe x) = x := by
  have hy : ∃ M, ∀ L : StrongDual ℝ E, Var[L; μ] ≤ 1 → L (cmCoe x) ≤ M := by
    refine ⟨‖x‖, ?_⟩
    intro L hL
    exact apply_cmCoe_le_norm (μ := μ) (x := x) hL
  have hcm : cmCoe (μ := μ) (cmOfBounded μ (cmCoe x)) = cmCoe (μ := μ) x := by
    simp [hy]
  exact cmCoe_injective (μ := μ) hcm

lemma range_cmCoe :
    Set.range (cmCoe (μ := μ))
      = {y : E | ∃ M, ∀ L : StrongDual ℝ E, Var[L; μ] ≤ 1 → L y ≤ M} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨‖x‖, ?_⟩
    intro L hL
    exact apply_cmCoe_le_norm (μ := μ) (x := x) hL
  · intro hy
    classical
    refine ⟨cmOfBounded μ y, ?_⟩
    simpa [hy] using (cmCoe_cmOfBounded (μ := μ) (y := y) hy)

lemma cmOfDual_inner_le_of_norm_cmOfDual_le (x : cameronMartin μ) {L : StrongDual ℝ E}
    (hL : ‖cmOfDual μ L‖ ≤ 1) :
    ⟪cmOfDual μ L, x⟫_ℝ ≤ ⨆ (L : StrongDual ℝ E) (_ : Var[L; μ] ≤ 1), L (cmCoe x) := by
  have h_bdd :
      BddAbove (Set.range fun L : StrongDual ℝ E => ⨆ (_ : Var[L; μ] ≤ 1), L (cmCoe x)) := by
    refine ⟨‖x‖, ?_⟩
    rintro _ ⟨L', rfl⟩
    by_cases hL' : Var[L'; μ] ≤ 1
    · simpa [hL'] using apply_cmCoe_le_norm (μ := μ) (x := x) (L := L') hL'
    · simp [hL']
  have hVar : Var[L; μ] ≤ 1 := by
    have hsq : ‖cmOfDual μ L‖ ^ 2 ≤ 1 := by
      have hmul : ‖cmOfDual μ L‖ * ‖cmOfDual μ L‖ ≤ (1 : ℝ) * 1 :=
        mul_le_mul hL hL (by positivity) (by positivity)
      simpa [pow_two] using hmul
    simpa [← sq_norm_cmOfDual (μ := μ) (L := L)] using hsq
  have hSup :
      L (cmCoe x) ≤ ⨆ (L : StrongDual ℝ E) (_ : Var[L; μ] ≤ 1), L (cmCoe x) := by
    refine le_ciSup_of_le h_bdd L ?_
    simp [hVar]
  have hinner : ⟪cmOfDual μ L, x⟫_ℝ = L (cmCoe x) := by
    simpa using (apply_cmCoe_eq_inner (μ := μ) (x := x) L).symm
  simpa [hinner] using hSup

lemma cmOfDual_inner_le_mul (x : cameronMartin μ) (L : StrongDual ℝ E) :
    ⟪cmOfDual μ L, x⟫_ℝ
      ≤ ‖cmOfDual μ L‖ * ⨆ (L : StrongDual ℝ E) (_ : Var[L; μ] ≤ 1), L (cmCoe x) := by
  classical
  by_cases h0 : ‖cmOfDual μ L‖ = 0
  · have hcm : cmOfDual μ L = 0 := by
      simpa [norm_eq_zero] using h0
    simp [hcm]
  · set a : ℝ := ‖cmOfDual μ L‖
    have ha_pos : 0 < a := by
      have hL0 : cmOfDual μ L ≠ 0 := by
        intro hL0
        apply h0
        simp [a, hL0]
      simpa [a] using (norm_pos_iff.mpr hL0)
    set r : ℝ := a⁻¹
    have hr : ‖cmOfDual μ (r • L)‖ ≤ 1 := by
      have hnorm : ‖cmOfDual μ (r • L)‖ = 1 := by
        calc
          ‖cmOfDual μ (r • L)‖ = ‖r • cmOfDual μ L‖ := by simp [map_smul]
          _ = |r| * ‖cmOfDual μ L‖ := by simp [norm_smul]
          _ = 1 := by
              simp [r, a]
              aesop
      exact le_of_eq hnorm
    have hnormed :
        ⟪cmOfDual μ (r • L), x⟫_ℝ
          ≤ ⨆ (L : StrongDual ℝ E) (_ : Var[L; μ] ≤ 1), L (cmCoe x) :=
      cmOfDual_inner_le_of_norm_cmOfDual_le (μ := μ) (x := x) hr
    have hmul := mul_le_mul_of_nonneg_left hnormed (by positivity : 0 ≤ a)
    have hrec : a • cmOfDual μ (r • L) = cmOfDual μ L := by
      calc
        a • cmOfDual μ (r • L) = a • (r • cmOfDual μ L) := by simp [map_smul]
        _ = (a * r) • cmOfDual μ L := by simp [smul_smul]
        _ = (1 : ℝ) • cmOfDual μ L := by simp [r, ha_pos.ne']
        _ = cmOfDual μ L := by simp
    have hscale : a * ⟪cmOfDual μ (r • L), x⟫_ℝ = ⟪cmOfDual μ L, x⟫_ℝ := by
      calc
        a * ⟪cmOfDual μ (r • L), x⟫_ℝ = ⟪a • cmOfDual μ (r • L), x⟫_ℝ := by
          simp [inner_smul_left]
        _ = ⟪cmOfDual μ L, x⟫_ℝ := by
          simpa using congrArg (fun v => ⟪v, x⟫_ℝ) hrec
    have : ⟪cmOfDual μ L, x⟫_ℝ ≤ a * ⨆ (L : StrongDual ℝ E) (_ : Var[L; μ] ≤ 1), L (cmCoe x) := by
      calc
        ⟪cmOfDual μ L, x⟫_ℝ = a * ⟪cmOfDual μ (r • L), x⟫_ℝ := by
          simpa using hscale.symm
        _ ≤ a * ⨆ (L : StrongDual ℝ E) (_ : Var[L; μ] ≤ 1), L (cmCoe x) := hmul
    simpa [a, mul_comm, mul_left_comm, mul_assoc] using this

omit [CompleteSpace E] [SecondCountableTopology E] in
/-- Closedness helper used in `inner_cameronMartin_le_mul_ciSup`. -/
lemma isClosed_setOf_inner_le_norm_mul (x : cameronMartin μ) (S : ℝ) :
    IsClosed {y : cameronMartin μ | ⟪y, x⟫_ℝ ≤ ‖y‖ * S} := by
  have hcont1 : Continuous fun y : cameronMartin μ => ⟪y, x⟫_ℝ :=
    continuous_id.inner continuous_const
  have hcont2 : Continuous fun y : cameronMartin μ => ‖y‖ * S :=
    continuous_norm.mul continuous_const
  exact isClosed_le hcont1 hcont2

lemma inner_cameronMartin_le_mul_ciSup (x y : cameronMartin μ) :
    ⟪y, x⟫_ℝ ≤ ‖y‖ * ⨆ (L : StrongDual ℝ E) (_ : Var[L; μ] ≤ 1), L (cmCoe x) := by
  let S : ℝ := ⨆ (L : StrongDual ℝ E) (_ : Var[L; μ] ≤ 1), L (cmCoe x)
  have hd : DenseRange (fun L : StrongDual ℝ E => (cmOfDual (μ := μ) L : cameronMartin μ)) :=
    denseRange_cmOfDual (E := E) (μ := μ)
  have hClosed :
      IsClosed {y : cameronMartin μ | ⟪y, x⟫_ℝ ≤ ‖y‖ * S} :=
    isClosed_setOf_inner_le_norm_mul (x := x) (S := S)
  have hOnRange : ∀ L : StrongDual ℝ E, (⟪cmOfDual μ L, x⟫_ℝ ≤ ‖cmOfDual μ L‖ * S) := by
    intro L
    simpa [S] using (cmOfDual_inner_le_mul (μ := μ) (x := x) L)
  refine DenseRange.induction_on (e := fun L : StrongDual ℝ E => (cmOfDual (μ := μ) L : cameronMartin μ))
    hd (p := fun y : cameronMartin μ => ⟪y, x⟫_ℝ ≤ ‖y‖ * S) y hClosed ?_
  intro L
  simpa [S] using hOnRange L

lemma norm_cameronMartin_eq_ciSup (x : cameronMartin μ) :
    ‖x‖ = ⨆ (L : StrongDual ℝ E) (_ : Var[L; μ] ≤ 1), L (cmCoe x) := by
  let S : ℝ := ⨆ (L : StrongDual ℝ E) (_ : Var[L; μ] ≤ 1), L (cmCoe x)
  have hS_nonneg : 0 ≤ S := by
    have h_bdd :
        BddAbove (Set.range fun L : StrongDual ℝ E => ⨆ (_ : Var[L; μ] ≤ 1), L (cmCoe x)) := by
      refine ⟨‖x‖, ?_⟩
      rintro _ ⟨L', rfl⟩
      by_cases hL' : Var[L'; μ] ≤ 1
      · simpa [hL'] using apply_cmCoe_le_norm (μ := μ) (x := x) (L := L') hL'
      · simp [hL']
    have : (0 : ℝ) ≤ ⨆ (L : StrongDual ℝ E) (_ : Var[L; μ] ≤ 1), L (cmCoe x) := by
      refine le_ciSup_of_le h_bdd (0 : StrongDual ℝ E) ?_
      simp
    simpa [S] using this
  have hS_le : S ≤ ‖x‖ := by
    dsimp [S]
    classical
    refine ciSup_le (fun L : StrongDual ℝ E => ?_)
    by_cases hL : Var[L; μ] ≤ 1
    · simpa [hL] using apply_cmCoe_le_norm (μ := μ) (x := x) (L := L) hL
    · simp [hL]
  have hnorm_le : ‖x‖ ≤ S := by
    classical
    by_cases hx : ‖x‖ = 0
    · simpa [hx] using hS_nonneg
    · have hxpos : 0 < ‖x‖ := by simpa [norm_pos_iff] using hx
      have hxx : ⟪x, x⟫_ℝ ≤ ‖x‖ * S := by
        simpa [S] using (inner_cameronMartin_le_mul_ciSup (μ := μ) (x := x) (y := x))
      have hmul : ‖x‖ * ‖x‖ ≤ ‖x‖ * S := by
        simpa [real_inner_self_eq_norm_sq, pow_two, mul_assoc] using hxx
      exact le_of_mul_le_mul_left hmul hxpos
  have : ‖x‖ = S := by grind
  simpa [S] using this

lemma norm_cmOfBounded {y : E} [Decidable (∃ M, ∀ L : StrongDual ℝ E, Var[L; μ] ≤ 1 → L y ≤ M)]
    (hy : ∃ M, ∀ L : StrongDual ℝ E, Var[L; μ] ≤ 1 → L y ≤ M) :
    ‖cmOfBounded μ y‖ = ⨆ (L : StrongDual ℝ E) (_ : Var[L; μ] ≤ 1), L y := by
  have hcm : cmCoe (μ := μ) (cmOfBounded μ y) = y := cmCoe_cmOfBounded (μ := μ) (y := y) hy
  simp [norm_cameronMartin_eq_ciSup (μ := μ) (x := cmOfBounded μ y), hcm]

end ProbabilityTheory
