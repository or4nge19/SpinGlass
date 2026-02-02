/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Data.Real.CompleteField
import Common.Mathlib.Probability.Distributions.GaussianIntegrationByParts
import Common.Mathlib.Probability.Distributions.Gaussian.CameronMartinTilt
import Common.Mathlib.Probability.Distributions.Gaussian.CameronMartinFernique

/-!
# Gaussian Integration by Parts on a real Hilbert space (finite-dimensional, covariant form)

This file lifts the one-dimensional Gaussian integration by parts (Stein's lemma)
formalized in `PhysLean/Probability/GaussianIntegrationByParts.lean` to a
**finite-dimensional** real Hilbert space `H` by decomposing along an
orthonormal basis and applying the 1D result on each coordinate, with a
conditioning argument.

Compared with a "standard" (identity covariance) statement, we work directly at
**covariant** generality: the coordinates may have arbitrary (nonnegative)
variances `τ i`. The covariance operator is then

```
Σ h = ∑ i, (τ i : ℝ) * ⟪h, w i⟫ • w i,
```

and the IBP identity reads

```
E[⟪g, h⟫ F(g)] = E[(fderiv ℝ F (g)) (Σ h)].
```

The proof strategy:
* Fix an orthonormal basis `w : OrthonormalBasis ι ℝ H` with `[Fintype ι]`.
* Model a centered Gaussian `g : Ω → H` via independent centered normal
  coordinates `c i : Ω → ℝ` of variances `τ i` so that `g = ∑ i, (c i) • w i`.
* Expand `⟪g, h⟫ = ∑ i (c i) * ⟪h, w i⟫` and reduce to a 1D conditional step
  along each coordinate, which contributes a factor `τ i`.

We package the modeling assumptions into a predicate `IsGaussianHilbert`.

NOTE: For this version we restrict to a *finite* orthonormal basis index `ι`
with `[Fintype ι]`. Extending to separable infinite-dimensional spaces follows
by dominated convergence and standard Gaussian moment facts.
-/

open scoped Filter BigOperators Topology ProbabilityTheory ENNReal InnerProductSpace NNReal
open MeasureTheory Filter Set

noncomputable section

namespace PhysLean.Probability.GaussianIBP

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [MeasurableSpace H] [BorelSpace H]

-- Expectation notation (local; avoids referring to section variables in the expansion)
local notation3 (prettyPrint := false) "𝔼[" e "]" => ∫ ω, e ∂ℙ

/-- A centered Gaussian `H`-valued random variable modeled by coordinates -/
structure IsGaussianHilbert (g : Ω → H) where
  /-- Finite index type for the orthonormal basis. -/
  ι : Type*
  /-- Finite type structure on the index `ι`. -/
  fintype_ι : Fintype ι
  /-- An orthonormal basis of `H` indexed by `ι`. -/
  w : OrthonormalBasis ι ℝ H
  /-- Coordinate variances `τ i ≥ 0` (as `NNReal`). -/
  τ : ι → NNReal
  /-- Coordinate random variables `c i : Ω → ℝ`. -/
  c : ι → Ω → ℝ
  /-- Measurability of each coordinate process `c i`. -/
  c_meas : ∀ i, Measurable (c i)
  /-- Each coordinate `c i` is centered Gaussian with variance `τ i`. -/
  c_gauss : ∀ i, ProbabilityTheory.IsCenteredGaussianRV (c i) (τ i)
  /-- Independence of the family of coordinates `(c i)_i`. -/
  c_indep : ProbabilityTheory.iIndepFun c ℙ
  /-- Representation of `g` as the finite ONB sum `∑ i, (c i) • w i`. -/
  repr : g = fun ω => ∑ i, (c i ω) • w i

attribute [instance] IsGaussianHilbert.fintype_ι

/-- Moderate growth on `H → ℝ` -/
structure HasModerateGrowth {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (F : H → ℝ) where
  /-- A positive constant controlling the growth bound. -/
  C : ℝ
  /-- A natural exponent controlling the polynomial growth. -/
  m : ℕ
  /-- Positivity of the growth constant. -/
  Cpos : 0 < C
  /-- Pointwise bound on `F`: `|F z| ≤ C * (1 + ‖z‖) ^ m`. -/
  F_bound : ∀ z, |F z| ≤ C * (1 + ‖z‖) ^ m
  /-- Operator-norm bound on the Fréchet derivative:
      `‖fderiv ℝ F z‖ ≤ C * (1 + ‖z‖) ^ m`. -/
  dF_bound : ∀ z, ‖fderiv ℝ F z‖ ≤ C * (1 + ‖z‖) ^ m

namespace HasModerateGrowth

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma bound_dF_apply {F : H → ℝ} (hMG : HasModerateGrowth F) (z h : H) :
    ‖(fderiv ℝ F z) h‖ ≤ hMG.C * (1 + ‖z‖) ^ hMG.m * ‖h‖ := by
  have h₁ : ‖(fderiv ℝ F z) h‖ ≤ ‖fderiv ℝ F z‖ * ‖h‖ :=
    ContinuousLinearMap.le_opNorm _ _
  have h₂ : ‖fderiv ℝ F z‖ * ‖h‖ ≤ (hMG.C * (1 + ‖z‖) ^ hMG.m) * ‖h‖ :=
    mul_le_mul_of_nonneg_right (hMG.dF_bound z) (norm_nonneg _)
  exact h₁.trans h₂

end HasModerateGrowth

namespace Aux

variable {ι : Type*} [Fintype ι]
variable (w : OrthonormalBasis ι ℝ H)

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] in
@[simp] lemma inner_decomp (x y : H) :
    ⟪x, y⟫_ℝ = ∑ i, (⟪x, w i⟫_ℝ) * (⟪y, w i⟫_ℝ) := by
  simpa [real_inner_comm] using (w.sum_inner_mul_inner x y).symm

end Aux

/-- Coordinates of `g` in the basis `w`. -/
@[simp] def coord {ι : Type*} [Fintype ι]
    (w : OrthonormalBasis ι ℝ H) (g : Ω → H) (i : ι) : Ω → ℝ :=
  fun ω => ⟪g ω, w i⟫_ℝ

omit [IsProbabilityMeasure (ℙ : Measure Ω)] [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] in
/-- Explicit formula for the coordinates of `g` in the basis `w`. -/
lemma coord_repr_eq
    {g : Ω → H} (hg : IsGaussianHilbert g) (i : hg.ι) :
    coord hg.w g i = fun ω => ⟪g ω, hg.w i⟫_ℝ := rfl

omit [IsProbabilityMeasure (ℙ : Measure Ω)] [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] in
/-- On a Gaussian Hilbert model, the abstract coordinate map coincides with the
explicit coefficient process supplied by the model. -/
lemma coord_eq_c {g : Ω → H} (hg : IsGaussianHilbert g) :
    coord hg.w g = hg.c := by
  classical
  funext i ω
  -- Expand g ω and move inner through the finite sum.
  have hrepr : g ω = ∑ j : hg.ι, (hg.c j ω) • hg.w j := by
    simpa using congrArg (fun f => f ω) hg.repr
  simp only [coord, hrepr, sum_inner, inner_smul_left]
  -- The sum collapses to the i-th term by orthonormality.
  convert Finset.sum_eq_single i (fun j _ hij => ?_) (fun hi => ?_)
  · -- The i-th term is `c i ω * ⟪w i, w i⟫ = c i ω * 1`.
    simp
  · -- Off-diagonal terms `j ≠ i` are zero.
    simp [hij]
  · -- The index `i` is always in the universe.
    exact (hi (Finset.mem_univ i)).elim

omit [IsProbabilityMeasure (ℙ : Measure Ω)] [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] in
/-- For a Gaussian Hilbert model, each coordinate is centered normal with the
specified variance, and the coordinates are independent. -/
lemma coord_isGaussian_and_indep {g : Ω → H}
    (hg : IsGaussianHilbert g) :
    (∀ i, ProbabilityTheory.IsCenteredGaussianRV (coord hg.w g i) (hg.τ i)) ∧
    ProbabilityTheory.iIndepFun (coord hg.w g) ℙ := by
  classical
  have hcoord : coord hg.w g = hg.c := coord_eq_c (g := g) hg
  refine ⟨?std, ?indep⟩
  · intro i; simpa [hcoord] using hg.c_gauss i
  · simpa [hcoord] using hg.c_indep

omit [IsProbabilityMeasure (ℙ : Measure Ω)] [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] in
/-- Coordinates are measurable functions (inherited from the model `c`). -/
lemma coord_measurable {g : Ω → H} (hg : IsGaussianHilbert g) :
    ∀ i, Measurable (coord hg.w g i) := by
  intro i
  simpa [coord_eq_c (g := g) hg] using hg.c_meas i

/-! ## Gaussianity of the law (measure-level)

For Mathlib-facing API, it is useful to know that the **law** of an `H`-valued Gaussian random
variable is a Gaussian measure in the sense of `ProbabilityTheory.IsGaussian`.

In the present finite-dimensional modeling setup (`IsGaussianHilbert`), this can be proved by:
1. writing every 1D projection `L (g ω)` as a finite sum of independent 1D Gaussians;
2. using the 1D closure of Gaussians under independent sums (`gaussianReal_add_gaussianReal_of_indepFun`);
3. applying `ProbabilityTheory.isGaussian_of_map_eq_gaussianReal`.
-/

omit [CompleteSpace H] in
theorem IsGaussianHilbert.isGaussian_map {g : Ω → H} (hg : IsGaussianHilbert g) :
    ProbabilityTheory.IsGaussian ((ℙ : Measure Ω).map g) := by
  classical
  -- Use the characterization: `μ` is Gaussian iff every 1D projection is a real Gaussian.
  refine ProbabilityTheory.isGaussian_of_map_eq_gaussianReal (μ := (Measure.map g (ℙ : Measure Ω))) ?_
  intro L
  -- Measurability of `g` from its finite coordinate representation.
  have hg_meas : Measurable g := by
    classical
    let Φ : (hg.ι → ℝ) → H := fun y => ∑ i, (y i) • hg.w i
    have hΦ_cont : Continuous Φ := by
      have h_i : ∀ i : hg.ι, Continuous fun y : (hg.ι → ℝ) => (y i) • hg.w i := by
        intro i
        exact (continuous_apply i).smul continuous_const
      simpa [Φ] using
        (continuous_finset_sum (s := (Finset.univ : Finset hg.ι)) (fun i _ => h_i i))
    let cvec : Ω → (hg.ι → ℝ) := fun ω i => hg.c i ω
    have hcvec_meas : Measurable cvec := by
      refine measurable_pi_iff.mpr ?_
      intro i
      simpa [cvec] using hg.c_meas i
    have : Measurable (fun ω => Φ (cvec ω)) := hΦ_cont.measurable.comp hcvec_meas
    simpa [hg.repr, Φ, cvec] using this

  have hL_meas : Measurable (fun x : H => L x) := by
    simpa using L.continuous.measurable

  have h_map_map :
      (Measure.map g (ℙ : Measure Ω)).map (fun x : H => L x)
        =
      Measure.map (fun ω : Ω => L (g ω)) (ℙ : Measure Ω) := by
    simpa [Measure.map_map, Function.comp] using
      (MeasureTheory.Measure.map_map (μ := (ℙ : Measure Ω)) (g := fun x : H => L x) (f := g)
        hL_meas hg_meas)

  -- Expand `L ∘ g` along the coordinate representation.
  let a : hg.ι → ℝ := fun i => L (hg.w i)
  let X : hg.ι → Ω → ℝ := fun i ω => (hg.c i ω) * (a i)
  let v : hg.ι → ℝ≥0 := fun i => ((a i) ^ 2).toNNReal * hg.τ i

  have hX_meas : ∀ i, Measurable (X i) := by
    intro i
    -- multiplication by a constant is measurable
    simpa [X, a] using (hg.c_meas i).mul measurable_const

  have hindX : ProbabilityTheory.iIndepFun X (ℙ : Measure Ω) := by
    -- independence is stable under measurable coordinate-wise maps
    refine hg.c_indep.comp (μ := (ℙ : Measure Ω)) (g := fun i x => x * (a i)) ?_
    intro i
    simpa using (measurable_id.mul measurable_const)

  have hX_law : ∀ i, Measure.map (X i) (ℙ : Measure Ω) = ProbabilityTheory.gaussianReal 0 (v i) := by
    intro i
    -- Start from the Gaussian law of the coordinate `c i` and push it forward by multiplication.
    have hc_law : Measure.map (hg.c i) (ℙ : Measure Ω) = ProbabilityTheory.gaussianReal 0 (hg.τ i) := by
      simpa [ProbabilityTheory.IsCenteredGaussianRV, ProbabilityTheory.IsGaussianRV] using hg.c_gauss i
    have hmul :
        Measure.map (X i) (ℙ : Measure Ω)
          =
        (ProbabilityTheory.gaussianReal 0 (hg.τ i)).map (fun x : ℝ => x * (a i)) := by
      have hmap :=
        (MeasureTheory.Measure.map_map (μ := (ℙ : Measure Ω)) (g := fun x : ℝ => x * (a i)) (f := hg.c i)
          (measurable_id.mul measurable_const) (hg.c_meas i))
      -- `map_map` gives `((ℙ.map c).map g) = ℙ.map (g ∘ c)`; rewrite it in the direction we need.
      have :
          Measure.map (fun ω : Ω => (hg.c i ω) * (a i)) (ℙ : Measure Ω)
            =
          Measure.map (fun x : ℝ => x * (a i)) (Measure.map (hg.c i) (ℙ : Measure Ω)) := by
        simpa [Measure.map_map, Function.comp] using hmap.symm
      simpa [X, hc_law] using this
    have hgauss_map :
        (ProbabilityTheory.gaussianReal (0 : ℝ) (hg.τ i)).map (fun x : ℝ => x * (a i))
          =
        ProbabilityTheory.gaussianReal 0 (v i) := by
      have h :=
        (ProbabilityTheory.gaussianReal_map_mul_const (μ := (0 : ℝ)) (v := hg.τ i) (c := a i))
      have hv_eq :
          (⟨(a i) ^ 2, sq_nonneg (a i)⟩ : ℝ≥0) = ((a i) ^ 2).toNNReal := by
        ext
        simp [sq_nonneg (a i)]
      -- Rewrite the variance factor.
      simpa [v, hv_eq] using h
    simpa [hmul] using hgauss_map

  -- Law of the finite sum of independent centered Gaussians.
  have hsum_law_finset :
      ∀ s : Finset hg.ι,
        Measure.map (fun ω : Ω => Finset.sum s (fun i => X i ω)) (ℙ : Measure Ω)
          =
        ProbabilityTheory.gaussianReal 0 (Finset.sum s v) := by
    intro s
    refine Finset.induction_on s ?base ?step
    · simp [ProbabilityTheory.gaussianReal_zero_var]
    · intro i s hi hs
      have hind_tuples :
          ProbabilityTheory.IndepFun
            (fun ω (j : {x // x ∈ s}) => X j.1 ω)
            (fun ω (k : {x // x ∈ ({i} : Finset hg.ι)}) => X k.1 ω)
            (ℙ : Measure Ω) := by
        have hdisj : Disjoint s ({i} : Finset hg.ι) := by
          refine Finset.disjoint_right.2 ?_
          intro x hxT hxS
          have : x = i := by simpa using (Finset.mem_singleton.mp hxT)
          exact hi (this ▸ hxS)
        exact ProbabilityTheory.iIndepFun.indepFun_finset
          (f := X) (μ := (ℙ : Measure Ω)) (S := s) (T := ({i} : Finset hg.ι))
          hdisj hindX hX_meas
      let φ : ({x // x ∈ s} → ℝ) → ℝ := fun y => Finset.sum s.attach (fun j => y j)
      let ψ : ({x // x ∈ ({i} : Finset hg.ι)} → ℝ) → ℝ := fun y => y ⟨i, by simp⟩
      have hφ_meas : Measurable φ := by
        have hcont : Continuous φ := by
          have h_j :
              ∀ j : {x // x ∈ s}, Continuous fun y : ({x // x ∈ s} → ℝ) => y j :=
            fun j => continuous_apply j
          simpa [φ] using
            (continuous_finset_sum (s := s.attach) (fun j _ => h_j j))
        exact hcont.measurable
      have hψ_meas : Measurable ψ := by
        have : Continuous ψ := by
          simpa [ψ] using (continuous_apply (⟨i, by simp⟩ : {x // x ∈ ({i} : Finset hg.ι)}))
        exact this.measurable
      have hind_sum :
          ProbabilityTheory.IndepFun
            (fun ω : Ω => Finset.sum s (fun j => X j ω))
            (fun ω : Ω => X i ω)
            (ℙ : Measure Ω) := by
        have hind' := ProbabilityTheory.IndepFun.comp hind_tuples hφ_meas hψ_meas
        have hleft :
            (φ ∘ fun ω (j : {x // x ∈ s}) => X j.1 ω)
              =
            (fun ω : Ω => Finset.sum s (fun j => X j ω)) := by
          funext ω
          simp [φ]
          simpa using (Finset.sum_attach s (fun j => X j ω))
        have hright :
            (ψ ∘ fun ω (k : {x // x ∈ ({i} : Finset hg.ι)}) => X k.1 ω)
              =
            (fun ω : Ω => X i ω) := by
          funext ω
          simp [ψ]
        simpa [hleft, hright] using hind'
      have hadd :=
        ProbabilityTheory.gaussianReal_add_gaussianReal_of_indepFun
          (hXY := hind_sum) (hX := hs) (hY := hX_law i)
      have hsum_insert :
          (fun ω : Ω => Finset.sum (insert i s) (fun j => X j ω))
            =
          (fun ω : Ω => (Finset.sum s (fun j => X j ω)) + X i ω) := by
        funext ω
        simp [Finset.sum_insert, hi, add_comm]
      have hv_insert :
          (Finset.sum (insert i s) v) = (Finset.sum s v) + v i := by
        simp [Finset.sum_insert, hi, add_comm]
      -- Align with the `X+Y` order of `gaussianReal_add_gaussianReal_of_indepFun`.
      simpa [hsum_insert, hv_insert, add_comm, add_left_comm, add_assoc] using hadd

  have hsum_law :
      Measure.map (fun ω : Ω => ∑ i : hg.ι, X i ω) (ℙ : Measure Ω)
        =
      ProbabilityTheory.gaussianReal 0 (∑ i : hg.ι, v i) := by
    -- `∑ i, _` is definitionally a `Finset.sum` over `Finset.univ`.
    classical
    simpa using (hsum_law_finset (Finset.univ : Finset hg.ι))

  have hLg :
      (fun ω : Ω => L (g ω)) = fun ω : Ω => ∑ i : hg.ι, X i ω := by
    funext ω
    have hrepr : g ω = ∑ i : hg.ι, (hg.c i ω) • hg.w i := by
      simpa using congrArg (fun f => f ω) hg.repr
    -- Expand and use linearity of `L`.
    simp [hrepr, X, a]

  refine ⟨0, (∑ i : hg.ι, v i), ?_⟩
  calc
    (Measure.map g (ℙ : Measure Ω)).map (fun x : H => L x)
        = Measure.map (fun ω : Ω => L (g ω)) (ℙ : Measure Ω) := h_map_map
    _ = ProbabilityTheory.gaussianReal 0 (∑ i : hg.ι, v i) := by
          simpa [hLg] using hsum_law

/-! ## Integrability lemmas and linearity under sums
The following lemmas gather the integrability facts needed to justify using
`integral_finset_sum`, pulling constants outside expectations, and swapping a
finite sum with an expectation.

We also provide a *weighted* linearity lemma for `fderiv` inside a finite sum.
section Integrability-/

section AuxMeasAndMoments

open scoped BigOperators
open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [MeasurableSpace H] [BorelSpace H]
variable {g : Ω → H} {F : H → ℝ}
variable {g : Ω → H} {F : H → ℝ}


omit [IsProbabilityMeasure (ℙ : Measure Ω)] [CompleteSpace H] in
/-- `g` is measurable from the coordinate representation in the Gaussian model. -/
lemma IsGaussianHilbert.repr_measurable (hg : IsGaussianHilbert (Ω := Ω) (H := H) g) :
    Measurable g := by
  classical
  let Φ : (hg.ι → ℝ) → H := fun y => ∑ i, (y i) • hg.w i
  have hΦ_cont : Continuous Φ := by
    have h_i : ∀ i : hg.ι, Continuous fun y : (hg.ι → ℝ) => (y i) • hg.w i := by
      intro i
      exact (continuous_apply i).smul continuous_const
    simpa [Φ] using
      (continuous_finset_sum (s := (Finset.univ : Finset hg.ι)) (fun i _ => h_i i))
  let cvec : Ω → (hg.ι → ℝ) := fun ω i => hg.c i ω
  have hcvec_meas : Measurable cvec := by
    refine measurable_pi_iff.mpr ?_
    intro i
    simpa [cvec] using hg.c_meas i
  have : Measurable (fun ω => Φ (cvec ω)) := hΦ_cont.measurable.comp hcvec_meas
  simpa [hg.repr, Φ, cvec] using this

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- For a centered real Gaussian random variable, the square is integrable. -/
lemma ProbabilityTheory.IsCenteredGaussianRV.integrable_sq
    {X : Ω → ℝ} {v : ℝ≥0}
    (hX : ProbabilityTheory.IsCenteredGaussianRV X v)
    (hX_meas : Measurable X) :
    Integrable (fun ω => (X ω)^2) := by
  have h_int_gauss : Integrable (fun x : ℝ => x^2) (gaussianReal 0 v) := by
    simpa using ProbabilityTheory.integrable_sq_gaussianReal_centered (v := v)
  have hmap : Measure.map X (ℙ : Measure Ω) = gaussianReal 0 v := hX
  have h_int_map : Integrable (fun x : ℝ => x^2) (Measure.map X (ℙ : Measure Ω)) := by
    simpa [hmap] using h_int_gauss
  exact h_int_map.comp_measurable (μ := (ℙ : Measure Ω)) hX_meas

end AuxMeasAndMoments

section Integrability

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [MeasurableSpace H] [BorelSpace H]
variable {g : Ω → H} {F : H → ℝ}

omit [CompleteSpace H][MeasurableSpace H] [BorelSpace H] in
/-- The finite sum of absolute Gaussian coordinates is integrable. -/
lemma integrable_sum_abs_coords (hg : IsGaussianHilbert g) :
    Integrable (fun ω => ∑ i, |coord hg.w g i ω|) := by
  classical
  have hL1_each : ∀ i : hg.ι, Integrable (fun ω => |coord hg.w g i ω|) := by
    intro i
    have hL2 : Integrable (fun ω => (coord hg.w g i ω) ^ 2) := by
      have hGauss := (coord_isGaussian_and_indep (g := g) hg).1 i
      have hMeas := coord_measurable (g := g) hg i
      exact ProbabilityTheory.IsCenteredGaussianRV.integrable_sq (X := coord hg.w g i)
        (v := hg.τ i) hGauss hMeas
    have h_major_int : Integrable (fun ω => 1 + (coord hg.w g i ω) ^ 2) := by
      simpa using (integrable_const (μ := (ℙ : Measure Ω)) (c := (1 : ℝ))).add hL2
    have h_meas : AEStronglyMeasurable (fun ω => |coord hg.w g i ω|) ℙ :=
      (coord_measurable (g := g) hg i).abs.aestronglyMeasurable
    have h_dom : ∀ᵐ ω ∂ℙ, ‖|coord hg.w g i ω|‖ ≤ 1 + (coord hg.w g i ω) ^ 2 := by
      refine Eventually.of_forall (fun ω => ?_)

      set x := coord hg.w g i ω
      have h0 : 0 ≤ x ^ 2 := sq_nonneg x
      have h1 : (1 : ℝ) ≤ 1 + x ^ 2 := by exact le_add_of_nonneg_right h0
      by_cases hx : |x| ≤ 1
      · exact (le_trans (by simpa [Real.norm_eq_abs, abs_abs] using hx)
          (by simpa [Real.norm_eq_abs, abs_abs, add_comm] using h1))
      · have hgt : 1 < |x| := not_le.mp hx
        have habs_nonneg : 0 ≤ |x| := abs_nonneg x
        have h_le_sq : |x| ≤ |x| * |x| := by
          have := mul_le_mul_of_nonneg_left (le_of_lt hgt) habs_nonneg
          simpa [one_mul] using this
        have h_le_sq' : |x| ≤ x^2 := by simpa [pow_two, sq_abs] using h_le_sq
        have hx2_le : x^2 ≤ 1 + x^2 := by
          have : 0 ≤ (1 : ℝ) := by exact zero_le_one
          simp
        have : |x| ≤ 1 + x^2 := le_trans h_le_sq' hx2_le
        simpa [Real.norm_eq_abs, abs_abs] using this
    exact h_major_int.mono' h_meas h_dom
  simpa using
    (integrable_finset_sum
      (s := (Finset.univ : Finset hg.ι))
      (f := fun i ω => |coord hg.w g i ω|)
      (by intro i _; simpa using hL1_each i))

omit [CompleteSpace H] in
/-- A finite-dimensional Gaussian has integrable norm. -/
lemma integrable_norm_of_gaussian (hg : IsGaussianHilbert g) :
    Integrable (fun ω => ‖g ω‖) := by
  classical
  have hcoord : coord hg.w g = hg.c := coord_eq_c (g := g) hg
  have hsum : ∀ ω, g ω = ∑ i, (hg.c i ω) • hg.w i := by
    intro ω
    simpa using congrArg (fun f => f ω) hg.repr
  have hnorm_w_one : ∀ i : hg.ι, ‖hg.w i‖ = (1 : ℝ) := by
    intro i; simp
  have h_norm_le : ∀ ω, ‖g ω‖ ≤ ∑ i, |coord hg.w g i ω| := by
    intro ω
    have h_step :
        ‖g ω‖ ≤ ∑ i, ‖(hg.c i ω) • hg.w i‖ := by
      calc
        ‖g ω‖ = ‖∑ i, (hg.c i ω) • hg.w i‖ := by simp [hsum ω]
        _ ≤ ∑ i, ‖(hg.c i ω) • hg.w i‖ := by
          simpa using
            (norm_sum_le (s := (Finset.univ : Finset hg.ι))
              (f := fun i => (hg.c i ω) • hg.w i))
    have h_to_abs :
        ∑ i, ‖(hg.c i ω) • hg.w i‖ = ∑ i, |hg.c i ω| := by
      refine Finset.sum_congr rfl (by
        intro i _
        simp [norm_smul, hnorm_w_one i] )
    have h_to_coord :
        ∑ i, |hg.c i ω| = ∑ i, |coord hg.w g i ω| := by
      refine Finset.sum_congr rfl (by
        intro i _; simp only [coord]; rw [← hcoord]; rfl )
    exact h_step.trans (by simp [h_to_abs, h_to_coord])
  have h_sum_int := integrable_sum_abs_coords (hg := hg)
  refine h_sum_int.mono' (hg.repr_measurable.norm.aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall (fun ω => by
    have : ‖‖g ω‖‖ = ‖g ω‖ := by
      simp
    simpa [this] using (h_norm_le ω))

omit [CompleteSpace H] in
/-- Backwards-compatible wrapper: the only cases used below are `p = 1` and
polynomial profiles, both covered by the previous lemmas. For `p = 1`
we provide this alias. -/
lemma integrable_norm_pow_one_of_gaussian (hg : IsGaussianHilbert g) :
    Integrable (fun ω => ‖g ω‖ ^ (1 : ℝ)) := by
  simpa using (integrable_norm_of_gaussian (hg := hg))

/-! ### A clean domination by polynomial moments

For p ≥ 0 and any natural m with p ≤ m, we have the pointwise bound
  x^p ≤ (1 + x)^m  for all x ≥ 0.
This yields integrability of ‖g‖^p from the polynomial moment
integrability already proved in `integrable_one_add_norm_pow`.
-/


/-- Scalar inequality: for `p ≥ 0`, `p ≤ m : ℕ`, and `x ≥ 0`,
we have `x^p ≤ (1 + x)^m`. -/
lemma rpow_le_one_add_pow_nat_of_le (p : ℝ) (m : ℕ)
    (hp : 0 ≤ p) (hp_le : p ≤ m) :
    ∀ x : ℝ, 0 ≤ x → x ^ p ≤ (1 + x) ^ m := by
  intro x hx
  by_cases hxle1 : x ≤ 1
  · have hxp_le_one : x ^ p ≤ (1 : ℝ) ^ p :=
      Real.rpow_le_rpow hx hxle1 hp
    have hone : (1 : ℝ) ^ p = (1 : ℝ) := by simp
    have h1le : (1 : ℝ) ≤ (1 + x) ^ m := by
      have h01x : 1 ≤ 1 + x := by linarith
      have h0 : 0 ≤ 1 + x := by linarith
      simp only [ge_iff_le]
      exact one_le_pow₀ h01x
    exact (by
      have : x ^ p ≤ (1 : ℝ) := by simpa [hone] using hxp_le_one
      exact this.trans h1le)
  · have hx1 : 1 ≤ x := le_of_lt (lt_of_not_ge hxle1)
    have hxp_le_xm : x ^ p ≤ x ^ (m : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 hp_le
    have hx_nonneg : 0 ≤ x := hx
    have hx_le_1x : x ≤ 1 + x := by linarith
    have xpow_nat :
        (x : ℝ) ^ (m : ℝ) = (x ^ m : ℝ) := by
      simp
    have x_pow_le_one_add :
        (x ^ m : ℝ) ≤ (1 + x) ^ m :=
          ProbabilityTheory.Real.pow_le_pow_of_le_left hx hx_le_1x
    calc
      x ^ p ≤ x ^ (m : ℝ) := hxp_le_xm
      _ = (x ^ m : ℝ) := by simp [xpow_nat]
      _ ≤ (1 + x) ^ m := x_pow_le_one_add

section MeanIneqHelpers

open scoped BigOperators
open Finset

variable {ι : Type*}

/-- For `p ≥ 1` and nonnegative weights `z i ≥ 0`, the generalized mean inequality
(unnormalized) on a finite set `s`:

  (∑ i∈s, z i)^p ≤ (s.card : ℝ)^(p - 1) * ∑ i∈s, (z i)^p.

This is the equal-weights case of `Real.rpow_arith_mean_le_arith_mean_rpow`. -/
lemma sum_rpow_le_card_pow_sub_one_sum_rpow
    (s : Finset ι) (z : ι → ℝ) {p : ℝ}
    (hp : 1 ≤ p) (hz : ∀ i ∈ s, 0 ≤ z i) :
    (∑ i ∈ s, z i) ^ p ≤ (s.card : ℝ) ^ (p - 1) * ∑ i ∈ s, (z i) ^ p := by
  classical
  by_cases h0 : s.card = 0
  · have hs : s = ∅ := Finset.card_eq_zero.mp h0
    have hp0 : 0 < p := by linarith
    simp [hs, hp0.ne']
  · have hcard_pos_nat : 0 < s.card := Nat.pos_of_ne_zero (by simpa using h0)
    have hcard_pos : 0 < (s.card : ℝ) := by exact_mod_cast hcard_pos_nat
    let c : ℝ := s.card
    have hc_pos : 0 < c := by simpa [c] using hcard_pos
    have hc_nonneg : 0 ≤ c := le_of_lt hc_pos
    have hw_nonneg : ∀ i ∈ s, 0 ≤ c⁻¹ := fun _ _ => inv_nonneg.mpr hc_nonneg
    have hw_sum : ∑ i ∈ s, c⁻¹ = 1 := by
      simp [Finset.sum_const, nsmul_eq_mul, c, ne_of_gt hc_pos]
    have hmean :
        (∑ i ∈ s, c⁻¹ * z i) ^ p ≤ ∑ i ∈ s, c⁻¹ * (z i) ^ p :=
      Real.rpow_arith_mean_le_arith_mean_rpow
        (s := s) (w := fun _ => c⁻¹) (z := z) hw_nonneg hw_sum hz hp
    have hR : (∑ i ∈ s, c⁻¹ * (z i) ^ p) = c⁻¹ * ∑ i ∈ s, (z i) ^ p := by
      simp [mul_sum]
    have ha_nonneg : 0 ≤ ∑ i ∈ s, c⁻¹ * z i :=
      Finset.sum_nonneg (by
        intro i hi; exact mul_nonneg (inv_nonneg.mpr hc_nonneg) (hz i hi))
    have hmul :
        (c : ℝ) ^ p * (∑ i ∈ s, c⁻¹ * z i) ^ p
          ≤ (c : ℝ) ^ p * (c⁻¹ * ∑ i ∈ s, (z i) ^ p) := by
      exact mul_le_mul_of_nonneg_left (by simpa [hR] using hmean)
        (Real.rpow_nonneg hc_nonneg _)
    have c_mul_avg :
        c * (∑ i ∈ s, c⁻¹ * z i) = ∑ i ∈ s, z i := by
      calc
        c * (∑ i ∈ s, c⁻¹ * z i)
            = ∑ i ∈ s, c * (c⁻¹ * z i) := by simp [mul_sum]
        _ = ∑ i ∈ s, (c * c⁻¹) * z i := by
          refine Finset.sum_congr rfl (by intro i hi; simp [mul_assoc])
        _ = ∑ i ∈ s, z i := by
          simp [ne_of_gt hc_pos, mul_comm]
    have hL :
        (c : ℝ) ^ p * (∑ i ∈ s, c⁻¹ * z i) ^ p = (∑ i ∈ s, z i) ^ p := by
      have : (c * (∑ i ∈ s, c⁻¹ * z i)) ^ p
              = (c : ℝ) ^ p * (∑ i ∈ s, c⁻¹ * z i) ^ p :=
        Real.mul_rpow hc_nonneg ha_nonneg
      aesop
    have hpow_mul_right :
        (c : ℝ) ^ p * (c⁻¹ * ∑ i ∈ s, (z i) ^ p)
          = (c : ℝ) ^ (p - 1) * ∑ i ∈ s, (z i) ^ p := by
      have hpdecomp : (c : ℝ) ^ p = (c : ℝ) ^ (p - 1) * (c : ℝ) ^ 1 := by
        simpa [sub_eq_add_neg, Real.rpow_one, add_comm, add_left_comm, add_assoc] using
          (Real.rpow_add hc_pos (p - 1) (1 : ℝ))
      calc
        (c : ℝ) ^ p * (c⁻¹ * ∑ i ∈ s, (z i) ^ p)
            = ((c : ℝ) ^ (p - 1) * (c : ℝ) ^ 1) * (c⁻¹ * ∑ i ∈ s, (z i) ^ p) := by
              simp [hpdecomp]
        _ = (c : ℝ) ^ (p - 1) * ((c : ℝ) ^ 1 * (c⁻¹ * ∑ i ∈ s, (z i) ^ p)) := by
              simp [mul_comm, mul_left_comm, mul_assoc]
        _ = (c : ℝ) ^ (p - 1) * (∑ i ∈ s, (z i) ^ p) := by
          have : (c : ℝ) ^ 1 = c := by simp
          simp [this, ne_of_gt hc_pos]
    simpa [hL, hpow_mul_right] using hmul

end MeanIneqHelpers

section PolynomialMoments

open scoped BigOperators
open MeasureTheory ProbabilityTheory
open Finset

variable {g : Ω → H}


/-! 1D Gaussian moment helpers (all nat moments are finite). -/
namespace ProbabilityTheory

/-- All absolute moments `|x|^k` are integrable under any centered real Gaussian. -/
lemma integrable_abs_pow_gaussianReal_centered_nat
    (v : ℝ≥0) (k : ℕ) :
    Integrable (fun x : ℝ => |x| ^ k) (ProbabilityTheory.gaussianReal 0 v) := by
  -- Prefer the Fernique/MemLp-based moment API (via `IsGaussian.memLp_id`), coming from Mathlib.
  simpa using (ProbabilityTheory.integrable_abs_pow_gaussianReal (m := (0 : ℝ)) (v := v) (n := k))

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- Lift to an RV: a centered Gaussian RV has all finite absolute moments. -/
lemma IsCenteredGaussianRV.integrable_abs_pow_nat
    {X : Ω → ℝ} {v : ℝ≥0}
    (hX : ProbabilityTheory.IsCenteredGaussianRV X v)
    (hX_meas : Measurable X) (k : ℕ) :
    Integrable (fun ω => |X ω| ^ k) := by
  have hmap : Measure.map X (ℙ : Measure Ω) = ProbabilityTheory.gaussianReal 0 v := hX
  have h_int_map :
      Integrable (fun x : ℝ => |x| ^ k) (Measure.map X (ℙ : Measure Ω)) := by
    simpa [hmap] using
      integrable_abs_pow_gaussianReal_centered_nat (v := v) (k := k)
  exact h_int_map.comp_measurable (μ := (ℙ : Measure Ω)) hX_meas

end ProbabilityTheory

-- Monotonicity of natural powers on ℝ for nonnegative bases.
namespace Real

lemma pow_le_pow_of_le_left {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (n : ℕ) :
    a ^ n ≤ b ^ n := by exact ProbabilityTheory.Real.pow_le_pow_of_le_left ha hab

end Real

section FiniteOnbPowerDomination

open scoped BigOperators
open Finset MeasureTheory ProbabilityTheory

variable {ι Ω H : Type*}
variable [Fintype ι]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [MeasurableSpace Ω] {μ : Measure Ω}

/-- For a finite orthonormal basis `w` and coefficients `c : ι → ℝ`, raise the
norm of the finite sum to a natural power and dominate it by the sum of powers
of the coefficients (generalized mean inequality, equal-weights case). -/
lemma norm_pow_nat_le_card_pow_pred_sum_abs_pow
  (w : OrthonormalBasis ι ℝ H) (c : ι → ℝ) (m : ℕ) (hm : 1 ≤ m) :
  ‖∑ i, c i • w i‖ ^ m ≤ (Fintype.card ι : ℝ) ^ (m - 1) * ∑ i, |c i| ^ m := by
  classical
  cases m with
  | zero => cases hm
  | succ k =>
    have h₁ : ‖∑ i, c i • w i‖ ≤ ∑ i, ‖c i • w i‖ := by
      simpa using norm_sum_le (s := (Finset.univ : Finset ι)) (f := fun i => c i • w i)
    have h₂ : ∀ i, ‖c i • w i‖ = |c i| := fun i => by
      -- `‖w i‖ = 1`
      have hw : ‖w i‖ = (1 : ℝ) := by simp
      simp [norm_smul, hw]
    have hsum_univ :
        ∑ i ∈ (Finset.univ : Finset ι), ‖c i • w i‖
          = ∑ i ∈ (Finset.univ : Finset ι), |c i| := by
      refine Finset.sum_congr rfl ?_
      intro i hi; simp [h₂ i]
    have hsum : ∑ i, ‖c i • w i‖ = ∑ i, |c i| := by
      simpa using hsum_univ
    let n := Nat.succ k
    have hnn : 0 ≤ ‖∑ i, c i • w i‖ := norm_nonneg _
    have h₁m : ‖∑ i, c i • w i‖ ^ n ≤ (∑ i, |c i|) ^ n := by
      exact Real.pow_le_pow_of_le_left hnn (by simpa [hsum] using h₁) n
    have hmean_main :
        (∑ i, |c i|) ^ n
          ≤ (Fintype.card ι : ℝ) ^ (n - 1) * ∑ i, |c i| ^ n := by
      by_cases h0 : Fintype.card ι = 0
      · have : (Finset.univ : Finset ι) = ∅ := by
          simpa using Finset.card_eq_zero.mp h0
        simp [this, h0]
      · set s : Finset ι := Finset.univ
        set cR : ℝ := (Fintype.card ι : ℝ)
        have hc_pos_nat : 0 < Fintype.card ι := Nat.pos_of_ne_zero h0
        have hc_pos : 0 < cR := by
          have : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr hc_pos_nat
          simpa [cR] using this
        have hw_nonneg : ∀ i ∈ s, 0 ≤ cR⁻¹ := fun _ _ => inv_nonneg.mpr (le_of_lt hc_pos)
        have hw_sum : ∑ i ∈ s, cR⁻¹ = 1 := by
          simp [s, cR, Finset.sum_const, nsmul_eq_mul, ne_of_gt hc_pos]
        have hz_nonneg : ∀ i ∈ s, 0 ≤ |c i| := by
          intro i _; exact abs_nonneg _
        have hmean :=
          Real.pow_arith_mean_le_arith_mean_pow (s := s)
            (w := fun _ => cR⁻¹) (z := fun i => |c i|)
            (hw := fun i hi => by exact hw_nonneg i hi)
            (hw' := by simpa [s] using hw_sum)
            (hz := fun i hi => hz_nonneg i hi)
            (n := n)
        have hL :
            (∑ i ∈ s, cR⁻¹ * |c i|) ^ n
              = (cR ^ n)⁻¹ * (∑ i, |c i|) ^ n := by
          have : (∑ i ∈ s, cR⁻¹ * |c i|) = cR⁻¹ * (∑ i, |c i|) := by
            simp [s, mul_sum]
          calc
            (∑ i ∈ s, cR⁻¹ * |c i|) ^ n
                = (cR⁻¹ * (∑ i, |c i|)) ^ n := by simp [this]
            _ = (cR⁻¹) ^ n * (∑ i, |c i|) ^ n := by
                  simpa using (mul_pow (cR⁻¹) (∑ i, |c i|) n)
            _ = (cR ^ n)⁻¹ * (∑ i, |c i|) ^ n := by
                  simp [inv_pow]
        have hR :
            (∑ i ∈ s, cR⁻¹ * (|c i|) ^ n)
              = cR⁻¹ * ∑ i, (|c i|) ^ n := by
          simp [s, mul_sum]
        have hrew : (cR ^ n)⁻¹ * (∑ i, |c i|) ^ n
                      ≤ cR⁻¹ * ∑ i, (|c i|) ^ n := by
          simpa [hL, hR, s] using hmean
        have hc_pow_pos : 0 < (cR : ℝ) ^ n := pow_pos hc_pos _
        have hmul := mul_le_mul_of_nonneg_left hrew (le_of_lt hc_pow_pos)
        have hc_ne : (cR : ℝ) ≠ 0 := ne_of_gt hc_pos
        have hc_pow_ne : (cR : ℝ) ^ n ≠ 0 := by exact pow_ne_zero _ hc_ne
        have hLcancel :
            cR ^ n * ((cR ^ n)⁻¹ * (∑ i, |c i|) ^ n) = (∑ i, |c i|) ^ n := by
          simp_all only [le_add_iff_nonneg_left, zero_le, norm_nonneg, Nat.succ_eq_add_one,
            Nat.cast_pos, Finset.mem_univ, inv_nonneg, Nat.cast_nonneg, imp_self, implies_true,
            sum_const, card_univ, nsmul_eq_mul, ne_eq, Nat.cast_eq_zero, not_false_eq_true,
            mul_inv_cancel₀, abs_nonneg, pow_pos, Nat.add_eq_zero_iff,
            one_ne_zero, and_false, pow_eq_zero_iff, mul_inv_cancel_left₀, cR, s, n]
        have hRcancel :
            cR ^ n * (cR⁻¹ * ∑ i, |c i| ^ n) = cR ^ k * ∑ i, |c i| ^ n := by
          have : cR * (cR ^ k * (cR⁻¹ * ∑ i, |c i| ^ n))
                  = cR ^ k * ∑ i, |c i| ^ n := by
            have hc_ne' : cR ≠ 0 := hc_ne
            calc
              cR * (cR ^ k * (cR⁻¹ * ∑ i, |c i| ^ n))
                  = cR ^ k * (cR * (cR⁻¹ * ∑ i, |c i| ^ n)) := by
                      simp [mul_left_comm]
              _ = cR ^ k * ((cR * cR⁻¹) * ∑ i, |c i| ^ n) := by
                      simp [mul_left_comm, mul_assoc]
              _ = cR ^ k * (1 * ∑ i, |c i| ^ n) := by
                      simp [hc_ne']
              _ = cR ^ k * ∑ i, |c i| ^ n := by simp
          simpa [n, pow_succ, mul_comm, mul_left_comm, mul_assoc] using this
        have hmul' :
            (∑ i, |c i|) ^ n ≤ cR ^ k * ∑ i, |c i| ^ n := by
          simpa [hLcancel, hRcancel] using hmul
        simpa [n, Nat.succ_sub_one, mul_comm, mul_left_comm, mul_assoc] using hmul'
    simpa [n] using (h₁m.trans hmean_main)

variable [MeasurableSpace H] [BorelSpace H]


/-- Integrability lift: if each `|c i|^m` is integrable (under `ℙ`) and `m ≥ 1`,
then `‖∑ i, c i • w i‖^m` is integrable (under `ℙ`). For `m = 0` it is the constant `1`. -/
lemma integrable_norm_pow_nat_of_onb_sum
  {Ω ι H : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
  [Fintype ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [MeasurableSpace H] [BorelSpace H]
  (w : OrthonormalBasis ι ℝ H) (c : ι → Ω → ℝ) (m : ℕ)
  (hc_meas : ∀ i, Measurable (c i))
  (hc_int : ∀ i, Integrable (fun ω => |c i ω| ^ m)) :
  Integrable (fun ω => ‖∑ i, c i ω • w i‖ ^ m) := by
  classical
  cases m with
  | zero =>
      simp
  | succ k =>
      let n := Nat.succ k
      have h_pt :
          ∀ ω, ‖∑ i, c i ω • w i‖ ^ n
                ≤ (Fintype.card ι : ℝ) ^ (n - 1) * ∑ i, |c i ω| ^ n := by
        intro ω
        have := norm_pow_nat_le_card_pow_pred_sum_abs_pow (w := w) (c := fun i => c i ω) (m := n) (by aesop)
        simpa using this
      have h_sum_int : Integrable (fun ω => ∑ i, |c i ω| ^ n) := by
        have h_each : ∀ i, Integrable (fun ω => |c i ω| ^ n) := by
          intro i
          simpa [n] using hc_int i
        simpa using (integrable_finset_sum (s := (Finset.univ : Finset ι))
                    (f := fun i ω => |c i ω| ^ n) (fun i _ => h_each i))
      have h_rhs_int :
          Integrable (fun ω => (Fintype.card ι : ℝ) ^ (n - 1) * ∑ i, |c i ω| ^ n) :=
        h_sum_int.const_mul _
      have h_meas_sum : Measurable (fun ω => ∑ i, c i ω • w i) := by
        classical
        let Φ : (ι → ℝ) → H := fun y => ∑ i, (y i) • w i
        have hΦ_cont : Continuous Φ := by
          have h_i : ∀ i : ι, Continuous fun y : (ι → ℝ) => (y i) • w i := by
            intro i
            exact (continuous_apply i).smul continuous_const
          simpa [Φ] using
            (continuous_finset_sum (s := (Finset.univ : Finset ι)) (fun i _ => h_i i))
        let cvec : Ω → (ι → ℝ) := fun ω i => c i ω
        have hcvec_meas : Measurable cvec := by
          refine measurable_pi_iff.mpr ?_
          intro i
          simpa [cvec] using hc_meas i
        simpa [Φ, cvec] using hΦ_cont.measurable.comp hcvec_meas
      have h_measL : AEStronglyMeasurable (fun ω => ‖∑ i, c i ω • w i‖ ^ n) (ℙ : Measure Ω) := by
        have : Measurable (fun ω => ‖∑ i, c i ω • w i‖) := h_meas_sum.norm
        exact (this.pow_const n).aestronglyMeasurable
      refine h_rhs_int.mono' h_measL (Filter.Eventually.of_forall ?_)
      intro ω
      have hR : 0 ≤ (Fintype.card ι : ℝ) ^ (n - 1) * ∑ i, |c i ω| ^ n := by
        have : 0 ≤ ∑ i, |c i ω| ^ n := by
          exact Finset.sum_nonneg (by intro i _; exact pow_nonneg (abs_nonneg _) _)
        have hc : 0 ≤ (Fintype.card ι : ℝ) ^ (n - 1) := by
          exact pow_nonneg (by exact_mod_cast (Nat.cast_nonneg (Fintype.card ι))) _
        exact mul_nonneg hc this
      have hL : 0 ≤ ‖∑ i, c i ω • w i‖ ^ n := by exact pow_nonneg (norm_nonneg _) _
      have := h_pt ω
      simpa [Real.norm_eq_abs, abs_of_nonneg hL, abs_of_nonneg hR] using this

end FiniteOnbPowerDomination

section GaussianONB_Moments

open MeasureTheory ProbabilityTheory Finset PhysLean.Probability.GaussianIBP

variable {Ω ι H : Type*}
variable [MeasureSpace Ω] {μ : Measure Ω}
variable [IsProbabilityMeasure (ℙ : Measure Ω)]
variable [Fintype ι]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [MeasurableSpace H] [BorelSpace H]

/-- If `g = ∑ i, c i • w i` with ONB `w` and each `c i` integrable in `|·|^m`,
then `‖g‖^m` is integrable (under `ℙ`). -/
lemma integrable_norm_pow_nat_of_onb_sum_of_gaussian_coords
  (w : OrthonormalBasis ι ℝ H) (c : ι → Ω → ℝ) (m : ℕ)
  (hc_meas : ∀ i, Measurable (c i))
  (hc_gauss : ∀ i, ProbabilityTheory.IsCenteredGaussianRV (c i) (0 : ℝ≥0)) :
  Integrable (fun ω => ‖∑ i, c i ω • w i‖ ^ m) := by
  classical
  have hc_int : ∀ i, Integrable (fun ω => |c i ω| ^ m) := by
    intro i
    exact ProbabilityTheory.IsCenteredGaussianRV.integrable_abs_pow_nat
      (hX := hc_gauss i) (hX_meas := hc_meas i) (k := m)
  exact integrable_norm_pow_nat_of_onb_sum
    (w := w) (c := c) (m := m) (hc_meas := hc_meas) (hc_int := hc_int)

/-- For the `IsGaussianHilbert` model, all natural moments of `‖g‖` are integrable (under `ℙ`). -/
lemma integrable_norm_pow_nat_of_gaussian
  {g : Ω → H} (hg : IsGaussianHilbert g) (m : ℕ) :
  Integrable (fun ω => ‖g ω‖ ^ m) := by
  classical
  cases m with
  | zero =>
      simp
  | succ k =>
      have h_repr : ∀ ω, g ω = ∑ i, (hg.c i ω) • hg.w i := fun ω =>
        by simpa using congrArg (fun f => f ω) hg.repr
      have h_meas : ∀ i, Measurable (hg.c i) := hg.c_meas
      have h_gauss : ∀ i, ProbabilityTheory.IsCenteredGaussianRV (hg.c i) (hg.τ i) := hg.c_gauss
      let mNat := Nat.succ k
      have h_int_sum :
          Integrable (fun ω => ‖∑ i, hg.c i ω • hg.w i‖ ^ mNat) := by
        have hc_int : ∀ i, Integrable (fun ω => |hg.c i ω| ^ mNat) := by
          intro i
          exact ProbabilityTheory.IsCenteredGaussianRV.integrable_abs_pow_nat
            (hX := h_gauss i) (hX_meas := h_meas i) (k := mNat)
        exact integrable_norm_pow_nat_of_onb_sum
          (w := hg.w) (c := hg.c) (m := mNat) (hc_meas := h_meas) (hc_int := hc_int)
      simpa [h_repr] using h_int_sum


end GaussianONB_Moments

end PolynomialMoments
open MeasureTheory ProbabilityTheory Finset PhysLean.Probability.GaussianIBP

open MeasureTheory ProbabilityTheory

omit [CompleteSpace H] in
/-- All polynomial profiles `(1 + ‖g‖)^m` are integrable. -/
lemma integrable_one_add_norm_pow
    (hg : IsGaussianHilbert g) (m : ℕ) :
    Integrable (fun ω => (1 + ‖g ω‖) ^ m) := by
  classical
  have h_term :
      ∀ k ∈ Finset.range (m + 1),
        Integrable (fun ω => (Nat.choose m k : ℝ) * (‖g ω‖) ^ k) := by
    intro k hk
    have hk_int : Integrable (fun ω => (‖g ω‖) ^ k) := by
      exact integrable_norm_pow_nat_of_gaussian (g := g) (hg := hg) k
    simpa using hk_int.const_mul (Nat.choose m k : ℝ)
  have h_sum :
      Integrable (fun ω =>
        ∑ k ∈ Finset.range (m + 1), (Nat.choose m k : ℝ) * (‖g ω‖) ^ k) := by
    simpa using
      (integrable_finset_sum
        (s := Finset.range (m + 1))
        (f := fun k ω => (Nat.choose m k : ℝ) * (‖g ω‖) ^ k)
        (by intro k hk; exact h_term k hk))
  have :
      (fun ω => (1 + ‖g ω‖) ^ m)
        =
      (fun ω =>
        ∑ k ∈ Finset.range (m + 1), (Nat.choose m k : ℝ) * (‖g ω‖) ^ k) := by
    funext ω
    simp [add_pow, one_pow, add_comm, mul_comm]
  simpa [this] using h_sum

omit [CompleteSpace H] in
/-- Parameterized integrability: if `p ≥ 0` and `p ≤ m` for some natural `m`,
then `‖g‖^p` is integrable. -/
lemma integrable_norm_rpow_of_gaussian_of_nat_ub
    (hg : IsGaussianHilbert g) (p : ℝ) (hp : 0 ≤ p)
    (m : ℕ) (hp_le : p ≤ m) :
    Integrable (fun ω => ‖g ω‖ ^ p) := by
  classical
  have h_dom :
      ∀ ω, ‖g ω‖ ^ p ≤ (1 + ‖g ω‖) ^ m :=
    fun ω => rpow_le_one_add_pow_nat_of_le (p := p) (m := m) hp hp_le (‖g ω‖) (norm_nonneg _)
  have h_int_poly : Integrable (fun ω => (1 + ‖g ω‖) ^ m) :=
    integrable_one_add_norm_pow (hg := hg) (m := m)
  have h_meas : AEStronglyMeasurable (fun ω => ‖g ω‖ ^ p) ℙ := by
    have h1 : Measurable (fun ω => ‖g ω‖) := hg.repr_measurable.norm
    have h2 : Measurable (fun t : ℝ => t ^ p) := by
      measurability
    exact (h2.comp h1).aestronglyMeasurable
  refine h_int_poly.mono' h_meas (Filter.Eventually.of_forall ?_)
  intro ω
  have hR : 0 ≤ (1 + ‖g ω‖) ^ m := by
    have : 0 ≤ 1 + ‖g ω‖ := by nlinarith [norm_nonneg (g ω)]
    exact pow_nonneg this _
  have hL : 0 ≤ ‖g ω‖ ^ p := Real.rpow_nonneg (norm_nonneg _) _
  simpa [Real.norm_eq_abs, abs_of_nonneg hL, abs_of_nonneg hR] using h_dom ω

omit [CompleteSpace H] in
/-- All moments of the norm of a finite-dimensional Gaussian are finite (for `p ≥ 0`).
This wrapper chooses a natural upper bound `m ≥ p` by existence. -/
lemma integrable_norm_pow_of_gaussian
    (hg : IsGaussianHilbert g) (p : ℝ) (hp : 0 ≤ p) :
    Integrable (fun ω => ‖g ω‖ ^ p) := by
  classical
  obtain ⟨m, hm⟩ := exists_nat_ge p
  exact integrable_norm_rpow_of_gaussian_of_nat_ub (hg := hg) (p := p) hp (m := m) (hp_le := by exact_mod_cast hm)

omit [CompleteSpace H] in
/-- Convenience: natural moments are integrable. -/
lemma integrable_norm_pow_nat_of_gaussian'
    (hg : IsGaussianHilbert g) (k : ℕ) :
    Integrable (fun ω => (‖g ω‖) ^ k) := by
  have h := integrable_norm_rpow_of_gaussian_of_nat_ub (hg := hg)
              (p := (k : ℝ)) (hp := by exact_mod_cast (Nat.cast_nonneg k))
              (m := k) (hp_le := by exact_mod_cast (le_of_eq rfl))
  exact integrable_norm_pow_nat_of_gaussian hg k

omit [CompleteSpace H] in
/-- All polynomial profiles in the norm are integrable. -/
lemma integrable_one_add_norm_pow' (hg : IsGaussianHilbert g) (m : ℕ) :
    Integrable (fun ω => (1 + ‖g ω‖) ^ m) := by
  classical
  have h_term :
      ∀ k ∈ Finset.range (m + 1),
        Integrable (fun ω => (Nat.choose m k : ℝ) * (‖g ω‖) ^ k) := by
    intro k hk
    have hk_int : Integrable (fun ω => (‖g ω‖) ^ k) := by
      cases k with
      | zero => simp
      | succ k' =>
          have h := integrable_norm_pow_of_gaussian (g := g) (hg := hg) (p := (Nat.succ k' : ℝ))
            (hp := by exact Nat.cast_nonneg' k'.succ)
          exact integrable_norm_pow_nat_of_gaussian hg (k' + 1)
    simpa using hk_int.const_mul (Nat.choose m k : ℝ)
  have h_sum :
      Integrable (fun ω =>
        ∑ k ∈ Finset.range (m + 1), (Nat.choose m k : ℝ) * (‖g ω‖) ^ k) := by
    simpa using
      (integrable_finset_sum
        (s := Finset.range (m + 1))
        (f := fun k ω => (Nat.choose m k : ℝ) * (‖g ω‖) ^ k)
        (by intro k hk; exact h_term k hk))
  have : (fun ω => (1 + ‖g ω‖) ^ m)
      = (fun ω =>
          ∑ k ∈ Finset.range (m + 1), (Nat.choose m k : ℝ) * (‖g ω‖) ^ k) := by
    funext ω
    simp [add_comm, add_pow, one_pow, mul_comm]
  simpa [this]

omit [CompleteSpace H] in
/-- Under polynomial growth of `F` and Gaussian tails of `g`, `F ∘ g` is integrable. -/
lemma integrable_F_of_growth
    (hg : IsGaussianHilbert g) (hF_diff : ContDiff ℝ 1 F) (hF_growth : HasModerateGrowth F) :
    Integrable (fun ω => F (g ω)) := by
  have h_bound : ∀ ω, |F (g ω)| ≤ hF_growth.C * (1 + ‖g ω‖) ^ hF_growth.m :=
    fun ω => hF_growth.F_bound (g ω)
  have h_int_poly : Integrable (fun ω => (1 + ‖g ω‖) ^ hF_growth.m) := by
    simpa using integrable_one_add_norm_pow (hg := hg) (m := hF_growth.m)
  have h_int_bound : Integrable (fun ω => hF_growth.C * (1 + ‖g ω‖) ^ hF_growth.m) :=
    h_int_poly.const_mul hF_growth.C
  have hg_meas : Measurable g := hg.repr_measurable
  have hF_meas : Measurable F := hF_diff.continuous.measurable
  apply Integrable.mono h_int_bound (hF_meas.comp hg_meas).aestronglyMeasurable
  refine Filter.Eventually.of_forall (fun ω => ?_)
  have hbase : 0 ≤ 1 + ‖g ω‖ := by nlinarith [norm_nonneg (g ω)]
  have hCabs : |hF_growth.C| = hF_growth.C := abs_of_nonneg (le_of_lt hF_growth.Cpos)
  have h1abs : |1 + ‖g ω‖| = 1 + ‖g ω‖ := abs_of_nonneg hbase
  simpa [Function.comp, Real.norm_eq_abs, hCabs, h1abs] using h_bound ω

omit [CompleteSpace H] in
/-- Each coordinate has finite moments; multiplying by `F(g)` preserves integrability. -/
lemma integrable_coord_mul_F
    (hg : IsGaussianHilbert g) (hF_diff : ContDiff ℝ 1 F) (hF_growth : HasModerateGrowth F) (i : hg.ι) :
    Integrable (fun ω => (coord hg.w g i ω) * F (g ω)) := by
  classical
  let c_i := coord hg.w g i
  have hc_i_L2 : Integrable (fun ω => c_i ω ^ 2) :=
    ProbabilityTheory.IsCenteredGaussianRV.integrable_sq
      (hX := (coord_isGaussian_and_indep hg).1 i)
      (hX_meas := (coord_measurable (g := g) hg i))
  have hF_L2 : Integrable (fun ω => F (g ω) ^ 2) := by
    have h_bound_sq :
        ∀ ω, |F (g ω) ^ 2| ≤ hF_growth.C ^ 2 * (1 + ‖g ω‖) ^ (2 * hF_growth.m) := by
      intro ω
      have hb : |F (g ω)| ≤ hF_growth.C * (1 + ‖g ω‖) ^ hF_growth.m :=
        hF_growth.F_bound (g ω)
      have hb2 : |F (g ω)| ^ 2
                    ≤ (hF_growth.C * (1 + ‖g ω‖) ^ hF_growth.m) ^ 2 :=
        Real.pow_le_pow_of_le_left (abs_nonneg _) hb 2
      have hR :
          (hF_growth.C * (1 + ‖g ω‖) ^ hF_growth.m) ^ 2
            = hF_growth.C ^ 2 * (1 + ‖g ω‖) ^ (2 * hF_growth.m) := by
        simp [pow_two, pow_mul, mul_comm, mul_left_comm, mul_assoc]
      simpa [abs_pow, hR] using hb2
    have h_int_poly :
        Integrable (fun ω => (1 + ‖g ω‖) ^ (2 * hF_growth.m)) := by
      simpa using integrable_one_add_norm_pow (hg := hg) (m := 2 * hF_growth.m)
    have h_int_bound := h_int_poly.const_mul (hF_growth.C ^ 2)
    have hg_meas : Measurable g := hg.repr_measurable
    have hF_meas : Measurable F := hF_diff.continuous.measurable
    refine h_int_bound.mono' ((hF_meas.comp hg_meas).pow_const 2).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun ω => ?_)
    have hpow_nonneg : 0 ≤ (1 + ‖g ω‖) ^ (2 * hF_growth.m) := by
      have : 0 ≤ 1 + ‖g ω‖ := by nlinarith [norm_nonneg (g ω)]
      exact pow_nonneg this _
    have hrhs_nonneg : 0 ≤ hF_growth.C ^ 2 * (1 + ‖g ω‖) ^ (2 * hF_growth.m) :=
      mul_nonneg (by exact sq_nonneg _) hpow_nonneg
    simpa [Real.norm_eq_abs, abs_of_nonneg hrhs_nonneg] using h_bound_sq ω
  have h_int_rhs :
      Integrable (fun ω => (1 / 2 : ℝ) * ((c_i ω) ^ 2 + (F (g ω)) ^ 2)) :=
    (hc_i_L2.add hF_L2).const_mul (1 / 2 : ℝ)
  have hc_meas : Measurable c_i := (coord_measurable (g := g) hg i)
  have hFcomp_meas : Measurable (fun ω => F (g ω)) :=
    (hF_diff.continuous.measurable).comp hg.repr_measurable
  have h_meas_prod :
      AEStronglyMeasurable (fun ω => c_i ω * F (g ω)) ℙ :=
    (hc_meas.mul hFcomp_meas).aestronglyMeasurable
  have h_dom :
      ∀ ω, |c_i ω * F (g ω)| ≤ (1 / 2 : ℝ) * ((c_i ω) ^ 2 + (F (g ω)) ^ 2) := by
    intro ω
    have hsq : 0 ≤ (|c_i ω| - |F (g ω)|) ^ 2 := sq_nonneg _
    have hcs' :
        2 * (|c_i ω| * |F (g ω)|) ≤ |c_i ω| ^ 2 + |F (g ω)| ^ 2 := by
      have := hsq
      nlinarith [pow_two (|c_i ω|), pow_two (|F (g ω)|)]
    have hcs :
        2 * |c_i ω * F (g ω)| ≤ |c_i ω| ^ 2 + |F (g ω)| ^ 2 := by
      simpa [abs_mul, mul_comm, mul_left_comm, mul_assoc] using hcs'
    have : |c_i ω * F (g ω)| ≤ (|c_i ω| ^ 2 + |F (g ω)| ^ 2) / 2 := by
      have hpos : (0 : ℝ) < 2 := by norm_num
      exact (le_div_iff₀' hpos).mpr hcs
    simpa [div_eq_mul_inv, one_div, pow_two, abs_pow, mul_add, mul_comm, mul_left_comm, mul_assoc]
      using this
  refine h_int_rhs.mono' h_meas_prod (Filter.Eventually.of_forall (fun ω => ?_))
  have hR : 0 ≤ (1 / 2 : ℝ) * ((c_i ω) ^ 2 + (F (g ω)) ^ 2) := by
    have : 0 ≤ (c_i ω) ^ 2 + (F (g ω)) ^ 2 := by exact add_nonneg (sq_nonneg _) (sq_nonneg _)
    have : 0 ≤ (1 / 2 : ℝ) * ((c_i ω) ^ 2 + (F (g ω)) ^ 2) :=
      mul_nonneg (by norm_num) this
    simpa using this
  exact h_dom ω

omit [CompleteSpace H] in
/-- The Fréchet derivative applied to a fixed direction is integrable under the growth bound. -/
lemma integrable_fderiv_apply
    (hg : IsGaussianHilbert g) (hF_diff : ContDiff ℝ 1 F)
    (hF_growth : HasModerateGrowth F) (h : H) :
    Integrable (fun ω => (fderiv ℝ F (g ω)) h) := by
  have h_bound : ∀ ω, ‖(fderiv ℝ F (g ω)) h‖
      ≤ hF_growth.C * (1 + ‖g ω‖) ^ hF_growth.m * ‖h‖ :=
    fun ω => HasModerateGrowth.bound_dF_apply hF_growth (g ω) h
  have h_int_poly : Integrable (fun ω => (1 + ‖g ω‖) ^ hF_growth.m) := by
    simpa using integrable_one_add_norm_pow (hg := hg) (m := hF_growth.m)
  have h_int_bound : Integrable (fun ω => (hF_growth.C * ‖h‖) * ((1 + ‖g ω‖) ^ hF_growth.m)) :=
    h_int_poly.const_mul (hF_growth.C * ‖h‖)
  have hg_meas : Measurable g := hg.repr_measurable
  have hF_deriv_cont : Continuous (fderiv ℝ F) :=
    hF_diff.continuous_fderiv (Ne.symm (zero_ne_one' (WithTop ℕ∞)))
  have h_comp_meas : Measurable (fun ω => fderiv ℝ F (g ω)) :=
    hF_deriv_cont.measurable.comp hg_meas
  have h_apply_meas : Measurable (fun ω => (fderiv ℝ F (g ω)) h) :=
    (ContinuousLinearMap.apply ℝ ℝ h).measurable.comp h_comp_meas
  refine h_int_bound.mono' h_apply_meas.aestronglyMeasurable (Filter.Eventually.of_forall ?_)
  intro ω
  simpa [mul_comm, mul_left_comm, mul_assoc] using h_bound ω

omit [IsProbabilityMeasure (ℙ : Measure Ω)] [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] in
/-- Interchange expectation with a finite sum. -/
lemma expectation_finset_sum
    (hg : IsGaussianHilbert g) --(hF_diff : ContDiff ℝ 1 F) (hF_growth : HasModerateGrowth F)
    (f : hg.ι → Ω → ℝ)
    (hint : ∀ i, Integrable (f i)) :
    𝔼[(fun ω => ∑ i, f i ω)] = ∑ i, 𝔼[(f i ·)] := by
  classical
  have hint' : ∀ i ∈ (Finset.univ : Finset hg.ι), Integrable (f i) := by
    intro i _; simpa using hint i
  change (∫ ω, (∑ i : hg.ι, f i ω) ∂ℙ) = ∑ i : hg.ι, (∫ ω, f i ω ∂ℙ)
  simpa using
    (integral_finset_sum (s := (Finset.univ : Finset hg.ι)) (f := fun i ω => f i ω) hint')

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- Pull out a *constant* scalar factor from expectation. -/
lemma expectation_const_mul
    (c : ℝ) {f : Ω → ℝ} (_ : Integrable f) :
    𝔼[(fun ω => c * f ω)] = c * 𝔼[f] := by
  classical
  change (∫ ω, c * f ω ∂ℙ) = c * (∫ ω, f ω ∂ℙ)
  exact MeasureTheory.integral_const_mul c f

omit [CompleteSpace H] in
/-- Weighted version: pull a finite *weighted* sum inside a continuous linear
map applied pointwise, then exchange the finite sum with expectation. -/
lemma fderiv_expectation_weighted_sum
    (hg : IsGaussianHilbert g) (hF_diff : ContDiff ℝ 1 F) (hF_growth : HasModerateGrowth F)
    (a : hg.ι → ℝ) :
    𝔼[(fun ω => (fderiv ℝ F (g ω)) (∑ i : hg.ι, (a i) • hg.w i))]
      = ∑ i : hg.ι, (a i) * 𝔼[(fun ω => (fderiv ℝ F (g ω)) (hg.w i))] := by
  classical
  have hint : ∀ i : hg.ι, Integrable (fun ω => (fderiv ℝ F (g ω)) (hg.w i)) :=
    fun i => integrable_fderiv_apply (hg := hg) (hF_diff := hF_diff)
      (hF_growth := hF_growth) (h := hg.w i)
  have pointwise :
    (fun ω => (fderiv ℝ F (g ω)) (∑ i : hg.ι, (a i) • hg.w i))
      = (fun ω => ∑ i : hg.ι, (a i) * ((fderiv ℝ F (g ω)) (hg.w i))) := by
    funext ω
    have L : H →L[ℝ] ℝ := fderiv ℝ F (g ω)
    simp [map_sum, smul_eq_mul]
  calc
    𝔼[(fun ω => (fderiv ℝ F (g ω)) (∑ i : hg.ι, (a i) • hg.w i))]
        = 𝔼[(fun ω => ∑ i : hg.ι, (a i) * ((fderiv ℝ F (g ω)) (hg.w i)))] := by
          simp
    _ = ∑ i : hg.ι, 𝔼[(fun ω => (a i) * ((fderiv ℝ F (g ω)) (hg.w i)))] := by
          simpa using
            expectation_finset_sum (hg := hg)
              (f := fun i ω => (a i) * ((fderiv ℝ F (g ω)) (hg.w i)))
              (hint := fun i => (hint i).const_mul (a i))
    _ = ∑ i : hg.ι, (a i) * 𝔼[(fun ω => (fderiv ℝ F (g ω)) (hg.w i))] := by
          refine Finset.sum_congr rfl ?_
          intro i _
          simpa [mul_comm, mul_left_comm, mul_assoc]
            using expectation_const_mul (c := (a i))
              (f := fun ω => (fderiv ℝ F (g ω)) (hg.w i))
              ((hint i))

end Integrability

/-! ## Covariance operator as a continuous linear map (rank‑one sum)
We package the covariance weights `(τ i)` and basis vectors `(w i)` into a
bounded operator `Σ : H →L[ℝ] H`. This lets us present the IBP identity in a
clean, coordinate‑free form.
-/
section CovarianceOperator

variable {g : Ω → H}
section InnerProductSpace
open scoped InnerProductSpace

/-- The continuous linear map `x ↦ ⟪v, x⟫` for a fixed `v`.
Note: this is linear in `x` for general `RCLike 𝕜`. -/
def ContinuousLinearMap.innerSL (𝕜 : Type*) [RCLike 𝕜] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (v : E) : E →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟪v, x⟫_𝕜
      map_add' := by
        intro x y
        -- ⟪v, x + y⟫ = ⟪v, x⟫ + ⟪v, y⟫
        simpa using (inner_add_right v x y)
      map_smul' := by
        intro c x
        -- ⟪v, c • x⟫ = c * ⟪v, x⟫
        simpa using (inner_smul_right v x c) }
    ‖v‖
    (fun x => by
      simpa using (norm_inner_le_norm v x))

@[simp] lemma ContinuousLinearMap.innerSL_apply
    (𝕜 : Type*) [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (v x : E) :
    (ContinuousLinearMap.innerSL 𝕜 (E := E) v) x = ⟪v, x⟫_𝕜 := rfl

end InnerProductSpace

/-- Covariance operator `Σ` built from the finite spectral data `(w, τ)`.
It is the finite sum of rank‑one projections `h ↦ ⟪h, w i⟫ • w i`, scaled by `τ i`. -/
noncomputable def covOp (hg : IsGaussianHilbert g) : H →L[ℝ] H :=
  (Finset.univ : Finset hg.ι).sum fun i =>
    (hg.τ i : ℝ) •
      ContinuousLinearMap.smulRight (ContinuousLinearMap.innerSL ℝ (hg.w i)) (hg.w i)

omit [IsProbabilityMeasure (ℙ : Measure Ω)] [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] in
@[simp] lemma covOp_apply
    {g : Ω → H} (hg : IsGaussianHilbert g) (h : H) :
    (covOp (g := g) hg) h
      = ∑ i : hg.ι, ((hg.τ i : ℝ) * ⟪h, hg.w i⟫_ℝ) • hg.w i := by
  classical
  rw [covOp, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [smul_smul, real_inner_comm]

/-- We write `Σ_hg` for the covariance operator associated
with a Gaussian Hilbert model `hg`. -/
notation3 "Σ_" hg => covOp (g := _ ) hg

omit [IsProbabilityMeasure (ℙ : Measure Ω)] [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] in
lemma covOp_symmetric
    {g : Ω → H} (hg : IsGaussianHilbert g) (x y : H) :
    ⟪(covOp (g := g) hg) x, y⟫_ℝ = ⟪x, (covOp (g := g) hg) y⟫_ℝ := by
  classical
  have L : ⟪(covOp (g := g) hg) x, y⟫_ℝ
      = ∑ i : hg.ι, (hg.τ i : ℝ) * ⟪x, hg.w i⟫_ℝ * ⟪hg.w i, y⟫_ℝ := by
    have hsum :=
      (sum_inner (𝕜 := ℝ) (E := H)
        (s := (Finset.univ : Finset hg.ι))
        (f := fun i => ((hg.τ i : ℝ) * ⟪x, hg.w i⟫_ℝ) • hg.w i)
        (x := y))
    simpa [covOp_apply (g := g) (hg := hg) x,
           real_inner_smul_left, mul_comm, mul_left_comm, mul_assoc]
      using hsum
  have R : ⟪x, (covOp (g := g) hg) y⟫_ℝ
      = ∑ i : hg.ι, (hg.τ i : ℝ) * ⟪x, hg.w i⟫_ℝ * ⟪hg.w i, y⟫_ℝ := by
    have hsum :=
      (inner_sum (𝕜 := ℝ) (E := H)
        (s := (Finset.univ : Finset hg.ι))
        (f := fun i => ((hg.τ i : ℝ) * ⟪y, hg.w i⟫_ℝ) • hg.w i)
        (x := x))
    simpa [covOp_apply (g := g) (hg := hg) y,
           real_inner_smul_right, real_inner_comm,
           mul_comm, mul_left_comm, mul_assoc]
      using hsum
  aesop

omit [IsProbabilityMeasure (ℙ : Measure Ω)] [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] in
lemma covOp_pos
    {g : Ω → H} (hg : IsGaussianHilbert g) (x : H) :
    0 ≤ ⟪(covOp (g := g) hg) x, x⟫_ℝ := by
  classical
  have hx :
      ⟪(covOp (g := g) hg) x, x⟫_ℝ
        = ∑ i : hg.ι, (hg.τ i : ℝ) * (⟪x, hg.w i⟫_ℝ)^2 := by
    have hsum :
        ⟪∑ i : hg.ι, ((hg.τ i : ℝ) * ⟪x, hg.w i⟫_ℝ) • hg.w i, x⟫_ℝ
          = ∑ i : hg.ι, ⟪((hg.τ i : ℝ) * ⟪x, hg.w i⟫_ℝ) • hg.w i, x⟫_ℝ := by
      simpa using
        (sum_inner (𝕜 := ℝ) (E := H)
          (s := (Finset.univ : Finset hg.ι))
          (f := fun i => ((hg.τ i : ℝ) * ⟪x, hg.w i⟫_ℝ) • hg.w i)
          (x := x))
    have : ∑ i : hg.ι, ⟪((hg.τ i : ℝ) * ⟪x, hg.w i⟫_ℝ) • hg.w i, x⟫_ℝ
            = ∑ i : hg.ι, (hg.τ i : ℝ) * (⟪x, hg.w i⟫_ℝ)^2 := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      calc
        ⟪((hg.τ i : ℝ) * ⟪x, hg.w i⟫_ℝ) • hg.w i, x⟫_ℝ
            = ((hg.τ i : ℝ) * ⟪x, hg.w i⟫_ℝ) * ⟪hg.w i, x⟫_ℝ := by
              rw [inner_smul_left]; simp
        _ = (hg.τ i : ℝ) * (⟪x, hg.w i⟫_ℝ * ⟪hg.w i, x⟫_ℝ) := by
              simp [mul_assoc]
        _ = (hg.τ i : ℝ) * (⟪x, hg.w i⟫_ℝ * ⟪x, hg.w i⟫_ℝ) := by
              simp [real_inner_comm]
        _ = (hg.τ i : ℝ) * (⟪x, hg.w i⟫_ℝ)^2 := by
              simp [pow_two]
    simpa [covOp_apply (g := g) (hg := hg) x] using hsum.trans this
  have hterm : ∀ i : hg.ι, 0 ≤ (hg.τ i : ℝ) * (⟪x, hg.w i⟫_ℝ)^2 := by
    intro i
    exact mul_nonneg (by exact (hg.τ i).coe_nonneg) (sq_nonneg _)
  have hsum : 0 ≤ ∑ i : hg.ι, (hg.τ i : ℝ) * (⟪x, hg.w i⟫_ℝ)^2 :=
    Finset.sum_nonneg (by intro i _; exact hterm i)
  aesop

end CovarianceOperator

/-! ## Linear test functions and covariance corollaries
For linear (or constant) test functions, the hypotheses are automatic. This
section packages some convenient special cases and algebraic consequences.
-/
section LinearTestFunctions

variable {g : Ω → H}

/-- Constant functions have moderate growth. -/
def hasModerateGrowth_const (c : ℝ) :
    HasModerateGrowth (fun _ : H => c) := by
  classical
  refine ⟨|c| + 1, 0, by exact add_pos_of_nonneg_of_pos (abs_nonneg c) zero_lt_one, ?F, ?dF⟩
  · intro z
    have : |c| ≤ |c| + 1 := by nlinarith [abs_nonneg c]
    simp [pow_zero]
  · intro z
    have : (0 : ℝ) ≤ |c| + 1 := by nlinarith [abs_nonneg c]
    simpa [fderiv_const, pow_zero, one_mul] using this

/-- Continuous linear maps have moderate growth with linear exponent. -/
def hasModerateGrowth_of_clm (L : H →L[ℝ] ℝ) :
    HasModerateGrowth (fun z : H => L z) := by
  classical
  refine ⟨‖L‖ + 1, 1, by exact add_pos_of_nonneg_of_pos (norm_nonneg (L : H →L[ℝ] ℝ)) zero_lt_one, ?F, ?dF⟩
  · intro z
    have h₁ : |L z| ≤ ‖L‖ * ‖z‖ := by simpa using L.le_opNorm z
    have h₂ : ‖L‖ * ‖z‖ ≤ (‖L‖ + 1) * (1 + ‖z‖) := by
      have hL : ‖L‖ ≤ ‖L‖ + 1 := by nlinarith [norm_nonneg (L : H →L[ℝ] ℝ)]
      have hz : ‖z‖ ≤ 1 + ‖z‖ := by nlinarith [norm_nonneg z]
      exact (mul_le_mul_of_nonneg_left hz (by nlinarith [norm_nonneg (L : H →L[ℝ] ℝ)])).trans
        (by nlinarith [norm_nonneg (L : H →L[ℝ] ℝ), norm_nonneg z])
    have : |L z| ≤ (‖L‖ + 1) * (1 + ‖z‖) := h₁.trans h₂
    simpa [pow_one] using this
  · intro z
    have hderiv : fderiv ℝ (fun x : H => L x) z = L := by
      simp
    have hL' : ‖L‖ ≤ (‖L‖ + 1) * (1 + ‖z‖) := by
      have h1 : ‖L‖ ≤ ‖L‖ + 1 := by nlinarith [norm_nonneg (L : H →L[ℝ] ℝ)]
      have h2 : (1 : ℝ) ≤ 1 + ‖z‖ := by nlinarith [norm_nonneg z]
      have h3 : ‖L‖ * 1 ≤ (‖L‖ + 1) * (1 + ‖z‖) := by
        exact mul_le_mul h1 h2 (by norm_num) (by nlinarith [norm_nonneg (L : H →L[ℝ] ℝ)])
      simpa using h3
    simpa [hderiv, pow_one] using hL'

end LinearTestFunctions

/-! ## Parameterized 1D Stein step along a coordinate
Fix a basis index `i`. Write the coordinate vector as `x := coord w g i` and
collect the remaining coordinates as a parameter `y`. For

```
φ (x : ℝ) (y : (hg.ι \ {i}) → ℝ) := F ( ∑ j ≠ i, (y j) • w j + x • w i ),
```

the 1D Stein identity applied to `x` (with `y` fixed) yields

```
E[ x * φ(x,y) ] = (τ i) * E[ ∂_x φ(x,y) ].
```

Integrating both sides with respect to `y` gives the desired coordinate step.
We package this as a lemma whose proof will unfold the conditional expectation
arguments.
-/
section CoordLineAndDecomposition

open scoped BigOperators
open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]

namespace CoordLine
section
/-- Index of the “complement” coordinates when singling out `i`. -/
@[simp] def Comp (ι : Type*) (i : ι) := { j : ι // j ≠ i }

variable {ι : Type*} [Fintype ι]
variable (w : OrthonormalBasis ι ℝ H)


/-- Finite instance for the complement subtype `{j // j ≠ i}`. -/
noncomputable instance instFintypeComp (i : ι) [DecidableEq ι] : Fintype (Comp ι i) :=
  Subtype.fintype (fun j : ι => j ≠ i)

/-- Build back a vector in `H` from a complement family and a coordinate along `w i`. -/
@[simp] def buildAlong [DecidableEq ι] (i : ι) (y : Comp ι i → ℝ) (x : ℝ) : H :=
  (∑ j : Comp ι i, (y j) • w j.1) + x • w i

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] in
/-- Finite-sum splitting identity along a fixed coordinate `i`. -/
lemma sum_split_along [DecidableEq ι] (i : ι) (a : ι → ℝ) :
  (∑ j, (a j) • w j) = (∑ j : Comp ι i, (a j.1) • w j.1) + (a i) • w i := by
  classical
  have hi : i ∈ (Finset.univ : Finset ι) := by simp
  have hsplit :
      (∑ j ∈ (Finset.univ.erase i), (a j) • w j) + (a i) • w i
        = ∑ j, (a j) • w j := by
    simp
  have hattach :
      (∑ j : {j // j ∈ (Finset.univ.erase i)}, (a j.1) • w j.1)
        = (∑ j ∈ (Finset.univ.erase i), (a j) • w j) := by
    simpa using
      (Finset.sum_attach (s := (Finset.univ.erase i))
        (f := fun j => (a j) • w j))
  let e : Comp ι i ≃ {j // j ∈ (Finset.univ.erase i)} :=
  { toFun := fun j =>
      ⟨j.1, by
        exact Finset.mem_erase.mpr ⟨j.2, by simp⟩⟩
    , invFun := fun j => ⟨j.1, (Finset.mem_erase.mp j.2).1⟩
    , left_inv := by
        intro j; cases j with
        | mk x hx => simp
    , right_inv := by
        intro j; cases j with
        | mk x hx =>
            rcases Finset.mem_erase.mp hx with ⟨hxi, hxU⟩
            simp}
  have htransport :
      (∑ j : {j // j ∈ (Finset.univ.erase i)}, (a j.1) • w j.1)
        = ∑ j : Comp ι i, (a j.1) • w j.1 := by
    simpa [e] using
      (e.symm.sum_comp (fun j => (a j.1) • w j.1))
  have hsub :
      (∑ j ∈ (Finset.univ.erase i), (a j) • w j)
        = ∑ j : Comp ι i, (a j.1) • w j.1 := by
    calc
      (∑ j ∈ (Finset.univ.erase i), (a j) • w j)
          = (∑ j : {j // j ∈ (Finset.univ.erase i)}, (a j.1) • w j.1) := by
            simpa using hattach.symm
      _ = (∑ j : Comp ι i, (a j.1) • w j.1) := htransport
  simpa [hsub] using hsplit.symm

/-- With coefficients `c : ι → Ω → ℝ`, the random vector `g` splits into complement + i-th. -/
lemma repr_split_along
  {Ω : Type*} [MeasureSpace Ω] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
  (w : OrthonormalBasis ι ℝ H) (i : ι) (c : ι → Ω → ℝ) :
  ∀ ω, (∑ j, (c j ω) • w j) = buildAlong (w := w) i (fun j => c j.1 ω) (c i ω) := by
  intro ω
  classical
  simpa [buildAlong] using
    sum_split_along (w := w) (i := i) (a := fun j => c j ω)

/-- Decomposition of `g` along `w i`: complement + `i`-th coordinate. -/
lemma g_decomp_along
  {Ω : Type*} [MeasureSpace Ω] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
  {g : Ω → H}
  (hg : PhysLean.Probability.GaussianIBP.IsGaussianHilbert (Ω := Ω) (H := H) g)
  [DecidableEq hg.ι]
  (i : hg.ι) :
  ∀ ω, g ω = buildAlong (w := hg.w) i (fun j => hg.c j.1 ω) (hg.c i ω) := by
  intro ω
  classical
  simpa [hg.repr] using
    repr_split_along (w := hg.w) (i := i) (c := hg.c) ω
end
end CoordLine
end CoordLineAndDecomposition

section JointLawFubini

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- If `Y` and `X` are independent measurable maps, the law of `(Y,X)` is the product of laws. -/
lemma map_pair_eq_prod_of_indep
  {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  (Y : Ω → α) (X : Ω → β)
  (hY : Measurable Y) (hX : Measurable X)
  (hIndep : ProbabilityTheory.IndepFun Y X (ℙ : Measure Ω)) :
  Measure.map (fun ω => (Y ω, X ω)) (ℙ : Measure Ω)
    = (Measure.map Y (ℙ : Measure Ω)).prod (Measure.map X (ℙ : Measure Ω)) := by
  classical
  exact
    (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      (μ := (ℙ : Measure Ω)) (hf := hY.aemeasurable) (hg := hX.aemeasurable)).1 hIndep

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- Change of variables for the pair map `(Y, X)`: no independence needed. -/
lemma integral_pair_change_of_variables
  {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  (Y : Ω → α) (X : Ω → β)
  (hY : Measurable Y) (hX : Measurable X)
  {φ : α × β → ℝ} (hφ_meas : Measurable φ) :
  ∫ ω, φ (Y ω, X ω) ∂ℙ = ∫ p, φ p ∂(Measure.map (fun ω => (Y ω, X ω)) ℙ) := by
  have hYX : AEMeasurable (fun ω => (Y ω, X ω)) ℙ := (hY.prodMk hX).aemeasurable
  have hφ : AEStronglyMeasurable φ (Measure.map (fun ω => (Y ω, X ω)) ℙ) :=
    hφ_meas.aestronglyMeasurable
  have h := MeasureTheory.integral_map hYX hφ
  simpa [Function.comp_def] using h.symm

/-- Same as `map_pair_eq_prod_of_indep` but only assuming a.e.-measurability of `Y` and `X`. -/
lemma map_pair_eq_prod_of_indep₀
  {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  (Y : Ω → α) (X : Ω → β)
  (hY : AEMeasurable Y ℙ) (hX : AEMeasurable X ℙ)
  (hIndep : ProbabilityTheory.IndepFun Y X ℙ) :
  Measure.map (fun ω => (Y ω, X ω)) ℙ
    = (Measure.map Y ℙ).prod (Measure.map X ℙ) := by
  classical
  exact
    (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      (μ := (ℙ : Measure Ω)) (hf := hY) (hg := hX)).1 hIndep

/-- Integration against the joint distribution of independent random variables
can be rewritten against the product of marginals (no integrability assumption needed). -/
lemma integral_joint_eq_integral_prod_of_indep_min
  {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  (Y : Ω → α) (X : Ω → β)
  (hY : Measurable Y) (hX : Measurable X)
  (hIndep : ProbabilityTheory.IndepFun Y X ℙ)
  {φ : α × β → ℝ} (hφ_meas : Measurable φ) :
  ∫ ω, φ (Y ω, X ω) ∂ℙ = ∫ p, φ p ∂((Measure.map Y ℙ).prod (Measure.map X ℙ)) := by
  have hchg := integral_pair_change_of_variables Y X hY hX hφ_meas
  have hmap := map_pair_eq_prod_of_indep Y X hY hX hIndep
  simp [hchg, hmap]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/- Transfer L¹-finiteness from composition to pushforward measure via change of variables. -/
/-- Change of variables for the pair map `(Y, X)` (no independence needed). -/
lemma lintegral_map_pair_eq_lintegral_comp
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (Y : Ω → α) (X : Ω → β)
    (hY : Measurable Y) (hX : Measurable X)
    {φ : α × β → ℝ} (hφ_meas : Measurable φ) :
    ∫⁻ p, (‖φ p‖₊ : ℝ≥0∞) ∂(Measure.map (fun ω => (Y ω, X ω)) ℙ)
      = ∫⁻ ω, (‖φ (Y ω, X ω)‖₊ : ℝ≥0∞) ∂ℙ := by
  have h_meas_norm : Measurable (fun p : α × β => (‖φ p‖₊ : ℝ≥0∞)) := by
    have h_norm_phi_meas : Measurable fun p => ‖φ p‖ := hφ_meas.norm
    have h_ofReal_meas : Measurable ENNReal.ofReal := ENNReal.measurable_ofReal
    simp only [measurable_coe_nnreal_ennreal_iff]
    exact Measurable.nnnorm hφ_meas
  refine lintegral_map h_meas_norm ?_
  exact Measurable.prodMk hY hX

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- Transfer integrability from the composition `φ ∘ (Y,X)` to `φ` under the push-forward law. -/
lemma integrable_map_pair_of_integrable_comp
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (Y : Ω → α) (X : Ω → β)
    (hY : Measurable Y) (hX : Measurable X)
    {φ : α × β → ℝ} (hφ_meas : Measurable φ)
    (hInt : Integrable (fun ω => φ (Y ω, X ω)) ℙ) :
    Integrable φ (Measure.map (fun ω => (Y ω, X ω)) ℙ) := by
  classical
  have hφ_aes : AEStronglyMeasurable φ (Measure.map (fun ω => (Y ω, X ω)) ℙ) :=
    hφ_meas.aestronglyMeasurable
  have h_norm_id :=
    lintegral_map_pair_eq_lintegral_comp Y X hY hX hφ_meas
  have hFin_comp : HasFiniteIntegral (fun ω => φ (Y ω, X ω)) ℙ := hInt.hasFiniteIntegral
  have hFin_push :
      HasFiniteIntegral φ (Measure.map (fun ω => (Y ω, X ω)) ℙ) := by
    refine (hasFiniteIntegral_def φ (Measure.map (fun ω => (Y ω, X ω)) ℙ)).mpr ?_
    exact lt_of_eq_of_lt h_norm_id hFin_comp
  exact ⟨hφ_aes, hFin_push⟩

/-- Transfer integrability from the push-forward law to the product law, using independence. -/
lemma integrable_prod_of_integrable_map_pair_of_indep
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (Y : Ω → α) (X : Ω → β)
    (hY : Measurable Y) (hX : Measurable X)
    (hIndep : ProbabilityTheory.IndepFun Y X ℙ)
    {φ : α × β → ℝ} --(hφ_meas : Measurable φ)
    (hInt_map : Integrable φ (Measure.map (fun ω => (Y ω, X ω)) ℙ)) :
    Integrable φ ((Measure.map Y ℙ).prod (Measure.map X ℙ)) := by
  have hmap :
      Measure.map (fun ω => (Y ω, X ω)) ℙ
        = (Measure.map Y ℙ).prod (Measure.map X ℙ) :=
    map_pair_eq_prod_of_indep Y X hY hX hIndep
  simpa [hmap] using hInt_map

/-- Transfer integrability from the composition to the product law (needed for Fubini). -/
lemma integrable_on_prod_of_indep_of_integrable_comp
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (Y : Ω → α) (X : Ω → β)
    (hY : Measurable Y) (hX : Measurable X)
    (hIndep : ProbabilityTheory.IndepFun Y X ℙ)
    {φ : α × β → ℝ} (hφ_meas : Measurable φ)
    (hInt : Integrable (fun ω => φ (Y ω, X ω)) ℙ) :
    Integrable φ ((Measure.map Y ℙ).prod (Measure.map X ℙ)) := by
  have hInt_map :=
    integrable_map_pair_of_integrable_comp Y X hY hX hφ_meas hInt
  exact
    integrable_prod_of_integrable_map_pair_of_indep
      Y X hY hX hIndep hInt_map

/-- Wrapper with the original name/signature kept for compatibility:
the integrability assumption is not needed for the equality, so it is ignored. -/
lemma integral_joint_eq_integral_prod_of_indep
  {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  (Y : Ω → α) (X : Ω → β)
  (hY : Measurable Y) (hX : Measurable X)
  (hIndep : ProbabilityTheory.IndepFun Y X ℙ)
  {φ : α × β → ℝ}
  (hφ_meas : Measurable φ)
  (_hInt : Integrable (fun ω => φ (Y ω, X ω)) ℙ) :
  ∫ ω, φ (Y ω, X ω) ∂ℙ = ∫ p, φ p ∂((Measure.map Y ℙ).prod (Measure.map X ℙ)) :=
  integral_joint_eq_integral_prod_of_indep_min Y X hY hX hIndep hφ_meas

/-- Fubini factorisation when `Y` and `X` are independent. -/
lemma integral_pair_via_prod
    {α β : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
    [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    (Y : Ω → α) (X : Ω → β)
    (hY : Measurable Y) (hX : Measurable X)
    (hIndep : ProbabilityTheory.IndepFun Y X ℙ)
    {Ψ : α → β → ℝ}
    (hΨ_meas : Measurable (fun p : α × β => Ψ p.1 p.2))
    (hInt : Integrable (fun ω => Ψ (Y ω) (X ω)) ℙ) :
    ∫ ω, Ψ (Y ω) (X ω) ∂ℙ
      = ∫ y, ∫ x, Ψ y x ∂(Measure.map X ℙ) ∂(Measure.map Y ℙ) := by
  classical
  set φ : α × β → ℝ := fun p => Ψ p.1 p.2
  have h1 :=
    integral_joint_eq_integral_prod_of_indep_min Y X hY hX hIndep (hφ_meas := hΨ_meas)
  have hInt_prod :
      Integrable φ ((Measure.map Y ℙ).prod (Measure.map X ℙ)) :=
    integrable_on_prod_of_indep_of_integrable_comp
      Y X hY hX hIndep (hφ_meas := hΨ_meas) (hInt := by simpa [φ] using hInt)
  have h2 :
      ∫ p, φ p ∂((Measure.map Y ℙ).prod (Measure.map X ℙ))
        = ∫ y, ∫ x, Ψ y x ∂(Measure.map X ℙ) ∂(Measure.map Y ℙ) := by
    simpa [φ] using
      MeasureTheory.integral_prod
        (μ := Measure.map Y ℙ) (ν := Measure.map X ℙ) φ hInt_prod
  simpa [φ] using (h1.trans h2)

/-- If `X` is a real-valued random variable with Gaussian law `gaussianReal 0 v`,
independent of `Y`, and if `ω ↦ φ (Y ω, X ω)` is integrable, then `φ` is integrable
with respect to the product measure `(map Y ℙ) × (gaussianReal 0 v)`.

This is a Gaussian specialization of `integrable_on_prod_of_indep_of_integrable_comp`. -/
lemma integrable_phi_on_mapY_prod_gauss
  {α : Type*} [MeasurableSpace α]
  (Y : Ω → α) (X : Ω → ℝ)
  (hY : Measurable Y) (hX : Measurable X)
  (hIndep : ProbabilityTheory.IndepFun Y X ℙ)
  (v : ℝ≥0) (hXlaw : Measure.map X ℙ = ProbabilityTheory.gaussianReal 0 v)
  {φ : α × ℝ → ℝ} (hφ_meas : Measurable φ)
  (hInt : Integrable (fun ω => φ (Y ω, X ω)) ℙ) :
  Integrable φ ((Measure.map Y ℙ).prod (ProbabilityTheory.gaussianReal 0 v)) := by
  have hInt_prod :
      Integrable φ ((Measure.map Y ℙ).prod (Measure.map X ℙ)) :=
    integrable_on_prod_of_indep_of_integrable_comp
      Y X hY hX hIndep hφ_meas hInt
  simpa [hXlaw] using hInt_prod

lemma integrable_psi_on_mapY_prod_gauss
  {α : Type*} [MeasurableSpace α]
  (Y : Ω → α) (X : Ω → ℝ)
  (hY : Measurable Y) (hX : Measurable X)
  (hIndep : ProbabilityTheory.IndepFun Y X ℙ)
  (v : ℝ≥0) (hXlaw : Measure.map X ℙ = ProbabilityTheory.gaussianReal 0 v)
  {ψ : α × ℝ → ℝ} (hψ_meas : Measurable ψ)
  (hInt : Integrable (fun ω => ψ (Y ω, X ω)) ℙ) :
  Integrable ψ ((Measure.map Y ℙ).prod (ProbabilityTheory.gaussianReal 0 v)) := by
  have hInt_prod :
      Integrable ψ ((Measure.map Y ℙ).prod (Measure.map X ℙ)) :=
    integrable_on_prod_of_indep_of_integrable_comp
      Y X hY hX hIndep hψ_meas hInt
  simpa [hXlaw] using hInt_prod

end JointLawFubini

section SliceCalculus

open scoped BigOperators
open MeasureTheory ProbabilityTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]

namespace CoordLine

variable {ι : Type*} [Fintype ι]
variable (w : OrthonormalBasis ι ℝ H) (i : ι)

/-- The linear map `ℝ →L[ℝ] H`, `x ↦ x • w i`. -/
@[simp] def lineCLM : ℝ →L[ℝ] H := (1 : ℝ →L[ℝ] ℝ).smulRight (w i)

/-- Affine line map `x ↦ z + x • w i`. -/
@[simp] def line (z : H) : ℝ → H := fun x => z + (lineCLM (w := w) (i := i)) x

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] in
lemma line_def (z : H) (x : ℝ) : line (w := w) (i := i) z x = z + x • w i := rfl

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] in
/-- Chain rule for the 1D slice of a `C¹` test `F : H → ℝ`. -/
lemma deriv_F_along (F : H → ℝ) (hF : ContDiff ℝ 1 F) (z : H) :
  ∀ x, deriv (fun t => F (line (w := w) (i := i) z t)) x
        = (fderiv ℝ F (line (w := w) (i := i) z x)) (w i) := by
  intro x
  have hline : HasFDerivAt (line (w := w) (i := i) z)
      (lineCLM (w := w) (i := i)) x :=
    (lineCLM (w := w) (i := i)).hasFDerivAt.const_add z
  have hF' : HasFDerivAt F (fderiv ℝ F (line (w := w) (i := i) z x))
      (line (w := w) (i := i) z x) :=
    (hF.differentiable one_ne_zero _).hasFDerivAt
  have hcomp := hF'.comp x hline
  have hderiv :
      HasDerivAt (fun t => F (line (w := w) (i := i) z t))
        (((fderiv ℝ F (line (w := w) (i := i) z x)).comp
            (lineCLM (w := w) (i := i))) 1) x := by
    simpa using hcomp.hasDerivAt
  have hCLM1 : (lineCLM (w := w) (i := i)) 1 = w i := by
    simp [lineCLM]
  simpa [ContinuousLinearMap.comp_apply, hCLM1] using hderiv.deriv

/-!
Split moderateGrowth_along into general affine lemmas and a thin ONB wrapper.
-/
namespace AffineModerateGrowth

open Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Basic affine bound along a line:
`1 + ‖z + L x‖ ≤ (1 + ‖z‖ + ‖L‖) * (1 + |x|)`. -/
lemma one_add_norm_comp_affine_le
    (z : E) (L : ℝ →L[ℝ] E) (x : ℝ) :
  1 + ‖z + L x‖ ≤ (1 + ‖z‖ + ‖L‖) * (1 + |x|) := by
  have h_tri : ‖z + L x‖ ≤ ‖z‖ + ‖L x‖ := norm_add_le _ _
  have h_op : ‖L x‖ ≤ ‖L‖ * ‖x‖ := L.le_opNorm x
  have hx : ‖x‖ = |x| := by simp [Real.norm_eq_abs]
  have h1 : 1 + ‖z + L x‖ ≤ 1 + ‖z‖ + ‖L‖ * |x| := by
    calc
      1 + ‖z + L x‖ ≤ 1 + (‖z‖ + ‖L x‖) := by simpa only [add_assoc] using ((add_le_add_iff_left 1).mpr h_tri)
      _ = 1 + ‖z‖ + ‖L x‖ := by simp [add_assoc]
      _ ≤ 1 + ‖z‖ + ‖L‖ * |x| := by simpa [hx] using add_le_add_left h_op (1 + ‖z‖)
  have h_nonneg_z : 0 ≤ 1 + ‖z‖ := by nlinarith [norm_nonneg z]
  have h_one_le : 1 ≤ 1 + |x| := by linarith [abs_nonneg x]
  have h_left_mul : 1 + ‖z‖ ≤ (1 + ‖z‖) * (1 + |x|) :=
    le_mul_of_one_le_right h_nonneg_z h_one_le
  have h_x_le : |x| ≤ 1 + |x| := by linarith [abs_nonneg x]
  have h_right_mul : ‖L‖ * |x| ≤ ‖L‖ * (1 + |x|) :=
    mul_le_mul_of_nonneg_left h_x_le (norm_nonneg (L : ℝ →L[ℝ] E))
  have h_sum : 1 + ‖z‖ + ‖L‖ * |x| ≤ (1 + ‖z‖) * (1 + |x|) + ‖L‖ * (1 + |x|) :=
    add_le_add h_left_mul h_right_mul
  have : (1 + ‖z‖) * (1 + |x|) + ‖L‖ * (1 + |x|) = (1 + ‖z‖ + ‖L‖) * (1 + |x|) := by
    simp [mul_add, add_comm, add_left_comm, add_assoc, mul_comm]
  calc
    1 + ‖z + L x‖ ≤ 1 + ‖z‖ + ‖L‖ * |x| := h1
    _ ≤ (1 + ‖z‖ + ‖L‖) * (1 + |x|) := by simpa using (le_trans h_sum (le_of_eq this))

/-- Power version of the previous bound. -/
lemma pow_le_pow_one_add_norm_comp_affine
    (z : E) (L : ℝ →L[ℝ] E) (x : ℝ) (m : ℕ) :
  (1 + ‖z + L x‖) ^ m ≤ ((1 + ‖z‖ + ‖L‖) * (1 + |x|)) ^ m := by
  have hbase : 0 ≤ 1 + ‖z + L x‖ := by nlinarith [norm_nonneg (z + L x)]
  exact Real.pow_le_pow_of_le_left hbase (one_add_norm_comp_affine_le z L x) m

/-- Chain rule for slicing `F : E → ℝ` along an affine line `x ↦ z + L x`. -/
lemma deriv_comp_affine
    {F : E → ℝ} (hF : ContDiff ℝ 1 F) (z : E) (L : ℝ →L[ℝ] E) (x : ℝ) :
  deriv (fun t => F (z + L t)) x = (fderiv ℝ F (z + L x)) (L 1) := by
  have hline : HasFDerivAt (fun t : ℝ => z + L t) L x := L.hasFDerivAt.const_add z
  have hF' : HasFDerivAt F (fderiv ℝ F (z + L x)) (z + L x) :=
    (hF.differentiable one_ne_zero _).hasFDerivAt
  have hcomp := hF'.comp x hline
  have : HasDerivAt (fun t => F (z + L t))
          (((fderiv ℝ F (z + L x)).comp L) 1) x := hcomp.hasDerivAt
  simpa [ContinuousLinearMap.comp_apply] using this.deriv

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

lemma bound_dF_apply {F : H → ℝ} (hMG : HasModerateGrowth F) (z h : H) :
    ‖(fderiv ℝ F z) h‖ ≤ hMG.C * (1 + ‖z‖) ^ hMG.m * ‖h‖ := by
  have h_op : ‖(fderiv ℝ F z) h‖ ≤ ‖fderiv ℝ F z‖ * ‖h‖ := ContinuousLinearMap.le_opNorm _ _
  have h_coeff_nonneg : 0 ≤ ‖h‖ := norm_nonneg _
  have h_body_le : ‖fderiv ℝ F z‖ * ‖h‖ ≤ (hMG.C * (1 + ‖z‖) ^ hMG.m) * ‖h‖ :=
    mul_le_mul_of_nonneg_right (hMG.dF_bound z) h_coeff_nonneg
  exact h_op.trans h_body_le

/-- General affine bound: `1 + ‖z + L x‖ ≤ (1 + ‖z‖ + ‖L‖) * (1 + ‖x‖)` for L : E' →L[ℝ] E. -/
lemma one_add_norm_comp_affine_le'
    {E' E : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (z : E) (L : E' →L[ℝ] E) (x : E') :
  1 + ‖z + L x‖ ≤ (1 + ‖z‖ + ‖L‖) * (1 + ‖x‖) := by
  have h_tri : ‖z + L x‖ ≤ ‖z‖ + ‖L x‖ := norm_add_le _ _
  have h_op : ‖L x‖ ≤ ‖L‖ * ‖x‖ := L.le_opNorm x
  have h1 : 1 + ‖z + L x‖ ≤ 1 + ‖z‖ + ‖L‖ * ‖x‖ := by
    calc
      1 + ‖z + L x‖ ≤ 1 + (‖z‖ + ‖L x‖) := by simpa [add_assoc] using (norm_add_le z (L x))
      _ = 1 + ‖z‖ + ‖L x‖ := by simp [add_assoc]
      _ ≤ 1 + ‖z‖ + ‖L‖ * ‖x‖ := by simpa using add_le_add_left h_op (1 + ‖z‖)
  have hx : ‖x‖ ≤ 1 + ‖x‖ := by nlinarith [norm_nonneg (x : E')]
  have hz : 0 ≤ 1 + ‖z‖ := by nlinarith [norm_nonneg (z : E)]
  have h_left : 1 + ‖z‖ ≤ (1 + ‖z‖) * (1 + ‖x‖) := le_mul_of_one_le_right hz (by nlinarith [norm_nonneg (x : E')])
  have h_right : ‖L‖ * ‖x‖ ≤ ‖L‖ * (1 + ‖x‖) := mul_le_mul_of_nonneg_left hx (norm_nonneg (L : E' →L[ℝ] E))
  have h_sum := add_le_add h_left h_right
  have : (1 + ‖z‖) * (1 + ‖x‖) + ‖L‖ * (1 + ‖x‖) = (1 + ‖z‖ + ‖L‖) * (1 + ‖x‖) := by ring
  exact (le_trans h1 (le_trans (le_of_eq (by simp)) h_sum)).trans (le_of_eq (by simp [this]))

/-- Power version. -/
lemma pow_le_pow_one_add_norm_comp_affine'
    {E' E : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (z : E) (L : E' →L[ℝ] E) (x : E') (m : ℕ) :
  (1 + ‖z + L x‖) ^ m ≤ ((1 + ‖z‖ + ‖L‖) * (1 + ‖x‖)) ^ m := by
  have hbase : 0 ≤ 1 + ‖z + L x‖ := by nlinarith [norm_nonneg (z + L x)]
  exact Real.pow_le_pow_of_le_left hbase (one_add_norm_comp_affine_le' z L x) m

/-- Value bound after composing F : E → ℝ with affine line x ↦ z + L x (real parameter). -/
lemma growth_bound_comp_affine_real_value
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℝ}
    (hMG : PhysLean.Probability.GaussianIBP.HasModerateGrowth F)
    (z : E) (L : ℝ →L[ℝ] E) :
  ∀ x : ℝ,
    |F (z + L x)|
      ≤ (hMG.C * (1 + ‖z‖ + ‖L‖) ^ hMG.m) * (1 + |x|) ^ hMG.m := by
  intro x
  have hF := hMG.F_bound (z + L x)
  have hpow := pow_le_pow_one_add_norm_comp_affine' (z := z) (L := L) (x := x) (m := hMG.m)
  have hx : ‖x‖ = |x| := by simp
  calc
    |F (z + L x)| ≤ hMG.C * (1 + ‖z + L x‖) ^ hMG.m := hF
    _ ≤ hMG.C * (((1 + ‖z‖ + ‖L‖) * (1 + ‖x‖)) ^ hMG.m) := by exact mul_le_mul_of_nonneg_left hpow (le_of_lt hMG.Cpos)
    _ = (hMG.C * (1 + ‖z‖ + ‖L‖) ^ hMG.m) * (1 + |x|) ^ hMG.m := by simp [mul_pow, hx, mul_comm, mul_left_comm]

/-- Derivative bound after composing F : E → ℝ with affine line x ↦ z + L x (real parameter). -/
lemma growth_bound_comp_affine_real_deriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℝ}
    (hF_diff : ContDiff ℝ 1 F)
    (hMG : PhysLean.Probability.GaussianIBP.HasModerateGrowth F)
    (z : E) (L : ℝ →L[ℝ] E) :
  ∀ x : ℝ,
    |deriv (fun t => F (z + L t)) x|
      ≤ (hMG.C * (1 + ‖z‖ + ‖L‖) ^ hMG.m * (1 + ‖L‖)) * (1 + |x|) ^ hMG.m := by
  intro x
  have hderiv := deriv_comp_affine (hF := hF_diff) (z := z) (L := L) (x := x)
  have hL1 : ‖L 1‖ ≤ ‖L‖ := by
    simpa [Real.norm_eq_abs, abs_one, mul_one] using (L.le_opNorm (1 : ℝ))
  have h_df : ‖fderiv ℝ F (z + L x)‖ ≤ hMG.C * (1 + ‖z + L x‖) ^ hMG.m := hMG.dF_bound _
  have hval :
      |(fderiv ℝ F (z + L x)) (L 1)| ≤ ‖fderiv ℝ F (z + L x)‖ * ‖L 1‖ := by
    simpa [Real.norm_eq_abs] using
      (ContinuousLinearMap.le_opNorm (fderiv ℝ F (z + L x)) (L 1))
  have h1 :
      |deriv (fun t => F (z + L t)) x|
        ≤ hMG.C * (1 + ‖z + L x‖) ^ hMG.m * ‖L‖ := by
    have := calc
      |(fderiv ℝ F (z + L x)) (L 1)|
            ≤ ‖fderiv ℝ F (z + L x)‖ * ‖L 1‖ := hval
      _ ≤ ‖fderiv ℝ F (z + L x)‖ * ‖L‖ := mul_le_mul_of_nonneg_left hL1 (norm_nonneg _)
      _ ≤ hMG.C * (1 + ‖z + L x‖) ^ hMG.m * ‖L‖ :=
            mul_le_mul_of_nonneg_right h_df (norm_nonneg _)
    simpa [hderiv, mul_comm, mul_left_comm, mul_assoc] using this
  have hL_le : ‖L‖ ≤ 1 + ‖L‖ := by nlinarith [norm_nonneg (L : ℝ →L[ℝ] E)]
  have coeff_nonneg :
      0 ≤ hMG.C * (1 + ‖z + L x‖) ^ hMG.m :=
    mul_nonneg (le_of_lt hMG.Cpos) (pow_nonneg (by nlinarith [norm_nonneg (z + L x)]) _)
  have h2 :
      hMG.C * (1 + ‖z + L x‖) ^ hMG.m * ‖L‖
        ≤ hMG.C * (1 + ‖z + L x‖) ^ hMG.m * (1 + ‖L‖) :=
    mul_le_mul_of_nonneg_left hL_le coeff_nonneg
  have hx : ‖x‖ = |x| := by simp
  have hpow₀ :=
    pow_le_pow_one_add_norm_comp_affine' (z := z) (L := L) (x := x) (m := hMG.m)
  have hpow' :
      (1 + ‖z + L x‖) ^ hMG.m
        ≤ (1 + ‖z‖ + ‖L‖) ^ hMG.m * (1 + |x|) ^ hMG.m := by
    simpa [mul_pow, hx] using hpow₀
  have h3 :
      hMG.C * (1 + ‖z + L x‖) ^ hMG.m * (1 + ‖L‖)
        ≤ (hMG.C * (1 + ‖z‖ + ‖L‖) ^ hMG.m * (1 + ‖L‖)) * (1 + |x|) ^ hMG.m := by
    have t1 := mul_le_mul_of_nonneg_left hpow' (le_of_lt hMG.Cpos)
    have h1L : 0 ≤ 1 + ‖L‖ := by nlinarith [norm_nonneg (L : ℝ →L[ℝ] E)]
    have t2 := mul_le_mul_of_nonneg_right t1 h1L
    simpa [mul_comm, mul_left_comm, mul_assoc, mul_pow] using t2
  exact (h1.trans (h2.trans h3))

/-- Thin wrapper: moderate growth for x ↦ F (z + L x). -/
lemma moderateGrowth_comp_affine_real
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℝ} (hF_diff : ContDiff ℝ 1 F)
    (hMG : PhysLean.Probability.GaussianIBP.HasModerateGrowth F)
    (z : E) (L : ℝ →L[ℝ] E) :
  ProbabilityTheory.HasModerateGrowth (fun x : ℝ => F (z + L x)) := by
  set A : ℝ := 1 + ‖z‖ + ‖L‖
  set C' : ℝ := hMG.C * A ^ hMG.m * (1 + ‖L‖)
  have hApos : 0 < A := by nlinarith [norm_nonneg z, norm_nonneg (L : ℝ →L[ℝ] E)]
  have hAmpos : 0 < A ^ hMG.m := pow_pos hApos _
  have hLpos : 0 < (1 + ‖L‖) := by nlinarith [norm_nonneg (L : ℝ →L[ℝ] E)]
  have hC'pos : 0 < C' := mul_pos (mul_pos hMG.Cpos hAmpos) hLpos
  refine ⟨C', hMG.m, hC'pos, ?_, ?_⟩
  · intro x
    exact (growth_bound_comp_affine_real_value (hMG := hMG) (z := z) (L := L) x).trans (by
      have hfac : (hMG.C * A ^ hMG.m) ≤ C' := by
        have hL1 : 1 ≤ 1 + ‖L‖ := by nlinarith [norm_nonneg (L : ℝ →L[ℝ] E)]
        have hnonneg : 0 ≤ hMG.C * A ^ hMG.m :=
          mul_nonneg (le_of_lt hMG.Cpos) (pow_nonneg (le_of_lt hApos) _)
        calc
          hMG.C * A ^ hMG.m = (hMG.C * A ^ hMG.m) * 1 := by ring
          _ ≤ (hMG.C * A ^ hMG.m) * (1 + ‖L‖) := mul_le_mul_of_nonneg_left hL1 hnonneg
          _ = C' := by simp [C']
      have hx_nonneg : 0 ≤ (1 + |x|) ^ hMG.m := pow_nonneg (by linarith [abs_nonneg x]) _
      exact mul_le_mul_of_nonneg_right hfac hx_nonneg)
  · intro x
    exact (growth_bound_comp_affine_real_deriv (hF_diff := hF_diff) (hMG := hMG) (z := z) (L := L) x).trans (by
      have hcoeff :
          hMG.C * (1 + ‖z‖ + ‖L‖) ^ hMG.m * (1 + ‖L‖) = C' := by aesop
      have : (hMG.C * (1 + ‖z‖ + ‖L‖) ^ hMG.m * (1 + ‖L‖)) * (1 + |x|) ^ hMG.m
            = C' * (1 + |x|) ^ hMG.m := by simp [hcoeff]
      exact le_of_eq this)

end AffineModerateGrowth

open AffineModerateGrowth

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
variable {ι : Type*} [Fintype ι]

variable (w : OrthonormalBasis ι ℝ H) (i : ι)

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] in
/-- Wrapper: moderate growth along the ONB coordinate line. -/
lemma moderateGrowth_along
  (F : H → ℝ)
  (hF_diff : ContDiff ℝ 1 F)
  (hMG : PhysLean.Probability.GaussianIBP.HasModerateGrowth F)
  (z : H) :
  ProbabilityTheory.HasModerateGrowth (fun x : ℝ => F (z + x • w i)) := by
  have h := AffineModerateGrowth.moderateGrowth_comp_affine_real
            (hF_diff := hF_diff) (hMG := hMG) (z := z) (L := lineCLM (w := w) (i := i))
  simpa [lineCLM] using h

end CoordLine
end SliceCalculus

section OneDStepWithParameter

open MeasureTheory ProbabilityTheory
open CoordLine

variable {vτ : ℝ≥0}

/-- 1D Gaussian IBP along a coordinate line, with an external parameter `y`. -/
lemma gaussian_IBP_along_line
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (w : OrthonormalBasis ι ℝ H) (i : ι)
  (F : H → ℝ) (hF_diff : ContDiff ℝ 1 F)
  (hF_growth : PhysLean.Probability.GaussianIBP.HasModerateGrowth F)
  (y : CoordLine.Comp ι i → ℝ) :
  ∫ (x : ℝ), x * (F (buildAlong (w := w) (i := i) y x)) ∂(ProbabilityTheory.gaussianReal 0 vτ)
    = (vτ : ℝ) * ∫ (x : ℝ), (deriv (fun t => F (buildAlong (w := w) (i := i) y t)) x)
        ∂(ProbabilityTheory.gaussianReal 0 vτ) := by
  classical
  let z : H := ∑ j : CoordLine.Comp ι i, (y j) • w j.1
  have hMG1D : ProbabilityTheory.HasModerateGrowth (fun x : ℝ => F (z + x • w i)) :=
    CoordLine.moderateGrowth_along (w := w) (i := i) F hF_diff hF_growth z
  have hF1D : ContDiff ℝ 1 (fun x : ℝ => F (z + x • w i)) := by
    exact hF_diff.comp ((contDiff_const.add (contDiff_id.smul contDiff_const)) : ContDiff ℝ 1 (fun x : ℝ => z + x • w i))
  by_cases hv : vτ = 0
  · subst hv
    simp [CoordLine.buildAlong, add_comm]
  · have hIBP :=
      ProbabilityTheory.gaussianReal_integration_by_parts
        (v := vτ) (hv := hv)
        (F := fun x : ℝ => F (z + x • w i))
        (hF := hF1D)
        (hMod := hMG1D)
    simpa [z, CoordLine.buildAlong, add_comm, add_left_comm, add_assoc] using hIBP

end OneDStepWithParameter

section SteinAlongOneCoordinate

open scoped BigOperators
open MeasureTheory ProbabilityTheory
open CoordLine

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [MeasurableSpace H] [BorelSpace H]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace ProductIBP

open MeasureTheory

variable {α β : Type*}
variable [MeasurableSpace α] [MeasurableSpace β]

/-- Fubini transport of a section-wise identity to the product. -/
lemma integral_prod_of_section_eq
  (μα : Measure α) (μβ : Measure β) (hα : SFinite μα) (hβ : SFinite μβ)
  {φ ψ : α × β → ℝ}
  (hφ_int : Integrable φ (μα.prod μβ))
  (hψ_int : Integrable ψ (μα.prod μβ))
  (hSec : ∀ a, ∫ b, φ (a, b) ∂μβ = ∫ b, ψ (a, b) ∂μβ) :
  ∫ p, φ p ∂(μα.prod μβ) = ∫ p, ψ p ∂(μα.prod μβ) := by
  classical
  haveI : SFinite μα := hα
  have hφ_prod :
      (∫ p, φ p ∂(μα.prod μβ))
        = (∫ a, ∫ b, φ (a, b) ∂μβ ∂μα) :=
    MeasureTheory.integral_prod (μ := μα) (ν := μβ) (f := φ) hφ_int
  have hψ_prod :
      (∫ p, ψ p ∂(μα.prod μβ))
        = (∫ a, ∫ b, ψ (a, b) ∂μβ ∂μα) :=
    MeasureTheory.integral_prod (μ := μα) (ν := μβ) (f := ψ) hψ_int
  have h_congr :
      (∫ a, ∫ b, φ (a, b) ∂μβ ∂μα)
        = (∫ a, ∫ b, ψ (a, b) ∂μβ ∂μα) :=
    MeasureTheory.integral_congr_ae (μ := μα)
      (Filter.Eventually.of_forall (fun a => by simpa using hSec a))
  simpa [hφ_prod, hψ_prod] using h_congr

end ProductIBP

namespace CoordLine

open Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Continuity of the affine ONB coordinate-line map (y,x) ↦ buildAlong w i y x. -/
lemma buildAlong_continuous
  (w : OrthonormalBasis ι ℝ H) (i : ι) :
  Continuous (fun p : (Comp ι i → ℝ) × ℝ => buildAlong (w := w) (i := i) p.1 p.2) := by
  classical
  have h_eval_sum :
      Continuous (fun y : Comp ι i → ℝ =>
        (∑ j : Comp ι i, (y j) • w j.1 : H)) := by
    refine
      continuous_finset_sum
        (s := (Finset.univ : Finset (Comp ι i)))
        (f := fun (j : Comp ι i) (y : Comp ι i → ℝ) => (y j) • w j.1)
        ?_
    intro j hj
    simpa using (continuous_apply j).smul continuous_const
  have h1 : Continuous (fun p : (Comp ι i → ℝ) × ℝ =>
      ∑ j : Comp ι i, (p.1 j) • w j.1) :=
    h_eval_sum.comp continuous_fst
  have h2 : Continuous (fun p : (Comp ι i → ℝ) × ℝ => p.2 • w i) :=
    continuous_snd.smul continuous_const
  simpa [buildAlong, add_comm, add_left_comm, add_assoc] using h1.add h2

section meas
variable [MeasurableSpace H] [BorelSpace H]

/-- Measurability of the affine ONB coordinate-line map. -/
lemma buildAlong_measurable
  (w : OrthonormalBasis ι ℝ H) (i : ι) :
  Measurable (fun p : (Comp ι i → ℝ) × ℝ => buildAlong (w := w) (i := i) p.1 p.2) :=
  (buildAlong_continuous (w := w) (i := i)).measurable

end meas

end CoordLine

/-- Pointwise-in-parameter 1D Stein identity along ONB coordinate `i`. -/
lemma stein_section_along_coord
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (w : OrthonormalBasis ι ℝ H) (i : ι)
  (F : H → ℝ) (hF_diff : ContDiff ℝ 1 F)
  (hF_growth : PhysLean.Probability.GaussianIBP.HasModerateGrowth F)
  (vτ : ℝ≥0)
  (y : CoordLine.Comp ι i → ℝ) :
  ∫ x, x * F (CoordLine.buildAlong (w := w) (i := i) y x) ∂(ProbabilityTheory.gaussianReal 0 vτ)
    = (vτ : ℝ) * ∫ x, deriv (fun t => F (CoordLine.buildAlong (w := w) (i := i) y t)) x
        ∂(ProbabilityTheory.gaussianReal 0 vτ) :=
  gaussian_IBP_along_line (w := w) (i := i) (F := F) (hF_diff := hF_diff) (hF_growth := hF_growth) (y := y)

open ProductIBP CoordLine

/-- Core product-level Stein step (pulls the scalar `(vτ : ℝ)` inside the integrand). -/
lemma stein_coord_on_product_core
  (w : OrthonormalBasis ι ℝ H) (i : ι)
  (F : H → ℝ) (hF_diff : ContDiff ℝ 1 F)
  (hF_growth : PhysLean.Probability.GaussianIBP.HasModerateGrowth F)
  (μY : Measure (CoordLine.Comp ι i → ℝ))
  (vτ : ℝ≥0)
  (hμY_sfinite : SFinite μY)
  (hInt_left :
     Integrable (fun p : (CoordLine.Comp ι i → ℝ) × ℝ =>
       p.2 * F (CoordLine.buildAlong (w := w) (i := i) p.1 p.2)) (μY.prod (ProbabilityTheory.gaussianReal 0 vτ)))
  (hInt_right :
     Integrable (fun p : (CoordLine.Comp ι i → ℝ) × ℝ =>
       (vτ : ℝ) * deriv (fun t => F (CoordLine.buildAlong (w := w) (i := i) p.1 t)) p.2)
     (μY.prod (ProbabilityTheory.gaussianReal 0 vτ))) :
  ∫ p, p.2 * F (CoordLine.buildAlong (w := w) (i := i) p.1 p.2) ∂(μY.prod (ProbabilityTheory.gaussianReal 0 vτ))
    =
  ∫ p, (vτ : ℝ) * deriv (fun t => F (CoordLine.buildAlong (w := w) (i := i) p.1 t)) p.2
    ∂(μY.prod (ProbabilityTheory.gaussianReal 0 vτ)) := by
  let γ : Measure ℝ := ProbabilityTheory.gaussianReal 0 vτ
  let φ : ((CoordLine.Comp ι i → ℝ) × ℝ) → ℝ :=
    fun p => p.2 * F (CoordLine.buildAlong (w := w) (i := i) p.1 p.2)
  let ψ : ((CoordLine.Comp ι i → ℝ) × ℝ) → ℝ :=
    fun p => (vτ : ℝ) * deriv (fun t => F (CoordLine.buildAlong (w := w) (i := i) p.1 t)) p.2
  have hSec : ∀ y, ∫ x, φ (y, x) ∂γ = ∫ x, ψ (y, x) ∂γ := by
    intro y
    simp [φ, ψ]; erw [stein_section_along_coord (w := w) (i := i) (F := F) (hF_diff := hF_diff)
      (hF_growth := hF_growth) (vτ := vτ) (y := y)]
    rw [← stein_section_along_coord w i F hF_diff hF_growth vτ y]; rw [stein_section_along_coord
        w i F hF_diff hF_growth vτ y]; simp; rw [integral_const_mul]
  exact ProductIBP.integral_prod_of_section_eq (μα := μY) (μβ := γ) (hα := hμY_sfinite)
    (hβ := (instSFiniteOfSigmaFinite)) (hφ_int := hInt_left) (hψ_int := hInt_right) (hSec := hSec)

/-- Backwards-compatible wrapper: original signature (keeps `(vτ : ℝ)` outside). -/
lemma stein_coord_on_product
  (w : OrthonormalBasis ι ℝ H) (i : ι)
  (F : H → ℝ) (hF_diff : ContDiff ℝ 1 F)
  (hF_growth : PhysLean.Probability.GaussianIBP.HasModerateGrowth F)
  (μY : Measure (CoordLine.Comp ι i → ℝ))
  (vτ : ℝ≥0)
  (hμY_sfinite : SFinite μY)
  (hInt_left :
     Integrable
       (fun p : (CoordLine.Comp ι i → ℝ) × ℝ =>
          p.2 * F (CoordLine.buildAlong (w := w) (i := i) p.1 p.2))
       (μY.prod (ProbabilityTheory.gaussianReal 0 vτ)))
  (hInt_right₀ :
     Integrable
       (fun p : (CoordLine.Comp ι i → ℝ) × ℝ =>
          deriv (fun t => F (CoordLine.buildAlong (w := w) (i := i) p.1 t)) p.2)
       (μY.prod (ProbabilityTheory.gaussianReal 0 vτ))) :
  ∫ p, p.2 * F (CoordLine.buildAlong (w := w) (i := i) p.1 p.2) ∂(μY.prod (ProbabilityTheory.gaussianReal 0 vτ))
    =
  (vτ : ℝ) * ∫ p, deriv (fun t => F (CoordLine.buildAlong (w := w) (i := i) p.1 t)) p.2
      ∂(μY.prod (ProbabilityTheory.gaussianReal 0 vτ)) := by
  have hInt_right := hInt_right₀.const_mul (vτ : ℝ)
  have hcore := stein_coord_on_product_core (w := w) (i := i) (F := F) (hF_diff := hF_diff)
    (hF_growth := hF_growth) (μY := μY) (vτ := vτ) (hμY_sfinite := hμY_sfinite)
    (hInt_left := hInt_left) (hInt_right := hInt_right)
  calc
      ∫ p, p.2 * F (CoordLine.buildAlong (w := w) (i := i) p.1 p.2)
        ∂(μY.prod (ProbabilityTheory.gaussianReal 0 vτ))
        =
      ∫ p, (vτ : ℝ) * deriv
          (fun t => F (CoordLine.buildAlong (w := w) (i := i) p.1 t)) p.2
        ∂(μY.prod (ProbabilityTheory.gaussianReal 0 vτ)) := hcore
    _ =
      (vτ : ℝ) *
      ∫ p, deriv (fun t => F (CoordLine.buildAlong (w := w) (i := i) p.1 t)) p.2
        ∂(μY.prod (ProbabilityTheory.gaussianReal 0 vτ)) := by
      simp [integral_const_mul]

namespace ProbabilityTheory

open MeasureTheory Set

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {α : ι → Type*} [∀ i, MeasurableSpace (α i)]

/-- If, for a measurable map `f : Ω → Π i, α i`, each coordinate has Dirac law at `c i`,
then the law of `f` is the Dirac mass at the whole point `c`.

Hypotheses:
- `μ` is a probability measure;
- the index type `ι` is countable (in particular, this includes finite index sets);
- each `α i` has measurable singletons;
- `f` is (globally) measurable;
- for each `i`, the pushforward of the coordinate `ω ↦ f ω i` is `dirac (c i)`.

Conclusion:
`map f μ = dirac c`. -/
lemma map_fun_dirac_of_coord_dirac
    [IsProbabilityMeasure μ] [Countable ι]
    [∀ i, MeasurableSingletonClass (α i)]
    {f : Ω → (∀ i, α i)} {c : ∀ i, α i}
    (hf : Measurable f)
    (hcoord : ∀ i, Measure.map (fun ω => f ω i) μ = Measure.dirac (c i)) :
    Measure.map f μ = Measure.dirac c := by
  classical
  have hAE_coord : ∀ i, ∀ᵐ ω ∂ μ, f ω i = c i := by
    intro i
    have hfi : Measurable (fun ω => f ω i) := (measurable_pi_apply i).comp hf
    have h1 : (Measure.map (fun ω => f ω i) μ) {c i} = 1 := by
      simpa using (by
        have := hcoord i
        simpa using congrArg (fun (m : Measure (α i)) => m {c i}) this)
    have : μ ((fun ω => f ω i) ⁻¹' {c i}) = 1 := by
      have hmap :
          (Measure.map (fun ω => f ω i) μ) {c i}
            = μ ((fun ω => f ω i) ⁻¹' {c i}) :=
        Measure.map_apply (μ := μ) (f := fun ω => f ω i) (s := {c i})
          hfi (measurableSet_singleton (c i))
      simpa [hmap] using h1
    have hcompl0 : μ (((fun ω => f ω i) ⁻¹' {c i})ᶜ) = 0 := by
      have : MeasurableSet ((fun ω => f ω i) ⁻¹' {c i}) :=
        hfi (measurableSet_singleton _)
      aesop
    exact (ae_iff.mpr hcompl0).mono (by intro ω hω; simpa using hω)
  have hAE_all : ∀ᵐ ω ∂ μ, ∀ i, f ω i = c i := by
    simpa using (ae_all_iff.mpr hAE_coord)
  have hAE_funext : f =ᵐ[μ] fun _ => c := by
    refine hAE_all.mono ?_
    intro ω hω; funext i; exact hω i
  ext s hs
  have hconst : Measurable fun (_ : Ω) => c := by
    simp
  have hf_map : (Measure.map f μ) s = μ (f ⁻¹' s) := Measure.map_apply hf hs
  have hconst_map : (Measure.map (fun (_ : Ω) => c) μ) s
      = μ ((fun _ => c) ⁻¹' s) := Measure.map_apply hconst hs
  have h_sets_ae :
      {ω | f ω ∈ s} =ᵐ[μ] {ω | (fun _ => c) ω ∈ s} :=
    hAE_funext.mono (by
      intro ω hω; aesop)
  have h_eq_measure : μ (f ⁻¹' s) = μ ((fun _ => c) ⁻¹' s) := by
    exact measure_congr h_sets_ae
  simpa [hf_map, hconst_map] using
    show (Measure.map f μ) s = (Measure.map (fun _ => c) μ) s from by
      aesop
  --done

end ProbabilityTheory

section Gauss1D_helpers

namespace ProbabilityTheory

/-- Under a centered real Gaussian law, `(1 + |x|)^n` is integrable for all `n`. -/
lemma integrable_one_add_abs_pow_nat_gaussian
    (v : ℝ≥0) (n : ℕ) :
    Integrable (fun x : ℝ => (1 + |x|) ^ n) (ProbabilityTheory.gaussianReal 0 v) := by
  -- Delegate to the (Fernique/MemLp based) integrability lemma in the 1D IBP file.
  simpa [pow_succ] using
    ProbabilityTheory.gaussianReal_integrable_one_add_abs_pow_centered (v := v) n

end ProbabilityTheory
end Gauss1D_helpers

section AlongLine_integrability

open ProbabilityTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (w : OrthonormalBasis ι ℝ H) (i : ι)

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [DecidableEq ι] in
/-- 1D along-line integrability (value): `x ↦ x · F(z + x • w i)` is `L¹(gauss)`. -/
lemma integrable_along_line_mul_gauss
    (F : H → ℝ) (hF_diff : ContDiff ℝ 1 F)
    (hF_growth : HasModerateGrowth F)
    (z : H) (v : ℝ≥0) :
    Integrable (fun x : ℝ => x * F (z + x • w i)) (ProbabilityTheory.gaussianReal 0 v) := by
  classical
  have hMG1D : ProbabilityTheory.HasModerateGrowth (fun x : ℝ => F (z + x • w i)) :=
    CoordLine.moderateGrowth_along (w := w) (i := i)
      (F := F) (hF_diff := hF_diff) (hMG := hF_growth) z
  have h_meas : AEStronglyMeasurable
      (fun x : ℝ => x * F (z + x • w i)) (ProbabilityTheory.gaussianReal 0 v) := by
    have hArg : Continuous (fun x : ℝ => z + (CoordLine.lineCLM (w := w) (i := i)) x) :=
      continuous_const.add (CoordLine.lineCLM (w := w) (i := i)).continuous
    have hcont : Continuous (fun x : ℝ => F (z + x • w i)) :=
      hF_diff.continuous.comp hArg
    exact (measurable_id.aestronglyMeasurable.mul hcont.measurable.aestronglyMeasurable)
  have h_dom :
      ∀ x, |x * F (z + x • w i)| ≤
        (hF_growth.C * (1 + ‖z‖ + ‖CoordLine.lineCLM (w := w) (i := i)‖) ^ hF_growth.m)
        * (|x| * (1 + |x|) ^ hF_growth.m) := by
    intro x
    have hv :=
      CoordLine.AffineModerateGrowth.growth_bound_comp_affine_real_value
        (hMG := hF_growth) (z := z) (L := CoordLine.lineCLM (w := w) (i := i)) x
    have hLnorm : ‖CoordLine.lineCLM (w := w) (i := i)‖ = ‖w i‖ := by
      simp [CoordLine.lineCLM]
    have hRew : 1 + ‖z‖ + ‖CoordLine.lineCLM (w := w) (i := i)‖
              = 1 + ‖z‖ + ‖w i‖ := by simp
    have hv' := hv.trans (by
      have hC : hF_growth.C * (1 + ‖z‖ + ‖CoordLine.lineCLM (w := w) (i := i)‖) ^ hF_growth.m
                ≤ hF_growth.C * (1 + ‖z‖ + ‖w i‖) ^ hF_growth.m := by
        simp
      have hx : 0 ≤ (1 + |x|) ^ hF_growth.m := by
        exact pow_nonneg (by linarith [abs_nonneg x]) _
      exact mul_le_mul_of_nonneg_right hC hx)
    have hv'' :
        |x * F (z + x • w i)|
          ≤ |x| * (hF_growth.C * (1 + ‖z‖ + ‖w i‖) ^ hF_growth.m) * (1 + |x|) ^ hF_growth.m := by
      have := mul_le_mul_of_nonneg_left hv' (by exact abs_nonneg x)
      simpa [mul_comm, mul_left_comm, mul_assoc, abs_mul] using this
    have hnormwi : ‖w i‖ = (1 : ℝ) := by simp
    have hConstRew :
        |x| * (hF_growth.C * (1 + ‖z‖ + ‖w i‖) ^ hF_growth.m)
              * (1 + |x|) ^ hF_growth.m
          = (hF_growth.C * (1 + ‖z‖ + 1) ^ hF_growth.m) * (|x| * (1 + |x|) ^ hF_growth.m) := by
      have hstep :
          hF_growth.C * (1 + ‖z‖ + ‖w i‖) ^ hF_growth.m
            = hF_growth.C * (1 + ‖z‖ + 1) ^ hF_growth.m := by
        simp [hnormwi]
      simp [mul_comm, mul_left_comm, mul_assoc]
    have hv''' :
        |x * F (z + x • w i)|
          ≤ (hF_growth.C * (1 + ‖z‖ + 1) ^ hF_growth.m) * (|x| * (1 + |x|) ^ hF_growth.m) := by
      aesop
    aesop
  have h_int_mplus1 :
      Integrable (fun x : ℝ => (1 + |x|) ^ (hF_growth.m + 1))
        (ProbabilityTheory.gaussianReal 0 v) :=
    (ProbabilityTheory.integrable_one_add_abs_pow_nat_gaussian (v := v) (n := hF_growth.m + 1))
  have h_meas_rhs :
      AEStronglyMeasurable (fun x : ℝ => |x| * (1 + |x|) ^ hF_growth.m)
        (ProbabilityTheory.gaussianReal 0 v) := by
    have hcont : Continuous (fun x : ℝ => |x| * (1 + |x|) ^ hF_growth.m) :=
      continuous_abs.mul ((continuous_const.add continuous_abs).pow _)
    simpa using hcont.measurable.aestronglyMeasurable
  have h_base_int :
      Integrable (fun x : ℝ => |x| * (1 + |x|) ^ hF_growth.m)
        (ProbabilityTheory.gaussianReal 0 v) := by
    refine h_int_mplus1.mono' h_meas_rhs (ae_of_all _ (fun x => ?_))
    have hx_pow_nonneg : 0 ≤ (1 + |x|) ^ hF_growth.m :=
      pow_nonneg (by linarith [abs_nonneg x]) _
    have hnonneg : 0 ≤ |x| * (1 + |x|) ^ hF_growth.m :=
      mul_nonneg (abs_nonneg _) hx_pow_nonneg
    have hx_le : |x| ≤ 1 + |x| := by linarith [abs_nonneg x]
    have hstep :
        |x| * (1 + |x|) ^ hF_growth.m
          ≤ (1 + |x|) * (1 + |x|) ^ hF_growth.m :=
      mul_le_mul_of_nonneg_right hx_le hx_pow_nonneg
    have habs : |(1 + |x|)| = 1 + |x| := by
      have : 0 ≤ 1 + |x| := by linarith [abs_nonneg x]
      simp [abs_of_nonneg this]
    have hx_pow_nonneg' : 0 ≤ |(1 + |x|)| ^ hF_growth.m :=
      pow_nonneg (abs_nonneg (1 + |x|)) _
    have hstep' :
        |x| * |(1 + |x|)| ^ hF_growth.m
          ≤ |(1 + |x|)| ^ (hF_growth.m + 1) := by
      have hx_le' : |x| ≤ |(1 + |x|)| := by simp [habs]
      have := mul_le_mul_of_nonneg_right hx_le' hx_pow_nonneg'
      simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using this
    have : ‖|x| * (1 + |x|) ^ hF_growth.m‖
            ≤ (1 + |x|) ^ (hF_growth.m + 1) := by
      have hnonneg' : 0 ≤ |x| * |(1 + |x|)| ^ hF_growth.m :=
        mul_nonneg (abs_nonneg _) hx_pow_nonneg'
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg', habs] using hstep'
    exact this
  have h_rhs_int :
      Integrable
        (fun x : ℝ =>
          (hF_growth.C * (1 + ‖z‖ + 1) ^ hF_growth.m) * (|x| * (1 + |x|) ^ hF_growth.m))
        (ProbabilityTheory.gaussianReal 0 v) :=
    h_base_int.const_mul _
  exact h_rhs_int.mono' h_meas (ae_of_all _ (fun x => by
    have hR : 0 ≤
        (hF_growth.C * (1 + ‖z‖ + 1) ^ hF_growth.m) * (|x| * (1 + |x|) ^ hF_growth.m) := by
      have hx : 0 ≤ (|x| * (1 + |x|) ^ hF_growth.m) :=
        mul_nonneg (abs_nonneg _) (pow_nonneg (by linarith [abs_nonneg x]) _)
      have hK : 0 ≤ (hF_growth.C * (1 + ‖z‖ + 1) ^ hF_growth.m) :=
        mul_nonneg (le_of_lt hF_growth.Cpos)
          (pow_nonneg (by nlinarith [norm_nonneg z]) _)
      exact mul_nonneg hK hx
    simpa [Real.norm_eq_abs, abs_mul] using h_dom x))

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [DecidableEq ι] in
/-- 1D along-line integrability (derivative). -/
lemma integrable_along_line_deriv_gauss
    (F : H → ℝ) (hF_diff : ContDiff ℝ 1 F)
    (hF_growth : HasModerateGrowth F)
    (z : H) (v : ℝ≥0) :
    Integrable (fun x : ℝ =>
      deriv (fun t => F (z + t • w i)) x) (ProbabilityTheory.gaussianReal 0 v) := by
  classical
  have hF1D : ContDiff ℝ 1 (fun x : ℝ => F (z + (CoordLine.lineCLM (w := w) (i := i)) x)) :=
    hF_diff.comp (contDiff_const.add (CoordLine.lineCLM (w := w) (i := i)).contDiff)
  have h_meas :
      AEStronglyMeasurable
        (fun x : ℝ => deriv (fun t => F (z + t • w i)) x)
        (ProbabilityTheory.gaussianReal 0 v) := by
    measurability
  have h_dom :
      ∀ x, |deriv (fun t => F (z + t • w i)) x|
        ≤ (hF_growth.C * (1 + ‖z‖ + ‖CoordLine.lineCLM (w := w) (i := i)‖) ^ hF_growth.m
              * (1 + ‖CoordLine.lineCLM (w := w) (i := i)‖))
          * ((1 + |x|) ^ hF_growth.m) := by
    intro x
    have hbound :=
      CoordLine.AffineModerateGrowth.growth_bound_comp_affine_real_deriv
        (hF_diff := hF_diff) (hMG := hF_growth) (z := z) (L := CoordLine.lineCLM (w := w) (i := i)) x
    have hLnorm : ‖CoordLine.lineCLM (w := w) (i := i)‖ = ‖w i‖ := by
      simp [CoordLine.lineCLM]
    have hw1 : ‖w i‖ = (1 : ℝ) := by simp
    simpa [hLnorm, hw1, mul_comm, mul_left_comm, mul_assoc] using hbound
  have h_base : Integrable (fun x : ℝ => (1 + |x|) ^ hF_growth.m)
        (ProbabilityTheory.gaussianReal 0 v) :=
    ProbabilityTheory.integrable_one_add_abs_pow_nat_gaussian (v := v) (n := hF_growth.m)
  have h_rhs_int :
      Integrable
        (fun x : ℝ =>
          (hF_growth.C * (1 + ‖z‖ + ‖CoordLine.lineCLM (w := w) (i := i)‖) ^ hF_growth.m
              * (1 + ‖CoordLine.lineCLM (w := w) (i := i)‖))
            * ((1 + |x|) ^ hF_growth.m))
        (ProbabilityTheory.gaussianReal 0 v) :=
    h_base.const_mul _
  exact h_rhs_int.mono' h_meas (ae_of_all _ (fun x => by
    simpa [Real.norm_eq_abs] using h_dom x))

end AlongLine_integrability

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α]
variable {E : Type*} [NormedAddCommGroup E]
variable {μ : Measure α}

/-- If `f =ᵐ[μ] g`, then `Integrable f μ ↔ Integrable g μ`. -/
lemma integrable_congr_ae {f g : α → E} (hfg : f =ᵐ[μ] g) :
    Integrable f μ ↔ Integrable g μ := by
  classical
  constructor
  · intro hf
    refine ⟨hf.aestronglyMeasurable.congr hfg, ?_⟩
    have hnn : (fun x => (‖g x‖₊ : ℝ≥0∞)) =ᵐ[μ]
                (fun x => (‖f x‖₊ : ℝ≥0∞)) := by
      refine hfg.mono ?_
      intro x hx; simp [hx]
    have hlin : ∫⁻ x, ‖g x‖₊ ∂μ = ∫⁻ x, ‖f x‖₊ ∂μ := by
      simpa using lintegral_congr_ae hnn
    rw [propext (hasFiniteIntegral_congr (id (EventuallyEq.symm hfg)))]
    exact hf.hasFiniteIntegral
  · intro hg
    refine ⟨hg.aestronglyMeasurable.congr hfg.symm, ?_⟩
    have hnn : (fun x => (‖f x‖₊ : ℝ≥0∞)) =ᵐ[μ]
                (fun x => (‖g x‖₊ : ℝ≥0∞)) := by
      refine hfg.mono ?_
      intro x hx; simp [hx]
    have hlin : ∫⁻ x, ‖f x‖₊ ∂μ = ∫⁻ x, ‖g x‖₊ ∂μ := by
      simpa using lintegral_congr_ae hnn
    rw [propext (hasFiniteIntegral_congr hfg)]
    simpa [hlin] using hg.hasFiniteIntegral

end MeasureTheory

section Pullback_to_Omega

open ProbabilityTheory MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (w : OrthonormalBasis ι ℝ H) (i : ι)

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] in
/-- If `X` has centered Gaussian law and `Y =ᵐ const y₀`, then
`ω ↦ X ω · F(buildAlong w i (Y ω) (X ω))` is integrable. -/
lemma integrable_coord_mul_F_of_gauss_and_aeConstY
    {Ω : Type*} [MeasureSpace Ω] (μ : Measure Ω)
    (F : H → ℝ) (hF_diff : ContDiff ℝ 1 F)
    (hF_growth : HasModerateGrowth F)
    (vτ : ℝ≥0)
    (X : Ω → ℝ) (hX_meas : Measurable X)
    (hX_gauss : Measure.map X μ = ProbabilityTheory.gaussianReal 0 vτ)
    (Y : Ω → (CoordLine.Comp ι i → ℝ)) {y0 : (CoordLine.Comp ι i → ℝ)}
    (hY_ae : Y =ᵐ[μ] fun _ => y0) :
    Integrable (fun ω => X ω * F ( CoordLine.buildAlong (w := w) (i := i) (Y ω) (X ω) )) μ := by
  classical
  have hae :
      (fun ω => X ω * F (CoordLine.buildAlong (w := w) (i := i) (Y ω) (X ω)))
        =ᵐ[μ]
      (fun ω => X ω * F (CoordLine.buildAlong (w := w) (i := i) y0 (X ω))) := by
    refine hY_ae.mono ?_
    intro ω hω
    simp [hω]
  let z0 : H := ∑ j : CoordLine.Comp ι i, (y0 j) • w j.1
  have hint_gauss :
      Integrable (fun x : ℝ => x * F (z0 + x • w i))
        (ProbabilityTheory.gaussianReal 0 vτ) :=
    integrable_along_line_mul_gauss (w := w) (i := i) (F := F)
      (hF_diff := hF_diff) (hF_growth := hF_growth) (z := z0) (v := vτ)
  have : Integrable
      (fun ω => X ω * F (CoordLine.buildAlong (w := w) (i := i) y0 (X ω))) μ := by
    have hmap_int :
        Integrable (fun x : ℝ => x * F (z0 + x • w i)) (Measure.map X μ) := by
      simpa [hX_gauss] using hint_gauss
    simpa [CoordLine.buildAlong, z0, add_comm, add_left_comm, add_assoc] using
      hmap_int.comp_measurable hX_meas
  exact (integrable_congr_ae hae).2 this

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] in
/-- If `X` has centered Gaussian law and `Y =ᵐ const y₀`, then
`ω ↦ deriv (t ↦ F(buildAlong w i (Y ω) t)) (X ω)` is integrable. -/
lemma integrable_deriv_F_along_coord_of_gauss_and_aeConstY
    {Ω : Type*} [MeasureSpace Ω] (μ : Measure Ω)
    (F : H → ℝ) (hF_diff : ContDiff ℝ 1 F)
    (hF_growth : HasModerateGrowth F)
    (vτ : ℝ≥0)
    (X : Ω → ℝ) (hX_meas : Measurable X)
    (hX_gauss : Measure.map X μ = ProbabilityTheory.gaussianReal 0 vτ)
    (Y : Ω → (CoordLine.Comp ι i → ℝ)) {y0 : (CoordLine.Comp ι i → ℝ)}
    (hY_ae : Y =ᵐ[μ] fun _ => y0) :
    Integrable (fun ω =>
      deriv (fun t => F (CoordLine.buildAlong (w := w) (i := i) (Y ω) t)) (X ω)) μ := by
  classical
  have hae : (fun ω =>
      deriv (fun t => F (CoordLine.buildAlong (w := w) (i := i) (Y ω) t)) (X ω))
      =ᵐ[μ]
      (fun ω =>
      deriv (fun t => F (CoordLine.buildAlong (w := w) (i := i) y0 t)) (X ω)) := by
    refine hY_ae.mono ?_
    intro ω hω
    simp [hω]
  let z0 : H := ∑ j : CoordLine.Comp ι i, (y0 j) • w j.1
  have hint_gauss :
      Integrable (fun x : ℝ =>
        deriv (fun t => F (z0 + t • w i)) x) (ProbabilityTheory.gaussianReal 0 vτ) :=
    integrable_along_line_deriv_gauss (w := w) (i := i) (F := F)
      (hF_diff := hF_diff) (hF_growth := hF_growth) (z := z0) (v := vτ)
  have : Integrable (fun ω =>
      deriv (fun t => F (CoordLine.buildAlong (w := w) (i := i) y0 t)) (X ω)) μ := by
    have hmap_int :
        Integrable (fun x : ℝ =>
          deriv (fun t => F (z0 + t • w i)) x) (Measure.map X μ) := by
      simpa [hX_gauss] using hint_gauss
    simpa [CoordLine.buildAlong, z0, add_comm, add_left_comm, add_assoc] using
      hmap_int.comp_measurable hX_meas
  exact (integrable_congr_ae hae).2 this

end Pullback_to_Omega

section AEconst_helper

open ProbabilityTheory

/-- If each coordinate of `Y` (to `Comp ι i → ℝ`) has pushforward law `gaussianReal 0 0`
with respect to `μ` (i.e. Dirac at `0`), then `Y =ᵐ[μ] const 0`. -/
lemma ae_const_zero_of_coord_gauss0
    {Ω : Type*} [MeasureSpace Ω] (μ : Measure Ω)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι)
    (Y : Ω → (CoordLine.Comp ι i → ℝ)) (hY_meas : Measurable Y)
    (hY_gauss0 : ∀ j, Measure.map (fun ω => Y ω j) μ = ProbabilityTheory.gaussianReal 0 0) :
    Y =ᵐ[μ] (fun _ => (fun _ => (0 : ℝ))) := by
  classical
  have hAEcoord : ∀ j, ∀ᵐ ω ∂ μ, Y ω j = 0 := by
    intro j
    have hmap : Measure.map (fun ω => Y ω j) μ
                = ProbabilityTheory.gaussianReal 0 0 := hY_gauss0 j
    have hmeasj : Measurable (fun ω => Y ω j) :=
      (measurable_pi_apply j).comp hY_meas
    have hdirac : ProbabilityTheory.gaussianReal 0 0 = Measure.dirac (0 : ℝ) := by
      simp
    have hcompl0 :
        μ (((fun ω => Y ω j) ⁻¹' {0})ᶜ) = 0 := by
      have hs : MeasurableSet (({0} : Set ℝ)ᶜ) :=
        (measurableSet_singleton (0 : ℝ)).compl
      have hmap_apply :
          (Measure.map (fun ω => Y ω j) μ) (({0} : Set ℝ)ᶜ)
            = μ (((fun ω => Y ω j) ⁻¹' (({0} : Set ℝ)ᶜ))) := by
        simpa using
          (Measure.map_apply (μ := μ) (f := fun ω => Y ω j) (s := (({0} : Set ℝ)ᶜ))
            hmeasj hs)
      have hpush0 :
          (Measure.map (fun ω => Y ω j) μ) (({0} : Set ℝ)ᶜ) = 0 := by
        classical
        simp [hmap, hdirac]
      have : μ (((fun ω => Y ω j) ⁻¹' (({0} : Set ℝ)ᶜ))) = 0 := by
        simpa [hmap_apply] using hpush0
      simpa using this
    exact (ae_iff.mpr hcompl0).mono (by intro ω hω; simpa using hω)
  have : ∀ᵐ ω ∂ μ, ∀ j, Y ω j = 0 := by
    refine ae_all_iff.2 (by intro j; exact hAEcoord j)
  exact this.mono (by intro ω hω; funext j; exact hω j)

end AEconst_helper

section Wrappers_old_names

open ProbabilityTheory

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- Wrapper (old name): integrability of `X · F(buildAlong (Y,X))` under independence,
using the a.e.-const helper for zero-variance coordinates. -/
lemma integrable_coord_mul_F_of_indep
    (w : OrthonormalBasis ι ℝ H) (i : ι)
    (F : H → ℝ) (hF_diff : ContDiff ℝ 1 F)
    (hF_growth : HasModerateGrowth F)
    (vτ : ℝ≥0)
    (X : Ω → ℝ) (Y : Ω → (CoordLine.Comp ι i → ℝ))
    (hX_meas : Measurable X) (hY_meas : Measurable Y)
    (_hIndep : ProbabilityTheory.IndepFun Y X ℙ)
    (hX_gauss : ProbabilityTheory.IsCenteredGaussianRV X vτ)
    (hY_gauss0 : ∀ j, ProbabilityTheory.IsCenteredGaussianRV (fun ω => Y ω j) 0) :
    Integrable (fun ω => X ω * F (CoordLine.buildAlong (w := w) (i := i) (Y ω) (X ω))) ℙ := by
  classical
  have hYpush :
      ∀ j, Measure.map (fun ω => Y ω j) (ℙ : Measure Ω)
            = ProbabilityTheory.gaussianReal 0 0 := by
    intro j
    simpa [ProbabilityTheory.IsCenteredGaussianRV, ProbabilityTheory.IsGaussianRV] using hY_gauss0 j
  have hYae : Y =ᵐ[ℙ] fun _ => (fun _ => (0 : ℝ)) :=
    ae_const_zero_of_coord_gauss0 (μ := (ℙ : Measure Ω))
      (i := i) (Y := Y) (hY_meas := hY_meas) (hY_gauss0 := hYpush)
  have hXlaw : Measure.map X ℙ = ProbabilityTheory.gaussianReal 0 vτ := by
    simpa [ProbabilityTheory.IsCenteredGaussianRV, ProbabilityTheory.IsGaussianRV] using hX_gauss
  simpa using
    integrable_coord_mul_F_of_gauss_and_aeConstY
      (w := w) (i := i) (μ := (ℙ : Measure Ω))
      (F := F) (hF_diff := hF_diff) (hF_growth := hF_growth)
      (vτ := vτ) (X := X) (hX_meas := hX_meas) (hX_gauss := hXlaw)
      (Y := Y) (y0 := fun _ => 0) (hY_ae := hYae)

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- Wrapper (old name): integrability of the derivative along the coordinate line under independence. -/
lemma integrable_deriv_F_along_coord_of_indep
    (w : OrthonormalBasis ι ℝ H) (i : ι)
    (F : H → ℝ) (hF_diff : ContDiff ℝ 1 F)
    (hF_growth : HasModerateGrowth F)
    (vτ : ℝ≥0)
    (X : Ω → ℝ) (Y : Ω → (CoordLine.Comp ι i → ℝ))
    (hX_meas : Measurable X) (hY_meas : Measurable Y)
    (_hIndep : ProbabilityTheory.IndepFun Y X ℙ)
    (hX_gauss : ProbabilityTheory.IsCenteredGaussianRV X vτ)
    (hY_gauss0 : ∀ j, ProbabilityTheory.IsCenteredGaussianRV (fun ω => Y ω j) 0) :
    Integrable (fun ω =>
      deriv (fun t => F (CoordLine.buildAlong (w := w) (i := i) (Y ω) t)) (X ω)) ℙ := by
  classical
  -- Y is a.e. zero
  have hYpush :
      ∀ j, Measure.map (fun ω => Y ω j) (ℙ : Measure Ω)
            = ProbabilityTheory.gaussianReal 0 0 := by
    intro j
    simpa [ProbabilityTheory.IsCenteredGaussianRV, ProbabilityTheory.IsGaussianRV] using hY_gauss0 j
  have hYae : Y =ᵐ[ℙ] fun _ => (fun _ => (0 : ℝ)) :=
    ae_const_zero_of_coord_gauss0 (μ := (ℙ : Measure Ω))
      (i := i) (Y := Y) (hY_meas := hY_meas) (hY_gauss0 := hYpush)
  have hXlaw : Measure.map X ℙ = ProbabilityTheory.gaussianReal 0 vτ := by
    simpa [ProbabilityTheory.IsCenteredGaussianRV, ProbabilityTheory.IsGaussianRV] using hX_gauss
  simpa using
    integrable_deriv_F_along_coord_of_gauss_and_aeConstY
      (w := w) (i := i) (μ := (ℙ : Measure Ω))
      (F := F) (hF_diff := hF_diff) (hF_growth := hF_growth)
      (vτ := vτ) (X := X) (hX_meas := hX_meas) (hX_gauss := hXlaw)
      (Y := Y) (y0 := fun _ => 0) (hY_ae := hYae)

end Wrappers_old_names
open ProbabilityTheory MeasureTheory

/-- If a real-valued map `X` is a.e. equal to the constant `0` under a probability measure `μ`,
then its pushforward law is the Dirac mass at `0`. Requires measurability of `X`. -/
lemma map_eq_dirac_of_ae_eq_const_zero
    {Ω : Type*} [MeasureSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX_meas : Measurable X)
    (hConst : X =ᵐ[μ] fun _ => (0 : ℝ)) :
    Measure.map X μ = Measure.dirac (0 : ℝ) := by
  classical
  ext s hs
  have hmapX : (Measure.map X μ) s = μ (X ⁻¹' s) :=
    Measure.map_apply hX_meas hs
  have hmap0 : (Measure.map (fun (_ : Ω) => (0 : ℝ)) μ) s
      = μ ((fun _ => (0 : ℝ)) ⁻¹' s) :=
    Measure.map_apply (measurable_const : Measurable fun (_ : Ω) => (0 : ℝ)) hs
  have hpreimage_ae :
      (X ⁻¹' s) =ᵐ[μ] ((fun _ : Ω => (0 : ℝ)) ⁻¹' s) := by
    refine hConst.mono ?_
    intro ω hω
    have hiff : (ω ∈ X ⁻¹' s) ↔ (ω ∈ ((fun _ : Ω => (0 : ℝ)) ⁻¹' s)) := by
      simp [Set.mem_preimage, hω]
    simpa using (propext hiff)
  have hEq : μ (X ⁻¹' s) = μ ((fun _ : Ω => (0 : ℝ)) ⁻¹' s) :=
    measure_congr hpreimage_ae
  have hEq : μ (X ⁻¹' s) = μ ((fun _ : Ω => (0 : ℝ)) ⁻¹' s) :=
    measure_congr hpreimage_ae
  have hConstPush :
      (Measure.map (fun _ : Ω => (0 : ℝ)) μ) s = (Measure.dirac (0 : ℝ)) s := by
    by_cases h0 : (0 : ℝ) ∈ s
    · have : ((fun _ : Ω => (0 : ℝ)) ⁻¹' s) = Set.univ := by
        ext ω; simp [h0]
      simp [h0]
    · have : ((fun _ : Ω => (0 : ℝ)) ⁻¹' s) = (∅ : Set Ω) := by
        ext ω; simp [h0]
      simp [h0]
  have hChain : μ (X ⁻¹' s) = (Measure.dirac (0 : ℝ)) s :=
    (hEq.trans hmap0.symm).trans hConstPush
  simpa [hmapX] using hChain

/-- If a real-valued map `X` is a.e. equal to the constant `0` under a probability measure `μ`,
then its pushforward law is the centered degenerate Gaussian `gaussianReal 0 0`. -/
lemma map_eq_gaussianReal0_of_ae_eq_const_zero
    {Ω : Type*} [MeasureSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX_meas : Measurable X)
    (hConst : X =ᵐ[μ] fun _ => (0 : ℝ)) :
    Measure.map X μ = ProbabilityTheory.gaussianReal 0 0 := by
  classical
  simpa [ProbabilityTheory.gaussianReal_dirac] using
    map_eq_dirac_of_ae_eq_const_zero (μ := μ) (hX_meas := hX_meas) (hConst := hConst)

namespace ProbabilityTheory

/-- Wrapper with the ambient probability measure `ℙ`:
if `X =ᵐ[ℙ] 0` and `X` is measurable, then `X` is a centered Gaussian with
variance `0`. -/
lemma IsCenteredGaussianRV.of_ae_eq_const
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : Ω → ℝ} (hX_meas : Measurable X)
    (hConst : X =ᵐ[ℙ] fun _ => (0 : ℝ)) :
    ProbabilityTheory.IsCenteredGaussianRV X 0 := by
  classical
  have hmap : Measure.map X (ℙ : Measure Ω) =
      ProbabilityTheory.gaussianReal 0 0 := by
    simpa [ProbabilityTheory.gaussianReal_dirac] using
      map_eq_dirac_of_ae_eq_const_zero (μ := (ℙ : Measure Ω))
        (hX_meas := hX_meas) (hConst := hConst)
  dsimp [ProbabilityTheory.IsCenteredGaussianRV,
         ProbabilityTheory.IsGaussianRV] at *
  exact hmap

/-- If a family `f` is mutually independent, then the tuple on the complement
of `i` is independent from the coordinate `i` itself. -/
lemma iIndepFun.indepFun_subtype_prod_singleton
  {Ω ι : Type*} {β : ι → Type*}
  [MeasurableSpace Ω] {μ : Measure Ω}
  [Fintype ι] [DecidableEq ι]
  [∀ i, MeasurableSpace (β i)]
  {f : ∀ i, Ω → β i}
  (hind : ProbabilityTheory.iIndepFun f μ)
  (hf : ∀ i, Measurable (f i))
  (i : ι) :
  ProbabilityTheory.IndepFun
    (fun ω => fun j : {j // j ≠ i} => f j.1 ω)
    (fun ω => f i ω) μ := by
  classical
  let S : Finset ι := Finset.univ.erase i
  let T : Finset ι := {i}
  have hST : Disjoint S T := by
    refine Finset.disjoint_left.2 ?_
    intro x hxS hxT
    exact (Finset.mem_erase.mp hxS).1 (Finset.mem_singleton.mp hxT)
  have h0 :
      ProbabilityTheory.IndepFun
        (fun ω (j : {x // x ∈ S}) => f j.1 ω)
        (fun ω (k : {x // x ∈ T}) => f k.1 ω) μ :=
    (ProbabilityTheory.iIndepFun.indepFun_finset
      (f := f) (μ := μ) (S := S) (T := T) hST hind hf)
  let e : {j // j ≠ i} ≃ {j // j ∈ S} :=
  { toFun := fun j =>
      ⟨j.1, by
        have : j.1 ≠ i ∧ j.1 ∈ Finset.univ := ⟨j.2, by simp⟩
        simpa [S, Finset.mem_erase] using this⟩
    , invFun := fun j => ⟨j.1, (Finset.mem_erase.mp j.2).1⟩
    , left_inv := by intro j; rfl
    , right_inv := by intro j; rfl }
  let φ :
      (∀ j : {j // j ∈ S}, β j.1) → (∀ j : {j // j ≠ i}, β j.1) :=
    fun v j => v (e j)
  have hφ_meas : Measurable φ := by
    refine measurable_pi_iff.mpr (fun j => ?_)
    simpa using (measurable_pi_apply (e j))
  let ψ : (∀ _k : {x // x ∈ T}, β _k.1) → β i :=
    fun v => v ⟨i, by simp [T]⟩
  have hψ_meas : Measurable ψ := by measurability
  have h' := (ProbabilityTheory.IndepFun.comp h0 hφ_meas hψ_meas)
  have h_left :
      (φ ∘ fun ω (j : {j // j ∈ S}) => f j.1 ω)
        =
      (fun ω (j : {j // j ≠ i}) => f j.1 ω) := by
    funext ω j; rfl
  have h_right :
      (ψ ∘ fun ω (k : {x // x ∈ T}) => f k.1 ω)
        = (fun ω => f i ω) := by
    funext ω; rfl
  simpa [h_left, h_right] using h'

omit [IsProbabilityMeasure (ℙ : Measure Ω)] [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] in
/-- Independence of i-th coordinate and complement under the Gaussian model. -/
lemma indep_coord_complement
  {g : Ω → H} (hg : PhysLean.Probability.GaussianIBP.IsGaussianHilbert g)
  (i : hg.ι) :
  ProbabilityTheory.IndepFun
    (fun ω => fun j : CoordLine.Comp hg.ι i => coord hg.w g j.1 ω)
    (coord hg.w g i) ℙ := by
  classical
  have hind :
      ProbabilityTheory.iIndepFun (coord hg.w g) ℙ :=
    (PhysLean.Probability.GaussianIBP.coord_isGaussian_and_indep (g := g) hg).2
  have hf : ∀ j, Measurable (coord hg.w g j) :=
    PhysLean.Probability.GaussianIBP.coord_measurable (g := g) hg
  simpa [CoordLine.Comp] using
    (ProbabilityTheory.iIndepFun.indepFun_subtype_prod_singleton
      (μ := ℙ) (f := coord hg.w g) hind hf i)

lemma stein_coord_with_param_of_indep
  (w : OrthonormalBasis ι ℝ H) (i : ι)
  (F : H → ℝ) (hF_diff : ContDiff ℝ 1 F)
  (hF_growth : PhysLean.Probability.GaussianIBP.HasModerateGrowth F)
  (vτ : ℝ≥0)
  (X : Ω → ℝ) (Y : Ω → (CoordLine.Comp ι i → ℝ))
  (hX_meas : Measurable X) (hY_meas : Measurable Y)
  (hIndep : ProbabilityTheory.IndepFun Y X ℙ)
  (hX_gauss : ProbabilityTheory.IsCenteredGaussianRV X vτ)
  (hY_gauss0 : ∀ j, ProbabilityTheory.IsCenteredGaussianRV (fun ω => Y ω j) 0) :
  ∫ ω, X ω * F (CoordLine.buildAlong (w := w) (i := i) (Y ω) (X ω)) ∂ℙ
    =
  (vτ : ℝ) *
  ∫ ω, deriv (fun t => F (CoordLine.buildAlong (w := w) (i := i) (Y ω) t)) (X ω) ∂ℙ := by
  classical
  set P := (CoordLine.Comp ι i → ℝ) × ℝ
  set φ : P → ℝ :=
    fun p => p.2 * F (CoordLine.buildAlong (w := w) (i := i) p.1 p.2)
  set ψ : P → ℝ :=
    fun p => deriv (fun t => F (CoordLine.buildAlong (w := w) (i := i) p.1 t)) p.2
  have hφ_meas : Measurable φ := by
    have h_eval_sum :
        Continuous (fun y : CoordLine.Comp ι i → ℝ =>
          ∑ j : CoordLine.Comp ι i, (y j) • w j.1) := by
      refine
        continuous_finset_sum
          (s := (Finset.univ : Finset (CoordLine.Comp ι i)))
          (f := fun (j : CoordLine.Comp ι i) (y : CoordLine.Comp ι i → ℝ) => (y j) • w j.1)
          ?_
      intro j _
      simpa using (continuous_apply j).smul continuous_const
    have h1 : Continuous (fun p : P => ∑ j : CoordLine.Comp ι i, (p.1 j) • w j.1) :=
      h_eval_sum.comp continuous_fst
    have h2 : Continuous (fun p : P => p.2 • w i) := continuous_snd.smul continuous_const
    have h_build_cont : Continuous (fun p : P =>
        CoordLine.buildAlong (w := w) (i := i) p.1 p.2) := by
      simpa [CoordLine.buildAlong, add_comm, add_left_comm, add_assoc] using h1.add h2
    have hFcont : Continuous (fun p : P =>
        F (CoordLine.buildAlong (w := w) (i := i) p.1 p.2)) :=
      hF_diff.continuous.comp h_build_cont
    have hSnd : Continuous (fun p : P => p.2) := continuous_snd
    exact (hSnd.measurable.mul hFcont.measurable)
  have hψ_meas : Measurable ψ := by
    have h_eval_sum :
        Continuous (fun y : CoordLine.Comp ι i → ℝ =>
          ∑ j : CoordLine.Comp ι i, (y j) • w j.1) := by
      refine
        continuous_finset_sum
          (s := (Finset.univ : Finset (CoordLine.Comp ι i)))
          (f := fun (j : CoordLine.Comp ι i) (y : CoordLine.Comp ι i → ℝ) => (y j) • w j.1)
          ?_
      intro j _
      simpa using (continuous_apply j).smul continuous_const
    have h1 : Continuous (fun p : P => ∑ j : CoordLine.Comp ι i, (p.1 j) • w j.1) :=
      h_eval_sum.comp continuous_fst
    have h2 : Continuous (fun p : P => p.2 • w i) := continuous_snd.smul continuous_const
    have h_build_meas : Measurable (fun p : P =>
        CoordLine.buildAlong (w := w) (i := i) p.1 p.2) := by
      have h_build_cont : Continuous (fun p : P =>
          CoordLine.buildAlong (w := w) (i := i) p.1 p.2) := by
        simpa [CoordLine.buildAlong, add_comm, add_left_comm, add_assoc] using h1.add h2
      exact h_build_cont.measurable
    have hFderiv_meas :
        Measurable (fun p : P =>
          fderiv ℝ F (CoordLine.buildAlong (w := w) (i := i) p.1 p.2)) :=
      (hF_diff.continuous_fderiv (Ne.symm (zero_ne_one' (WithTop ℕ∞)))).measurable.comp h_build_meas
    have hEval : Measurable (fun L : H →L[ℝ] ℝ => L (w i)) :=
      ContinuousLinearMap.measurable_apply (w i)
    have h_rhs :
        Measurable (fun p : P =>
          (fderiv ℝ F (CoordLine.buildAlong (w := w) (i := i) p.1 p.2)) (w i)) :=
      hEval.comp hFderiv_meas
    have h_eq :
        (fun p : P =>
          deriv (fun t => F (CoordLine.buildAlong (w := w) (i := i) p.1 t)) p.2)
        =
        (fun p : P =>
          (fderiv ℝ F (CoordLine.buildAlong (w := w) (i := i) p.1 p.2)) (w i)) := by
      funext p
      have : ∀ t : ℝ,
          CoordLine.buildAlong (w := w) (i := i) p.1 t
            = (∑ j, (p.1 j) • w j.1) + t • w i := by
        intro t; simp [CoordLine.buildAlong, add_comm]
      simpa [this, CoordLine.line_def] using
        (CoordLine.deriv_F_along (w := w) (i := i) (F := F)
          (hF := hF_diff) (z := ∑ j, (p.1 j) • w j.1) (x := p.2))
    simpa [ψ, h_eq] using h_rhs
  have hmap_pair := map_pair_eq_prod_of_indep Y X hY_meas hX_meas hIndep
  have hchg_pair_φ :
      ∫ ω, φ (Y ω, X ω) ∂ℙ
        = ∫ p, φ p ∂Measure.map (fun ω => (Y ω, X ω)) ℙ := by
    simpa using
      integral_pair_change_of_variables Y X hY_meas hX_meas hφ_meas
  have hchg_pair_ψ :
      ∫ ω, ψ (Y ω, X ω) ∂ℙ
        = ∫ p, ψ p ∂Measure.map (fun ω => (Y ω, X ω)) ℙ := by
    simpa using
      integral_pair_change_of_variables Y X hY_meas hX_meas hψ_meas
  have hchg_φ :
      ∫ ω, φ (Y ω, X ω) ∂ℙ
        = ∫ p, φ p ∂((Measure.map Y ℙ).prod (Measure.map X ℙ)) := by
    simpa [hmap_pair] using hchg_pair_φ
  have hchg_ψ :
      ∫ ω, ψ (Y ω, X ω) ∂ℙ
        = ∫ p, ψ p ∂((Measure.map Y ℙ).prod (Measure.map X ℙ)) := by
    simpa [hmap_pair] using hchg_pair_ψ
  have hX_law : Measure.map X ℙ = ProbabilityTheory.gaussianReal 0 vτ := hX_gauss
  have hInt_φΩ :
      Integrable (fun ω =>
        φ (Y ω, X ω)) ℙ := by
    simpa [φ] using
      (integrable_coord_mul_F_of_indep (w := w) (i := i)
        (F := F) (hF_diff := hF_diff) (hF_growth := hF_growth)
        (vτ := vτ) (X := X) (Y := Y)
        (hX_meas := hX_meas) (hY_meas := hY_meas)
        (_hIndep := hIndep) (hX_gauss := hX_gauss)
        (hY_gauss0 := hY_gauss0))
  have hInt_ψΩ :
      Integrable (fun ω =>
        ψ (Y ω, X ω)) ℙ := by
    simpa [ψ] using
      (integrable_deriv_F_along_coord_of_indep (w := w) (i := i)
        (F := F) (hF_diff := hF_diff) (hF_growth := hF_growth)
        (vτ := vτ) (X := X) (Y := Y)
        (hX_meas := hX_meas) (hY_meas := hY_meas)
        (_hIndep := hIndep) (hX_gauss := hX_gauss)
        (hY_gauss0 := hY_gauss0))

  have hprod' :
      ∫ p, φ p ∂((Measure.map Y ℙ).prod (Measure.map X ℙ))
        =
      (vτ : ℝ) *
      ∫ p, ψ p ∂((Measure.map Y ℙ).prod (Measure.map X ℙ)) := by
    haveI : SFinite (Measure.map Y ℙ) := Measure.instSFiniteMap ℙ Y
    have h :=
      stein_coord_on_product (w := w) (i := i) (F := F)
        (hF_diff := hF_diff) (hF_growth := hF_growth)
        (μY := Measure.map Y ℙ) (vτ := vτ)
        (hμY_sfinite := inferInstance)
        (hInt_left := by
          simpa [hX_law, φ] using
            (integrable_phi_on_mapY_prod_gauss (Y := Y) (X := X)
              (hY := hY_meas) (hX := hX_meas) (hIndep := hIndep)
              (v := vτ) (hXlaw := hX_law) (hφ_meas := hφ_meas)
              (hInt := hInt_φΩ)))
        (hInt_right₀ := by
          simpa [hX_law, ψ] using
            (integrable_psi_on_mapY_prod_gauss (Y := Y) (X := X)
              (hY := hY_meas) (hX := hX_meas) (hIndep := hIndep)
              (v := vτ) (hXlaw := hX_law) (hψ_meas := hψ_meas)
              (hInt := hInt_ψΩ)))
    simpa [φ, ψ, hX_law] using h
  calc
    ∫ ω, X ω * F (CoordLine.buildAlong (w := w) (i := i) (Y ω) (X ω)) ∂ℙ
        = ∫ ω, φ (Y ω, X ω) ∂ℙ := by
          simp [φ]
    _ = ∫ p, φ p ∂((Measure.map Y ℙ).prod (Measure.map X ℙ)) := hchg_φ
    _ = (vτ : ℝ) * ∫ p, ψ p ∂((Measure.map Y ℙ).prod (Measure.map X ℙ)) := hprod'
    _ = (vτ : ℝ) * ∫ ω, ψ (Y ω, X ω) ∂ℙ := by
          have := congrArg (fun z => (vτ : ℝ) * z) (hchg_ψ.symm)
          simpa using this
    _ = (vτ : ℝ) * ∫ ω, deriv (fun t => F (CoordLine.buildAlong (w := w) (i := i) (Y ω) t)) (X ω) ∂ℙ := by
          simp [ψ]

/-- Final split that replaces the old `stein_coord_with_param_split`. -/
lemma stein_coord_with_param'
  {g : Ω → H} (hg : PhysLean.Probability.GaussianIBP.IsGaussianHilbert g)
  {F : H → ℝ} (hF_diff : ContDiff ℝ 1 F)
  (hF_growth : PhysLean.Probability.GaussianIBP.HasModerateGrowth F)
  (i : hg.ι) :
  ∫ ω, (PhysLean.Probability.GaussianIBP.coord hg.w g i ω) * F (g ω) ∂ℙ
    = (hg.τ i : ℝ) * ∫ ω, (fderiv ℝ F (g ω)) (hg.w i) ∂ℙ := by
  classical
  let X := PhysLean.Probability.GaussianIBP.coord hg.w g i
  let Y := fun ω => fun j : PhysLean.Probability.GaussianIBP.CoordLine.Comp hg.ι i =>
    PhysLean.Probability.GaussianIBP.coord hg.w g j.1 ω
  have hX_meas : Measurable X :=
    (PhysLean.Probability.GaussianIBP.coord_measurable (g := g) hg) i
  have hY_meas : Measurable Y :=
    measurable_pi_iff.mpr (fun j =>
      (PhysLean.Probability.GaussianIBP.coord_measurable (g := g) hg) j.1)
  have hIndep := ProbabilityTheory.indep_coord_complement (hg := hg) (i := i)
  have hX_gauss := (PhysLean.Probability.GaussianIBP.coord_isGaussian_and_indep (g := g) hg).1 i
  have hcoord_eq_c :
      PhysLean.Probability.GaussianIBP.coord hg.w g = hg.c :=
    PhysLean.Probability.GaussianIBP.coord_eq_c (g := g) hg
  have h_decomp : ∀ ω, g ω =
      PhysLean.Probability.GaussianIBP.CoordLine.buildAlong (w := hg.w) (i := i) (Y ω) (X ω) := by
    intro ω
    have hrepr : g ω = ∑ j : hg.ι, (hg.c j ω) • hg.w j := by
      simpa using congrArg (fun f => f ω) hg.repr
    have hsplit :
        ∑ j : hg.ι, (hg.c j ω) • hg.w j
          =
        (∑ j : PhysLean.Probability.GaussianIBP.CoordLine.Comp hg.ι i,
           (hg.c j.1 ω) • hg.w j.1) + (hg.c i ω) • hg.w i := by
      simpa using
        PhysLean.Probability.GaussianIBP.CoordLine.repr_split_along
          (w := hg.w) (i := i) (c := hg.c) ω
    have hY' : (fun j : PhysLean.Probability.GaussianIBP.CoordLine.Comp hg.ι i => Y ω j)
                = (fun j => hg.c j.1 ω) := by
      funext j
      simp [Y]; rw [← hcoord_eq_c]; aesop
    have hX' : X ω = hg.c i ω := by
      simp [X, hcoord_eq_c]
    calc
      g ω = ∑ j, (hg.c j ω) • hg.w j := hrepr
      _ = (∑ j : PhysLean.Probability.GaussianIBP.CoordLine.Comp hg.ι i,
              (hg.c j.1 ω) • hg.w j.1) + (hg.c i ω) • hg.w i := hsplit
      _ = (∑ j : PhysLean.Probability.GaussianIBP.CoordLine.Comp hg.ι i,
              (Y ω j) • hg.w j.1) + (X ω) • hg.w i := by
            simp [hY', hX']
      _ = PhysLean.Probability.GaussianIBP.CoordLine.buildAlong
              (w := hg.w) (i := i) (Y ω) (X ω) := by
            simp [PhysLean.Probability.GaussianIBP.CoordLine.buildAlong,
                  add_comm]
  set P := (PhysLean.Probability.GaussianIBP.CoordLine.Comp hg.ι i → ℝ) × ℝ
  set φ : P → ℝ :=
    fun p => p.2 * F (PhysLean.Probability.GaussianIBP.CoordLine.buildAlong
                        (w := hg.w) (i := i) p.1 p.2)
  set ψ : P → ℝ :=
    fun p => deriv (fun t =>
      F (PhysLean.Probability.GaussianIBP.CoordLine.buildAlong
            (w := hg.w) (i := i) p.1 t)) p.2
  have hφ_meas : Measurable φ := by
    have h_eval_sum :
        Continuous (fun y : PhysLean.Probability.GaussianIBP.CoordLine.Comp hg.ι i → ℝ =>
          ∑ j, (y j) • hg.w j.1) := by
      refine
        continuous_finset_sum
          (s := (Finset.univ : Finset (PhysLean.Probability.GaussianIBP.CoordLine.Comp hg.ι i)))
          (f := fun (j : PhysLean.Probability.GaussianIBP.CoordLine.Comp hg.ι i)
                       (y : PhysLean.Probability.GaussianIBP.CoordLine.Comp hg.ι i → ℝ) =>
                       (y j) • hg.w j.1)
          ?_
      intro j _
      simpa using (continuous_apply j).smul continuous_const
    have h1 : Continuous (fun p : P =>
        ∑ j : PhysLean.Probability.GaussianIBP.CoordLine.Comp hg.ι i, (p.1 j) • hg.w j.1) :=
      h_eval_sum.comp continuous_fst
    have h2 : Continuous (fun p : P => p.2 • hg.w i) :=
      continuous_snd.smul continuous_const
    have h_build_cont : Continuous (fun p : P =>
        PhysLean.Probability.GaussianIBP.CoordLine.buildAlong (w := hg.w) (i := i) p.1 p.2) := by
      simpa [PhysLean.Probability.GaussianIBP.CoordLine.buildAlong,
             add_comm, add_left_comm, add_assoc] using h1.add h2
    have hFcont : Continuous (fun p : P =>
        F (PhysLean.Probability.GaussianIBP.CoordLine.buildAlong (w := hg.w) (i := i) p.1 p.2)) :=
      hF_diff.continuous.comp h_build_cont
    have hSnd : Continuous (fun p : P => p.2) := continuous_snd
    exact (hSnd.measurable.mul hFcont.measurable)
  have hψ_meas : Measurable ψ := by
    have h_eval_sum :
        Continuous (fun y : PhysLean.Probability.GaussianIBP.CoordLine.Comp hg.ι i → ℝ =>
          ∑ j, (y j) • hg.w j.1) := by
      refine
        continuous_finset_sum
          (s := (Finset.univ : Finset (PhysLean.Probability.GaussianIBP.CoordLine.Comp hg.ι i)))
          (f := fun (j : PhysLean.Probability.GaussianIBP.CoordLine.Comp hg.ι i)
                       (y : PhysLean.Probability.GaussianIBP.CoordLine.Comp hg.ι i → ℝ) =>
                       (y j) • hg.w j.1)
          ?_
      intro j _
      simpa using (continuous_apply j).smul continuous_const
    have h1 : Continuous (fun p : P =>
        ∑ j : PhysLean.Probability.GaussianIBP.CoordLine.Comp hg.ι i, (p.1 j) • hg.w j.1) :=
      h_eval_sum.comp continuous_fst
    have h2 : Continuous (fun p : P => p.2 • hg.w i) :=
      continuous_snd.smul continuous_const
    have h_build_meas : Measurable (fun p : P =>
        PhysLean.Probability.GaussianIBP.CoordLine.buildAlong (w := hg.w) (i := i) p.1 p.2) := by
      have h_build_cont : Continuous (fun p : P =>
          PhysLean.Probability.GaussianIBP.CoordLine.buildAlong (w := hg.w) (i := i) p.1 p.2) := by
        simpa [PhysLean.Probability.GaussianIBP.CoordLine.buildAlong,
               add_comm, add_left_comm, add_assoc] using h1.add h2
      exact h_build_cont.measurable
    have hFderiv_meas :
        Measurable (fun p : P =>
          fderiv ℝ F (PhysLean.Probability.GaussianIBP.CoordLine.buildAlong
                        (w := hg.w) (i := i) p.1 p.2)) :=
      (hF_diff.continuous_fderiv (Ne.symm (zero_ne_one' (WithTop ℕ∞)))).measurable.comp h_build_meas
    have hEval : Measurable (fun L : H →L[ℝ] ℝ => L (hg.w i)) :=
      ContinuousLinearMap.measurable_apply (hg.w i)
    have h_rhs :
        Measurable (fun p : P =>
          (fderiv ℝ F (PhysLean.Probability.GaussianIBP.CoordLine.buildAlong
                        (w := hg.w) (i := i) p.1 p.2)) (hg.w i)) :=
      hEval.comp hFderiv_meas
    have h_eq :
        (fun p : P =>
          deriv (fun t =>
            F (PhysLean.Probability.GaussianIBP.CoordLine.buildAlong
                  (w := hg.w) (i := i) p.1 t)) p.2)
        =
        (fun p : P =>
          (fderiv ℝ F (PhysLean.Probability.GaussianIBP.CoordLine.buildAlong
                        (w := hg.w) (i := i) p.1 p.2)) (hg.w i)) := by
      funext p
      have : ∀ t : ℝ,
          PhysLean.Probability.GaussianIBP.CoordLine.buildAlong (w := hg.w) (i := i) p.1 t
            = (∑ j, (p.1 j) • hg.w j.1) + t • hg.w i := by
        intro t; simp [PhysLean.Probability.GaussianIBP.CoordLine.buildAlong,
                       add_comm]
      simpa [this, PhysLean.Probability.GaussianIBP.CoordLine.line_def] using
        (PhysLean.Probability.GaussianIBP.CoordLine.deriv_F_along
          (w := hg.w) (i := i) (F := F)
          (hF := hF_diff)
          (z := ∑ j, (p.1 j) • hg.w j.1) (x := p.2))
    simpa [ψ, h_eq] using h_rhs
  have hmap_pair := map_pair_eq_prod_of_indep Y X hY_meas hX_meas hIndep
  have hchg_pair_φ :
      ∫ ω, φ (Y ω, X ω) ∂ℙ
        = ∫ p, φ p ∂Measure.map (fun ω => (Y ω, X ω)) ℙ := by
    simpa using
      integral_pair_change_of_variables Y X hY_meas hX_meas hφ_meas
  have hchg_pair_ψ :
      ∫ ω, ψ (Y ω, X ω) ∂ℙ
        = ∫ p, ψ p ∂Measure.map (fun ω => (Y ω, X ω)) ℙ := by
    simpa using
      integral_pair_change_of_variables Y X hY_meas hX_meas hψ_meas
  have hchg_φ :
      ∫ ω, φ (Y ω, X ω) ∂ℙ
        = ∫ p, φ p ∂((Measure.map Y ℙ).prod (Measure.map X ℙ)) := by
    simpa [hmap_pair] using hchg_pair_φ
  have hchg_ψ :
      ∫ ω, ψ (Y ω, X ω) ∂ℙ
        = ∫ p, ψ p ∂((Measure.map Y ℙ).prod (Measure.map X ℙ)) := by
    simpa [hmap_pair] using hchg_pair_ψ
  have hInt_φΩ :
      Integrable (fun ω =>
        φ (Y ω, X ω)) ℙ := by
    have : Integrable (fun ω => X ω * F (g ω)) ℙ :=
      integrable_coord_mul_F hg hF_diff hF_growth i
    simpa [φ, h_decomp] using this
  have hInt_ψΩ :
      Integrable (fun ω =>
        ψ (Y ω, X ω)) ℙ := by
    have h_deriv_pointwise : ∀ ω,
        deriv (fun t =>
          F (PhysLean.Probability.GaussianIBP.CoordLine.buildAlong
                (w := hg.w) (i := i) (Y ω) t)) (X ω)
          = (fderiv ℝ F (g ω)) (hg.w i) := by
      intro ω
      have := PhysLean.Probability.GaussianIBP.CoordLine.deriv_F_along
        (w := hg.w) (i := i) (F := F) (hF := hF_diff)
        (z := ∑ j : PhysLean.Probability.GaussianIBP.CoordLine.Comp hg.ι i,
                  (Y ω j) • hg.w j.1)
        (x := X ω)
      simpa [PhysLean.Probability.GaussianIBP.CoordLine.line_def,
             PhysLean.Probability.GaussianIBP.CoordLine.buildAlong,
             h_decomp ω, add_comm, add_left_comm, add_assoc] using this
    have hInt_fderiv :
        Integrable (fun ω => (fderiv ℝ F (g ω)) (hg.w i)) ℙ :=
      integrable_fderiv_apply hg hF_diff hF_growth (hg.w i)
    have h_eq_fun :
        (fun ω => ψ (Y ω, X ω))
          = (fun ω => (fderiv ℝ F (g ω)) (hg.w i)) := by
      funext ω
      simp [ψ]
      exact h_deriv_pointwise ω
    simpa [h_eq_fun] using hInt_fderiv
  have hX_law : Measure.map X ℙ = ProbabilityTheory.gaussianReal 0 (hg.τ i) := hX_gauss
  have hprod' :
      ∫ p, φ p ∂((Measure.map Y ℙ).prod (Measure.map X ℙ))
        =
      (hg.τ i : ℝ) *
      ∫ p, ψ p ∂((Measure.map Y ℙ).prod (Measure.map X ℙ)) := by
    haveI : SFinite (Measure.map Y ℙ) := Measure.instSFiniteMap ℙ Y
    have h :=
      stein_coord_on_product (w := hg.w) (i := i) (F := F)
        (hF_diff := hF_diff) (hF_growth := hF_growth)
        (μY := Measure.map Y ℙ) (vτ := hg.τ i)
        (hμY_sfinite := inferInstance)
        (hInt_left := by
          simpa [hX_law, φ] using
            (integrable_phi_on_mapY_prod_gauss (Y := Y) (X := X)
              (hY := hY_meas) (hX := hX_meas) (hIndep := hIndep)
              (v := hg.τ i) (hXlaw := hX_law) (hφ_meas := hφ_meas)
              (hInt := hInt_φΩ)))
        (hInt_right₀ := by
          simpa [hX_law, ψ] using
            (integrable_psi_on_mapY_prod_gauss (Y := Y) (X := X)
              (hY := hY_meas) (hX := hX_meas) (hIndep := hIndep)
              (v := hg.τ i) (hXlaw := hX_law) (hψ_meas := hψ_meas)
              (hInt := hInt_ψΩ)))
    simpa [φ, ψ, hX_law] using h
  calc
    ∫ ω, X ω * F (g ω) ∂ℙ
        = ∫ ω, φ (Y ω, X ω) ∂ℙ := by
          simp [φ, h_decomp]
    _ = ∫ p, φ p ∂((Measure.map Y ℙ).prod (Measure.map X ℙ)) := hchg_φ
    _ = (hg.τ i : ℝ) * ∫ p, ψ p ∂((Measure.map Y ℙ).prod (Measure.map X ℙ)) := hprod'
    _ = (hg.τ i : ℝ) * ∫ ω, ψ (Y ω, X ω) ∂ℙ := by
          have := congrArg (fun z => (hg.τ i : ℝ) * z) (hchg_ψ.symm)
          simpa using this
    _ = (hg.τ i : ℝ) * ∫ ω, (fderiv ℝ F (g ω)) (hg.w i) ∂ℙ := by
          have h_deriv_pointwise : ∀ ω,
              deriv (fun t =>
                F (PhysLean.Probability.GaussianIBP.CoordLine.buildAlong
                      (w := hg.w) (i := i) (Y ω) t)) (X ω)
              = (fderiv ℝ F (g ω)) (hg.w i) := by
            intro ω
            have := PhysLean.Probability.GaussianIBP.CoordLine.deriv_F_along
              (w := hg.w) (i := i) (F := F) (hF := hF_diff)
              (z := ∑ j : PhysLean.Probability.GaussianIBP.CoordLine.Comp hg.ι i,
                        (Y ω j) • hg.w j.1)
              (x := X ω)
            simpa [PhysLean.Probability.GaussianIBP.CoordLine.line_def,
                   PhysLean.Probability.GaussianIBP.CoordLine.buildAlong,
                   h_decomp ω, add_comm, add_left_comm, add_assoc] using this
          refine congrArg (fun r => (hg.τ i : ℝ) * r) ?_
          refine integral_congr_ae (ae_of_all _ (fun ω => ?_))
          exact h_deriv_pointwise ω

/-- Wrapper that reuses the split proof. -/
lemma stein_coord_with_param
  {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H]
  {g : Ω → H} (hg : PhysLean.Probability.GaussianIBP.IsGaussianHilbert g)
  {F : H → ℝ} (hF_diff : ContDiff ℝ 1 F)
  (hF_growth : PhysLean.Probability.GaussianIBP.HasModerateGrowth F)
  (i : hg.ι) :
  𝔼[(fun ω => (coord hg.w g i ω) * F (g ω))]
    = (hg.τ i : ℝ) * 𝔼[(fun ω => (fderiv ℝ F (g ω)) (hg.w i))] :=
  stein_coord_with_param' (g := g) hg hF_diff hF_growth i

/-- The key 1D conditional IBP step for a fixed basis direction `w i`.
This is an immediate wrapper around `stein_coord_with_param`. -/
lemma coord_IBP
    {g : Ω → H} (hg : IsGaussianHilbert g)
    {F : H → ℝ} (hF_diff : ContDiff ℝ 1 F)
    (hF_growth : HasModerateGrowth F)
    (i : hg.ι) :
  𝔼[(fun ω => (coord hg.w g i ω) * F (g ω))]
    = (hg.τ i : ℝ) * 𝔼[(fun ω => (fderiv ℝ F (g ω)) (hg.w i))] := by
  classical
  simpa using
    stein_coord_with_param (g := g) (hg := hg) (F := F)
      (hF_diff := hF_diff) (hF_growth := hF_growth) (i := i)

/-- **Gaussian IBP on a finite-dimensional Hilbert space (covariant form).**
If `g` is a centered Gaussian on `H` modeled by independent coordinates along an
orthonormal basis with variances `τ i`, then for every `h ∈ H` and every `C¹`
 test function `F : H → ℝ` of moderate growth,

```
  E[⟪g, h⟫ F(g)] = E[(fderiv ℝ F (g)) (Σ h)],
  where  Σ h = ∑ i, (τ i : ℝ) * ⟪h, w i⟫ • w i.
```
-/
@[simp]
theorem gaussian_integration_by_parts_hilbert_cov
    {g : Ω → H} (hg : IsGaussianHilbert g)
    (h : H)
    {F : H → ℝ} (hF_diff : ContDiff ℝ 1 F) (hF_growth : HasModerateGrowth F) :
    𝔼[(fun ω => ⟪g ω, h⟫_ℝ * F (g ω))]
      = 𝔼[(fun ω => (fderiv ℝ F (g ω))
          (∑ i : hg.ι, ((hg.τ i : ℝ) * ⟪h, hg.w i⟫_ℝ) • hg.w i))] := by
  classical
  let ι := hg.ι
  let w := hg.w
  have inner_expansion :
      (fun ω => ⟪g ω, h⟫_ℝ)
        = (fun ω => ∑ i : ι, (⟪g ω, w i⟫_ℝ) * (⟪h, w i⟫_ℝ)) := by
    funext ω; simpa using Aux.inner_decomp (w := w) (x := g ω) (y := h)
  have step1 :
      𝔼[(fun ω => ⟪g ω, h⟫_ℝ * F (g ω))]
        = ∑ i : ι, (⟪h, w i⟫_ℝ) * 𝔼[(fun ω => (⟪g ω, w i⟫_ℝ) * F (g ω))] := by
    classical
    have h_int : ∀ i : ι, Integrable (fun ω => (⟪g ω, w i⟫_ℝ) * F (g ω)) :=
      fun i => integrable_coord_mul_F hg hF_diff hF_growth i
    have distr :
        (fun ω =>
          (∑ i : ι, (⟪g ω, w i⟫_ℝ) * (⟪h, w i⟫_ℝ)) * F (g ω))
      = (fun ω =>
          ∑ i : ι, (⟪h, w i⟫_ℝ) * ((⟪g ω, w i⟫_ℝ) * F (g ω))) := by
      funext ω
      simp [mul_comm, mul_left_comm]
      exact Finset.mul_sum Finset.univ (fun i => ⟪h, w i⟫_ℝ * ⟪g ω, w i⟫_ℝ) (F (g ω))
    calc
      𝔼[(fun ω => ⟪g ω, h⟫_ℝ * F (g ω))]
          = 𝔼[(fun ω =>
                (∑ i : ι, (⟪g ω, w i⟫_ℝ) * (⟪h, w i⟫_ℝ)) * F (g ω))] := by
              refine integral_congr_ae (ae_of_all _ (fun ω => ?_))
              have hpt :
                  ⟪g ω, h⟫_ℝ
                    = ∑ i : ι, (⟪g ω, w i⟫_ℝ) * (⟪h, w i⟫_ℝ) := by
                have := congrArg (fun f : Ω → ℝ => f ω) inner_expansion
                simpa using this
              simpa using congrArg (fun t => t * F (g ω)) hpt
      _ = 𝔼[(fun ω =>
                ∑ i : ι, (⟪h, w i⟫_ℝ) * ((⟪g ω, w i⟫_ℝ) * F (g ω)))] := by
              simp [distr]
      _ = ∑ i : ι, 𝔼[(fun ω =>
                (⟪h, w i⟫_ℝ) * ((⟪g ω, w i⟫_ℝ) * F (g ω)))] := by
              simpa using
                expectation_finset_sum
                  (hg := hg)
                  (f := fun i ω => (⟪h, w i⟫_ℝ) * ((⟪g ω, w i⟫_ℝ) * F (g ω)))
                  (hint := fun i => (h_int i).const_mul (⟪h, w i⟫_ℝ))
      _ = ∑ i : ι, (⟪h, w i⟫_ℝ) * 𝔼[(fun ω => (⟪g ω, w i⟫_ℝ) * F (g ω))] := by
              refine Finset.sum_congr rfl ?_
              intro i _
              simpa [mul_comm, mul_left_comm, mul_assoc]
                using expectation_const_mul
                  (c := (⟪h, w i⟫_ℝ))
                  (f := fun ω => (⟪g ω, w i⟫_ℝ) * F (g ω))
                  ((h_int i))
  have step2 :
      ∀ i : ι,
        𝔼[(fun ω => (⟪g ω, w i⟫_ℝ) * F (g ω))]
          = (hg.τ i : ℝ) * 𝔼[(fun ω => (fderiv ℝ F (g ω)) (w i))] := by
    intro i
    simpa [coord] using
      coord_IBP (g := g) (hg := hg) (F := F)
        (hF_diff := hF_diff) (hF_growth := hF_growth) (i := i)
  have step3 :
      ∑ i : ι, (⟪h, w i⟫_ℝ) * 𝔼[(fun ω => (⟪g ω, w i⟫_ℝ) * F (g ω))]
        = ∑ i : ι, ((hg.τ i : ℝ) * ⟪h, w i⟫_ℝ)
            * 𝔼[(fun ω => (fderiv ℝ F (g ω)) (w i))] := by
    classical
    refine Finset.sum_congr rfl ?_
    intro i _
    have h_comm :
        𝔼[(fun ω => F (g ω) * ⟪g ω, w i⟫_ℝ)]
          = 𝔼[(fun ω => ⟪g ω, w i⟫_ℝ * F (g ω))] := by
      change ∫ ω, F (g ω) * ⟪g ω, w i⟫_ℝ ∂ℙ
          = ∫ ω, ⟪g ω, w i⟫_ℝ * F (g ω) ∂ℙ
      refine integral_congr_ae (ae_of_all _ (fun ω => ?_))
      simp [mul_comm]
    calc
      (⟪h, w i⟫_ℝ) * 𝔼[(fun ω => (⟪g ω, w i⟫_ℝ) * F (g ω))]
          = (⟪h, w i⟫_ℝ) * ((hg.τ i : ℝ) * 𝔼[(fun ω =>
                (fderiv ℝ F (g ω)) (w i))]) := by
                simp [step2 i]
      _ = ((hg.τ i : ℝ) * ⟪h, w i⟫_ℝ) * 𝔼[(fun ω =>
                (fderiv ℝ F (g ω)) (w i))] := by
                simp [mul_left_comm, mul_assoc]
  have step4 :
      (∑ i : ι, ((hg.τ i : ℝ) * ⟪h, w i⟫_ℝ)
            * 𝔼[(fun ω => (fderiv ℝ F (g ω)) (w i))])
        = 𝔼[(fun ω => (fderiv ℝ F (g ω))
              (∑ i : ι, ((hg.τ i : ℝ) * ⟪h, w i⟫_ℝ) • w i))] := by
    classical
    simpa using
      (fderiv_expectation_weighted_sum
        (hg := hg) (hF_diff := hF_diff) (hF_growth := hF_growth)
        (a := fun i : ι => (hg.τ i : ℝ) * ⟪h, w i⟫_ℝ)).symm
  calc
    𝔼[(fun ω => ⟪g ω, h⟫_ℝ * F (g ω))]
        = ∑ i : ι, (⟪h, w i⟫_ℝ) * 𝔼[(fun ω => (⟪g ω, w i⟫_ℝ) * F (g ω))] := step1
    _ = ∑ i : ι, ((hg.τ i : ℝ) * ⟪h, w i⟫_ℝ)
            * 𝔼[(fun ω => (fderiv ℝ F (g ω)) (w i))] := step3
    _ = 𝔼[(fun ω => (fderiv ℝ F (g ω))
              (∑ i : ι, ((hg.τ i : ℝ) * ⟪h, w i⟫_ℝ) • w i))] := step4

/-- **Operator form (coordinate‑free).** Using the covariance operator `Σ`,
the covariant IBP reads

```
  𝔼[⟪g, h⟫ F(g)] = 𝔼[(fderiv ℝ F (g)) (Σ h)].
```
-/
@[simp]
 theorem gaussian_integration_by_parts_hilbert_cov_op
    {g : Ω → H} (hg : IsGaussianHilbert g)
    (h : H)
    {F : H → ℝ} (hF_diff : ContDiff ℝ 1 F) (hF_growth : HasModerateGrowth F) :
    𝔼[(fun ω => ⟪g ω, h⟫_ℝ * F (g ω))]
      = 𝔼[(fun ω => (fderiv ℝ F (g ω)) ((covOp (g := g) hg) h))] := by
  classical
  simpa [covOp_apply (g := g) (hg := hg) h]
    using gaussian_integration_by_parts_hilbert_cov
      (g := g) (hg := hg) (h := h) (F := F)
      (hF_diff := hF_diff) (hF_growth := hF_growth)

section LinearTestFunctions

/-- Zero mean of Gaussian inner coordinates (take `F ≡ 1`). -/
@[simp]
lemma gaussian_zero_mean_inner
    {g : Ω → H} (hg : IsGaussianHilbert g) (h : H) :
    𝔼[(fun ω => ⟪g ω, h⟫_ℝ)] = 0 := by
  classical
  have hMG : HasModerateGrowth (fun _ : H => (1 : ℝ)) :=
    hasModerateGrowth_const (H := H) (c := (1 : ℝ))
  have hDiff : ContDiff ℝ 1 (fun _ : H => (1 : ℝ)) := by
    simpa using (contDiff_const : ContDiff ℝ 1 (fun _ : H => (1 : ℝ)))
  simpa using
    (gaussian_integration_by_parts_hilbert_cov_op (g := g) (hg := hg) (h := h)
      (F := fun _ : H => (1 : ℝ)) (hF_diff := hDiff) (hF_growth := hMG))

/-- Covariance identity: `E[⟪g,h⟫ ⟪g,u⟫] = ⟪(Σ h), u⟫`. -/
@[simp]
lemma gaussian_covariance_pairing
    {g : Ω → H} (hg : IsGaussianHilbert g) (h u : H) :
    𝔼[(fun ω => ⟪g ω, h⟫_ℝ * ⟪g ω, u⟫_ℝ)]
      = ⟪(covOp (g := g) hg) h, u⟫_ℝ := by
  classical
  let L : H →L[ℝ] ℝ := ContinuousLinearMap.innerSL ℝ u
  have hDiff : ContDiff ℝ 1 (fun z : H => L z) := L.contDiff
  have hMG : HasModerateGrowth (fun z : H => L z) := hasModerateGrowth_of_clm (L := L)
  have hIBP :=
    gaussian_integration_by_parts_hilbert_cov_op (g := g) (hg := hg) (h := h)
      (F := fun z : H => L z) (hF_diff := hDiff) (hF_growth := hMG)
  have hderiv : ∀ z, fderiv ℝ (fun x : H => L x) z = L := by
    intro z
    exact ContinuousLinearMap.fderiv L
  have hR :
      𝔼[(fun ω : Ω =>
        (fderiv ℝ (fun z : H => L z) (g ω)) ((covOp (g := g) hg) h))]
      =
      𝔼[(fun _ω : Ω => L ((covOp (g := g) hg) h))] := by
    simp [hderiv]
  have hExpConst :
      𝔼[(fun _ω : Ω => L ((covOp (g := g) hg) h))] = L ((covOp (g := g) hg) h) := by
    simp
  have hMain :
      𝔼[(fun ω : Ω => ⟪g ω, h⟫_ℝ * L (g ω))]
        = L ((covOp (g := g) hg) h) := by
    have h' :
        𝔼[(fun ω : Ω => ⟪g ω, h⟫_ℝ * L (g ω))]
          = 𝔼[(fun _ω : Ω => L ((covOp (g := g) hg) h))] := by
      simpa [hR] using hIBP
    simpa [hExpConst] using h'
  have hRhs :
      𝔼[(fun ω : Ω => ⟪g ω, h⟫_ℝ * ⟪u, g ω⟫_ℝ)]
        = ⟪u, (covOp (g := g) hg) h⟫_ℝ := by
    simpa only [L, ContinuousLinearMap.innerSL_apply] using hMain
  simpa [real_inner_comm] using hRhs


end LinearTestFunctions

/-- **Standard-covariance corollary.** If all coordinate variances are `1`, the
covariant formula reduces to the usual identity with `h` on the RHS. -/
@[simp]
 theorem gaussian_integration_by_parts_hilbert_std
    {g : Ω → H} (hg : IsGaussianHilbert g)
    (hτ : ∀ i : hg.ι, hg.τ i = 1)
    (h : H)
    {F : H → ℝ} (hF_diff : ContDiff ℝ 1 F) (hF_growth : HasModerateGrowth F) :
    𝔼[(fun ω => ⟪g ω, h⟫_ℝ * F (g ω))]
      = 𝔼[(fun ω => (fderiv ℝ F (g ω)) h)] := by
  classical
  have := gaussian_integration_by_parts_hilbert_cov
    (g := g) (hg := hg) (h := h) (F := F)
    (hF_diff := hF_diff) (hF_growth := hF_growth)
  have h_as_sum :
      (∑ i : hg.ι, ((hg.τ i : ℝ) * ⟪h, hg.w i⟫_ℝ) • hg.w i) = h := by
    classical
    have : (∑ i : hg.ι, (⟪h, hg.w i⟫_ℝ) • hg.w i) = h := by
      simpa [hg.w.repr_apply_apply, real_inner_comm] using (hg.w.sum_repr h)
    simpa [hτ, mul_one] using this
  simpa [h_as_sum] using this

/-! ### Roadmap for subsequent iterations
* Prove the integrability lemmas using Gaussian moment finiteness results in mathlib.
* Prove `stein_coord_with_param` by unfolding the conditional expectation step
  and invoking the parameterized 1D Stein identity from the imported file.
* Remove the finite-dimensional index restriction by replacing finite sums with
  `∑'` and applying dominated convergence; the present structure already points
  to the covariance operator `Σ` built from the spectral data `(w, τ)`.
-/


/-! ## Further corollaries and operator‑centric consequences
These statements are immediate algebraic fallouts of the operator‑form IBP
and require no extra analysis beyond what is already used above.
-/
section MoreCorollaries

variable {g : Ω → H}

/-- **CLM test functions.** A clean operator‑form covariance identity for any
continuous linear functional `L : H →L[ℝ] ℝ`.

This is just `gaussian_integration_by_parts_hilbert_cov_op` with `F = L`, whose
Fréchet derivative is constantly `L`. -/
@[simp]
lemma gaussian_covariance_clm
    (hg : IsGaussianHilbert (Ω := Ω) (H := H) g)
    (L : H →L[ℝ] ℝ) (h : H) :
    𝔼[(fun ω => ⟪g ω, h⟫_ℝ * L (g ω))]
      = L ((covOp (g := g) hg) h) := by
  classical
  have hDiff : ContDiff ℝ 1 (fun z : H => L z) := L.contDiff
  have hMG   : HasModerateGrowth (fun z : H => L z) :=
    hasModerateGrowth_of_clm (L := L)
  simpa using
    (gaussian_integration_by_parts_hilbert_cov_op (g := g) (hg := hg)
      (h := h) (F := fun z : H => L z) (hF_diff := hDiff) (hF_growth := hMG))

/-- **Quadratic moment along a direction.** Specializing the covariance pairing
with `u = h` gives the second moment of the scalar coordinate. -/
@[simp]
lemma gaussian_quadratic_moment
    (hg : IsGaussianHilbert (Ω := Ω) (H := H) g) (h : H) :
    𝔼[(fun ω => (⟪g ω, h⟫_ℝ)^2)]
      = ⟪(covOp (g := g) hg) h, h⟫_ℝ := by
  classical
  simpa [pow_two] using
    (gaussian_covariance_pairing (g := g) (hg := hg) (h := h) (u := h))

lemma gaussian_second_moment
    (hg : IsGaussianHilbert (Ω := Ω) (H := H) g) :
    𝔼[(fun ω => ‖g ω‖^2)] = ∑ i : hg.ι, (hg.τ i : ℝ) := by
  classical
  have h_decomp :
      (fun ω => ‖g ω‖^2) = (fun ω => ∑ i : hg.ι, (⟪g ω, hg.w i⟫_ℝ)^2) := by
    funext ω
    simpa [real_inner_self_eq_norm_sq, pow_two] using
      (Aux.inner_decomp (w := hg.w) (x := g ω) (y := g ω))
  have h_each : ∀ i : hg.ι,
      𝔼[(fun ω => (⟪g ω, hg.w i⟫_ℝ)^2)] = (hg.τ i : ℝ) := by
    intro i
    simpa [pow_two,
           covOp_apply (g := g) (hg := hg),
           OrthonormalBasis.inner_eq_ite,
           inner_smul_left] using
      (gaussian_quadratic_moment (g := g) (hg := hg) (h := hg.w i))
  have h_int : ∀ i : hg.ι, Integrable (fun ω => (⟪g ω, hg.w i⟫_ℝ)^2) := by
    intro i
    have hX_gauss :
        ProbabilityTheory.IsCenteredGaussianRV (coord hg.w g i) (hg.τ i) :=
      (coord_isGaussian_and_indep (g := g) hg).1 i
    have hX_meas : Measurable (coord hg.w g i) :=
      (coord_measurable (g := g) hg) i
    simpa [coord, pow_two] using
      (ProbabilityTheory.IsCenteredGaussianRV.integrable_sq
        (Ω := Ω) (X := coord hg.w g i) (v := hg.τ i) hX_gauss hX_meas)
  calc
    𝔼[(fun ω => ‖g ω‖^2)]
        = 𝔼[(fun ω => ∑ i : hg.ι, (⟪g ω, hg.w i⟫_ℝ)^2)] := by
            simp [h_decomp]
    _ = ∑ i : hg.ι, 𝔼[(fun ω => (⟪g ω, hg.w i⟫_ℝ)^2)] := by
            simpa using
              expectation_finset_sum (g := g) (hg := hg)
                (f := fun i ω => (⟪g ω, hg.w i⟫_ℝ)^2) (hint := h_int)
    _ = ∑ i : hg.ι, (hg.τ i : ℝ) := by
            simp [h_each]

end MoreCorollaries
end ProbabilityTheory
end SteinAlongOneCoordinate
end GaussianIBP
end Probability
