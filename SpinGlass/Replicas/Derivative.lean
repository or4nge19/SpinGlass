/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.Replicas

/-!
# The directional derivative of the replica Gibbs average

`A_disorder`, the derivative of the `n`-replica Gibbs average along a Dirac direction of the
disorder space, and its explicit form as a Gibbs correlation. This is the algebraic heart of the
smart-path computation: differentiating the Gibbs weights produces the difference between the
Gibbs average of an observable and the product of Gibbs averages. Talagrand Vol. I, §1.4.
-/

open MeasureTheory ProbabilityTheory Real BigOperators SpinGlass Set
open scoped ENNReal NNReal Topology

namespace SpinGlass

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable (N : ℕ) (h : ℝ)
variable {K₁ K₂ : Config N → Config N → ℝ}
variable (G₁ : GaussianDisorder (Ω := Ω) (N := N) (ℙ : Measure Ω) K₁)
variable (G₂ : GaussianDisorder (Ω := Ω) (N := N) (ℙ : Measure Ω) K₂)

section ReplicaCalculus

variable (n : ℕ)
/-! ### Directional derivative `A_disorder` -/
/-- The derivative of the `n`-replica Gibbs average along the interpolating Hamiltonian, in the
direction of the Dirac vector `e_τ`, read as a function of the disorder. -/
noncomputable def A_disorder (t : ℝ) (f : ReplicaFun N n) (τ : Config N) :
    DisorderSpace (N := N) → ℝ :=
  fun x =>
    fderiv ℝ (fun H' => gibbs_average_n_det (N := N) (n := n) H' f)
      (H_t_disorder N (H_field N h) t x)
      (std_basis N τ)

/-! ### Explicit form of `A_disorder` -/
/-- The explicit replica-sum formula for `A_disorder`: `n ⟨f⟩ p(τ) - ∑_l ⟨f 1_{σˡ = τ}⟩`,
weighted by the interpolated Gibbs weights. -/
noncomputable def A_disorder_explicit (t : ℝ) (f : ReplicaFun N n) (τ : Config N) :
    DisorderSpace (N := N) → ℝ :=
  fun x =>
    ∑ σs : ReplicaSpace N n,
      f σs * (prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) (t := t) σs x) *
        ((n : ℝ) * (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x)
          - ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ))

lemma contDiff_A_disorder_explicit (t : ℝ) (f : ReplicaFun N n) (τ : Config N) :
    ContDiff ℝ 1 (A_disorder_explicit (N := N) (n := n) (h := h) t f τ) := by
  classical
  -- Finite sum over `σs`, each summand is a product of `C^1` functions.
  -- `ContDiff.sum` for `Finset`.
  have hsum :
      ContDiff ℝ 1 (fun x : DisorderSpace (N := N) =>
        ∑ σs : ReplicaSpace N n, f σs *
          (prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) (t := t) σs x) *
            (((n : ℝ) * (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x))
              - ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ))) := by
    refine ContDiff.sum (𝕜 := ℝ) (n := (1 : ℕ))
      (s := (Finset.univ : Finset (ReplicaSpace N n))) ?_
    intro σs _hσs
    have hP : ContDiff ℝ 1 (prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) t σs) :=
      contDiff_prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) (t := t) σs
    have hG : ContDiff ℝ 1 (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ)) :=
      contDiff_gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ)
    have hDiff :
        ContDiff ℝ 1 (fun x : DisorderSpace (N := N) =>
          ((n : ℝ) * gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x)
            - ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ)) := by
      simpa using (contDiff_const.mul hG).sub contDiff_const
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (contDiff_const.mul (hP.mul hDiff))
  exact hsum

lemma measurable_A_disorder_explicit (t : ℝ) (f : ReplicaFun N n) (τ : Config N) :
    Measurable (A_disorder_explicit (N := N) (n := n) (h := h) t f τ) :=
  (contDiff_A_disorder_explicit (N := N) (n := n) (h := h) (t := t) (f := f) (τ :=
    τ)).continuous.measurable

lemma abs_prod_gibbs_pmf_disorder_le_one (t : ℝ) (σs : ReplicaSpace N n) (x : DisorderSpace (N :=
    N)) :
    |prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) (t := t) σs x| ≤ 1 := by
  classical
  -- Reduce to the model-agnostic finite-volume bounds for Gibbs weights.
  let H : EnergySpace N := H_t_disorder N (H_field N h) t x
  have hnonneg :
      0 ≤ ∏ l : Fin n, FiniteGibbs.gibbs_pmf (α := Config N) H (σs l) :=
    FiniteGibbs.prod_gibbs_pmf_nonneg (α := Config N) (n := n) (H := H) σs
  have hle1 :
      (∏ l : Fin n, FiniteGibbs.gibbs_pmf (α := Config N) H (σs l)) ≤ (1 : ℝ) :=
    FiniteGibbs.prod_gibbs_pmf_le_one (α := Config N) (n := n) (H := H) σs
  simpa [prod_gibbs_pmf_disorder, gibbs_pmf_disorder, gibbs_pmf_eq_FiniteGibbs_gibbs_pmf, H,
    abs_of_nonneg hnonneg] using hle1

lemma abs_n_mul_gibbs_pmf_sub_card_le (t : ℝ) (τ : Config N) (σs : ReplicaSpace N n)
    (x : DisorderSpace (N := N)) :
    |(n : ℝ) * (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x)
        - ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ)|
      ≤ (2 * (n : ℝ)) := by
  simpa [gibbs_pmf_disorder, gibbs_pmf_eq_FiniteGibbs_gibbs_pmf] using
    (FiniteGibbs.abs_n_mul_gibbs_pmf_sub_card_le (α := Config N) (n := n)
      (H := H_t_disorder N (H_field N h) t x) (τ := τ) (σs := σs))

lemma abs_A_disorder_explicit_le (t : ℝ) (f : ReplicaFun N n) (τ : Config N)
    (x : DisorderSpace (N := N)) :
    |A_disorder_explicit (N := N) (n := n) (h := h) t f τ x|
      ≤ (2 * (n : ℝ)) * (∑ σs : ReplicaSpace N n, |f σs|) := by
  classical
  let H : EnergySpace N := H_t_disorder N (H_field N h) t x
  simpa [A_disorder_explicit, prod_gibbs_pmf_disorder, gibbs_pmf_disorder,
    gibbs_pmf_eq_FiniteGibbs_gibbs_pmf, H] using
    (FiniteGibbs.abs_sum_mul_prod_gibbs_pmf_mul_n_mul_sub_card_le (α := Config N)
      (n := n) (H := H) (f := f) (τ := τ))

lemma norm_fderiv_A_disorder_explicit_le (t : ℝ) (f : ReplicaFun N n) (τ : Config N)
    (x : DisorderSpace (N := N)) :
    ‖fderiv ℝ (A_disorder_explicit (N := N) (n := n) (h := h) t f τ) x‖
      ≤ ((2 * (n : ℝ) * (n : ℝ) + (n : ℝ)) *
            (2 * (|Real.sqrt t| + |Real.sqrt (1 - t)|))) *
          (∑ σs : ReplicaSpace N n, |f σs|) := by
  classical
  let μC : ℝ := 2 * (|Real.sqrt t| + |Real.sqrt (1 - t)|)
  have hμC : 0 ≤ μC := by
    have : (0 : ℝ) ≤ |Real.sqrt t| + |Real.sqrt (1 - t)| := by positivity
    nlinarith [this]
  have hfderivG :
      ‖fderiv ℝ (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ)) x‖ ≤ μC := by
    exact norm_fderiv_gibbs_pmf_disorder_le (N := N) (h := h) (t := t) (σ := τ) x
  have hsum :
      fderiv ℝ (A_disorder_explicit (N := N) (n := n) (h := h) t f τ) x
        =
        ∑ σs : ReplicaSpace N n,
          fderiv ℝ (fun x : DisorderSpace (N := N) =>
            f σs *
              (prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) (t := t) σs x) *
              ((n : ℝ) * (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x)
                - ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ))) x := by
    have hdiff :
        ∀ σs : ReplicaSpace N n,
          DifferentiableAt ℝ (fun x : DisorderSpace (N := N) =>
            f σs *
              (prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) (t := t) σs x) *
              ((n : ℝ) * (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x)
                - ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ))) x := by
      intro σs
      have hC1 :
          ContDiff ℝ 1 (fun x : DisorderSpace (N := N) =>
            f σs *
              (prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) (t := t) σs x) *
              ((n : ℝ) * (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x)
                - ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ))) := by
        have hP : ContDiff ℝ 1 (prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) t σs) :=
          contDiff_prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) (t := t) σs
        have hG : ContDiff ℝ 1 (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ)) :=
          contDiff_gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ)
        have hDiff :
            ContDiff ℝ 1 (fun x : DisorderSpace (N := N) =>
              ((n : ℝ) * gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x)
                - ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ)) := by
          simpa using (contDiff_const.mul hG).sub contDiff_const
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          (contDiff_const.mul (hP.mul hDiff))
      -- `ContDiff 1` implies differentiable.
      exact ((hC1.differentiable (by norm_num)) x)
    -- Use `fderiv_fun_sum` on `Finset.univ`.
    exact
      (fderiv_fun_sum (𝕜 := ℝ) (u := (Finset.univ : Finset (ReplicaSpace N n)))
        (A := fun σs : ReplicaSpace N n => fun x : DisorderSpace (N := N) =>
          f σs *
            (prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) (t := t) σs x) *
            ((n : ℝ) * (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x)
              - ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ)))
        (x := x)
        (h := fun σs _hσs => hdiff σs))
  -- Now bound the norm by the sum of the norms.
  rw [hsum]
  refine le_trans (norm_sum_le (s := (Finset.univ : Finset (ReplicaSpace N n)))
      (f := fun σs : ReplicaSpace N n =>
        fderiv ℝ (fun x : DisorderSpace (N := N) =>
          f σs *
            (prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) (t := t) σs x) *
            ((n : ℝ) * (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x)
              - ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ))) x)) ?_
  -- Bound each summand uniformly, then sum.
  have hsum_bound :
      ∀ σs : ReplicaSpace N n,
        ‖fderiv ℝ (fun x : DisorderSpace (N := N) =>
            f σs *
              (prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) (t := t) σs x) *
              ((n : ℝ) * (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x)
                - ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ))) x‖
          ≤ |f σs| * ((2 * (n : ℝ) * (n : ℝ) + (n : ℝ)) * μC) := by
    intro σs
    -- Let `P x := prod_gibbs_pmf_disorder ... σs x`, `D x := (n) * G x - card`.
    let P : DisorderSpace (N := N) → ℝ :=
      prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) (t := t) σs
    let D : DisorderSpace (N := N) → ℝ :=
      fun x =>
        (n : ℝ) * gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x
          - ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ)
    have hP_abs : |P x| ≤ 1 := by
      simpa [P] using abs_prod_gibbs_pmf_disorder_le_one (N := N) (n := n) (h := h) (t := t) σs x
    have hD_abs : |D x| ≤ 2 * (n : ℝ) := by
      simpa [D] using
        (abs_n_mul_gibbs_pmf_sub_card_le (N := N) (n := n) (h := h) (t := t) (τ := τ) σs x)
    have hP_der : ‖fderiv ℝ P x‖ ≤ (n : ℝ) * μC := by
      -- This is `norm_fderiv_prod_gibbs_pmf_disorder_le`.
      simpa [P, μC, mul_assoc, mul_left_comm, mul_comm] using
        (norm_fderiv_prod_gibbs_pmf_disorder_le (N := N) (n := n) (h := h) (t := t) σs x)
    have hD_der : ‖fderiv ℝ D x‖ ≤ (n : ℝ) * μC := by
      -- `D = (n) * G - const`, so `‖Df‖ ≤ n * ‖DG‖`.
      have hDG : ‖fderiv ℝ (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ)) x‖ ≤ μC :=
        hfderivG
      -- `fderiv` of `x ↦ (n : ℝ) * G x` is `n • fderiv G x`.
      have hdiffG :
          DifferentiableAt ℝ (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ)) x := by
        -- `ContDiff 1` implies differentiable
        exact ((contDiff_gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ)).differentiable (by
          norm_num)) x
      have hfderivMul :
          fderiv ℝ (fun x : DisorderSpace (N := N) => (n : ℝ) * gibbs_pmf_disorder (N := N) (h := h)
            (t := t) (σ := τ) x) x
            = (n : ℝ) • fderiv ℝ (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ)) x := by
        simpa using (fderiv_const_mul (𝕜 := ℝ) (a := gibbs_pmf_disorder (N := N) (h := h) (t := t)
          (σ := τ)) hdiffG (b := (n : ℝ)))
      -- subtracting a constant doesn't change the derivative
      -- (the constant derivative is `0`).
      have : ‖fderiv ℝ D x‖ ≤ (n : ℝ) * μC := by
        -- rewrite `fderiv D`
        -- `fderiv (fun x => A x - const) = fderiv A`
        -- and then bound using `hDG`.
        have hsub :
            fderiv ℝ D x
              = fderiv ℝ (fun x : DisorderSpace (N := N) =>
                  (n : ℝ) * gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x) x := by
          -- Use `fderiv_sub_const`.
          simpa [D] using
            (fderiv_sub_const (𝕜 := ℝ)
              (f := fun x : DisorderSpace (N := N) =>
                (n : ℝ) * gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x)
              (x := x)
              (c := ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ)))
        rw [hsub, hfderivMul]
        -- Now bound the operator norm.
        have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
        -- `‖c • L‖ = |c| * ‖L‖` and `|n| = n`.
        simpa [Real.norm_eq_abs, abs_of_nonneg hn0, norm_smul, μC, mul_assoc] using
          (mul_le_mul_of_nonneg_left hDG hn0)
      exact this
    -- Now estimate `‖fderiv (P*D)‖`.
    have hPdiff : DifferentiableAt ℝ P x := by
      exact ((contDiff_prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) (t := t)
        σs).differentiable
        (by norm_num)) x
    have hDdiff : DifferentiableAt ℝ D x := by
      -- `D` is a combination of differentiable functions.
      have hGdiff :
          DifferentiableAt ℝ (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ)) x := by
        exact ((contDiff_gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ)).differentiable
          (by norm_num)) x
      have hmul :
          DifferentiableAt ℝ (fun x : DisorderSpace (N := N) =>
              (n : ℝ) * gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x) x :=
        hGdiff.const_mul (n : ℝ)
      have hconst :
          DifferentiableAt ℝ (fun _ : DisorderSpace (N := N) =>
              ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ)) x :=
        by simp
      simpa [D] using hmul.sub hconst
    have hPDdiff : DifferentiableAt ℝ (fun x : DisorderSpace (N := N) => P x * D x) x :=
      hPdiff.mul hDdiff
    have hfderivPD :
        fderiv ℝ (fun x : DisorderSpace (N := N) => P x * D x) x
          = (P x) • fderiv ℝ D x + (D x) • fderiv ℝ P x := by
      simpa [P, D] using (fderiv_fun_mul (𝕜 := ℝ) (c := P) (d := D) (hc := hPdiff) (hd := hDdiff))
    -- Bound the norm of `fderiv (P*D)` using the product rule.
    have hPD_norm :
        ‖fderiv ℝ (fun x : DisorderSpace (N := N) => P x * D x) x‖
          ≤ ((2 * (n : ℝ) * (n : ℝ) + (n : ℝ)) * μC) := by
      -- `‖a • L + b • M‖ ≤ |a|*‖L‖ + |b|*‖M‖`
      rw [hfderivPD]
      have h1 : ‖(P x) • fderiv ℝ D x‖ ≤ 1 * ((n : ℝ) * μC) := by
        have : ‖(P x) • fderiv ℝ D x‖ = |P x| * ‖fderiv ℝ D x‖ := by
          simp [norm_smul]
        rw [this]
        calc
          |P x| * ‖fderiv ℝ D x‖ ≤ 1 * ‖fderiv ℝ D x‖ := by
              exact mul_le_mul_of_nonneg_right hP_abs (norm_nonneg _)
          _ = ‖fderiv ℝ D x‖ := by ring
          _ ≤ (n : ℝ) * μC := hD_der
          _ = 1 * ((n : ℝ) * μC) := by ring
      have h2 : ‖(D x) • fderiv ℝ P x‖ ≤ (2 * (n : ℝ)) * ((n : ℝ) * μC) := by
        have : ‖(D x) • fderiv ℝ P x‖ = |D x| * ‖fderiv ℝ P x‖ := by
          simp [norm_smul]
        rw [this]
        calc
          |D x| * ‖fderiv ℝ P x‖ ≤ (2 * (n : ℝ)) * ‖fderiv ℝ P x‖ := by
              exact mul_le_mul_of_nonneg_right hD_abs (norm_nonneg _)
          _ ≤ (2 * (n : ℝ)) * ((n : ℝ) * μC) := by
              exact mul_le_mul_of_nonneg_left hP_der (by positivity)
      -- Combine via triangle inequality and simplify constants.
      have htri : ‖(P x) • fderiv ℝ D x + (D x) • fderiv ℝ P x‖
          ≤ 1 * ((n : ℝ) * μC) + (2 * (n : ℝ)) * ((n : ℝ) * μC) := by
        exact (norm_add_le _ _).trans (add_le_add h1 h2)
      have htri' :
          ‖(P x) • fderiv ℝ D x + (D x) • fderiv ℝ P x‖
            ≤ (n : ℝ) * μC + (2 * (n : ℝ)) * ((n : ℝ) * μC) := by
        simpa [mul_assoc] using htri
      have hR' :
          (n : ℝ) * μC + (2 * (n : ℝ)) * ((n : ℝ) * μC)
            = ((2 * (n : ℝ) * (n : ℝ) + (n : ℝ)) * μC) := by ring
      simpa [hR'] using htri'
    -- Finally scale by the constant `f σs`.
    have hdiffPD :
        DifferentiableAt ℝ (fun x : DisorderSpace (N := N) => P x * D x) x := hPDdiff
    have hfderivConst :
        fderiv ℝ (fun x : DisorderSpace (N := N) => (f σs) * (P x * D x)) x
          = (f σs) • fderiv ℝ (fun x : DisorderSpace (N := N) => P x * D x) x := by
      simpa using (fderiv_const_mul (𝕜 := ℝ) (a := fun x : DisorderSpace (N := N) => P x * D x)
        hdiffPD (b := f σs))
    -- Use `‖c • L‖ = |c| * ‖L‖`.
    have hn : ‖fderiv ℝ (fun x : DisorderSpace (N := N) =>
          (f σs) * (P x * D x)) x‖
          ≤ |f σs| * ((2 * (n : ℝ) * (n : ℝ) + (n : ℝ)) * μC) := by
      rw [hfderivConst]
      -- `‖c • L‖ = |c| * ‖L‖`, then use `hPD_norm`.
      have : |f σs| * ‖fderiv ℝ (fun x : DisorderSpace (N := N) => P x * D x) x‖
          ≤ |f σs| * ((2 * (n : ℝ) * (n : ℝ) + (n : ℝ)) * μC) := by
        exact mul_le_mul_of_nonneg_left hPD_norm (abs_nonneg _)
      simpa [norm_smul] using this
    simpa [P, D, mul_assoc, mul_left_comm, mul_comm] using hn
  have :
      (∑ σs : ReplicaSpace N n,
        ‖fderiv ℝ (fun x : DisorderSpace (N := N) =>
            f σs *
              (prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) (t := t) σs x) *
              ((n : ℝ) * (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x)
                - ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ))) x‖)
        ≤ ((2 * (n : ℝ) * (n : ℝ) + (n : ℝ)) * μC) *
            (∑ σs : ReplicaSpace N n, |f σs|) := by
    calc
      (∑ σs : ReplicaSpace N n,
          ‖fderiv ℝ (fun x : DisorderSpace (N := N) =>
              f σs *
                (prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) (t := t) σs x) *
                ((n : ℝ) * (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x)
                  - ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ))) x‖)
          ≤ ∑ σs : ReplicaSpace N n,
              |f σs| * ((2 * (n : ℝ) * (n : ℝ) + (n : ℝ)) * μC) := by
              refine Finset.sum_le_sum (fun σs _ => hsum_bound σs)
      _ = ((2 * (n : ℝ) * (n : ℝ) + (n : ℝ)) * μC) * (∑ σs : ReplicaSpace N n, |f σs|) := by
              simp [Finset.mul_sum, mul_comm]
  -- Put everything together and rewrite `μC`.
  have hpow : (1 + ‖x‖) ^ (0 : ℕ) = (1 : ℝ) := by simp
  -- finish
  nlinarith [this]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
theorem
    integral_disorderPairLaw_left_apply_mul_A_disorder_explicit_eq
    (hindep : G₁.U ⟂ᵢ[(ℙ : Measure Ω)] G₂.U) (t : ℝ) (f : ReplicaFun N n) (σ τ : Config N) :
    (∫ x : DisorderSpace (N := N),
        ((WithLp.ofLp x).1 σ) *
          (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x)
        ∂(disorderPairLaw (Ω := Ω) (N := N) (G₁ := G₁) (G₂ := G₂)))
      =
      ∫ x : DisorderSpace (N := N),
        (fderiv ℝ (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ) x)
          (ProbabilityTheory.covarianceOperator
            (disorderPairLaw (Ω := Ω) (N := N) (G₁ := G₁) (G₂ := G₂))
            (std_basis_left (N := N) σ))
        ∂(disorderPairLaw (Ω := Ω) (N := N) (G₁ := G₁) (G₂ := G₂)) :=
          by
  classical
  -- Regularity and growth hypotheses for IBP.
  have hF_c1 :
      ContDiff ℝ 1 (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ) :=
    contDiff_A_disorder_explicit (N := N) (n := n) (h := h) (t := t) (f := f) (τ := τ)
  have hF_meas :
      Measurable (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ) :=
    measurable_A_disorder_explicit (N := N) (n := n) (h := h) (t := t) (f := f) (τ := τ)
  let Sf : ℝ := ∑ σs : ReplicaSpace N n, |f σs|
  let μC : ℝ := 2 * (|Real.sqrt t| + |Real.sqrt (1 - t)|)
  let Cfun : ℝ := (2 * (n : ℝ)) * Sf
  let Cder : ℝ := ((2 * (n : ℝ) * (n : ℝ) + (n : ℝ)) * μC) * Sf
  let C : ℝ := max Cfun Cder
  have hC : 0 ≤ C := by
    have hSf : 0 ≤ Sf :=
      Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    have hn0 : 0 ≤ (2 * (n : ℝ)) := by positivity
    have hμC : 0 ≤ μC := by
      have : (0 : ℝ) ≤ |Real.sqrt t| + |Real.sqrt (1 - t)| := by positivity
      nlinarith [this]
    have hCfun : 0 ≤ Cfun := mul_nonneg hn0 hSf
    have hcoeff : 0 ≤ (2 * (n : ℝ) * (n : ℝ) + (n : ℝ)) := by positivity
    have hCder : 0 ≤ Cder := by
      have : 0 ≤ ((2 * (n : ℝ) * (n : ℝ) + (n : ℝ)) * μC) * Sf :=
        mul_nonneg (mul_nonneg hcoeff hμC) hSf
      simpa [Cder, mul_assoc, mul_left_comm, mul_comm] using this
    exact le_trans hCfun (le_max_left _ _)
  have hF_growth :
      ∀ x, |A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x|
        ≤ C * (1 + ‖x‖) ^ (0 : ℕ) := by
    intro x
    have h1 :
        |A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x| ≤ Cfun := by
      simpa [Cfun, Sf] using (abs_A_disorder_explicit_le (N := N) (n := n) (h := h) (t := t) (f :=
        f) (τ := τ) x)
    have hCfun : Cfun ≤ C := le_max_left _ _
    have : |A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x| ≤ C := le_trans h1 hCfun
    simpa [pow_zero] using this
  have hF'_growth :
      ∀ x, ‖fderiv ℝ (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ) x‖
        ≤ C * (1 + ‖x‖) ^ (0 : ℕ) := by
    intro x
    have h1 :
        ‖fderiv ℝ (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ) x‖ ≤ Cder := by
      simpa [Cder, Sf, μC] using
        (norm_fderiv_A_disorder_explicit_le (N := N) (n := n) (h := h) (t := t) (f := f) (τ := τ) x)
    have hCder : Cder ≤ C := le_max_right _ _
    have : ‖fderiv ℝ (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ) x‖ ≤ C :=
      le_trans h1 hCder
    simpa [pow_zero] using this
  -- Apply the generic packaged IBP lemma.
  simpa using
    (integral_disorderPairLaw_left_apply_mul_eq
      (Ω := Ω) (N := N) (G₁ := G₁) (G₂ := G₂)
      (hindep := hindep) (σ := σ) (F := A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ)
      hF_meas hF_c1 hC hF_growth hF'_growth)

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
theorem
    integral_disorderPairLaw_right_apply_mul_A_disorder_explicit_eq
    (hindep : G₁.U ⟂ᵢ[(ℙ : Measure Ω)] G₂.U) (t : ℝ) (f : ReplicaFun N n) (σ τ : Config N) :
    (∫ x : DisorderSpace (N := N),
        ((WithLp.ofLp x).2 σ) *
          (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x)
        ∂(disorderPairLaw (Ω := Ω) (N := N) (G₁ := G₁) (G₂ := G₂)))
      =
      ∫ x : DisorderSpace (N := N),
        (fderiv ℝ (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ) x)
          (ProbabilityTheory.covarianceOperator
            (disorderPairLaw (Ω := Ω) (N := N) (G₁ := G₁) (G₂ := G₂))
            (std_basis_right (N := N) σ))
        ∂(disorderPairLaw (Ω := Ω) (N := N) (G₁ := G₁) (G₂ := G₂)) :=
          by
  classical
  -- Reuse the left lemma with the right-hand packaged IBP.
  have hF_c1 :
      ContDiff ℝ 1 (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ) :=
    contDiff_A_disorder_explicit (N := N) (n := n) (h := h) (t := t) (f := f) (τ := τ)
  have hF_meas :
      Measurable (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ) :=
    measurable_A_disorder_explicit (N := N) (n := n) (h := h) (t := t) (f := f) (τ := τ)
  let Sf : ℝ := ∑ σs : ReplicaSpace N n, |f σs|
  let μC : ℝ := 2 * (|Real.sqrt t| + |Real.sqrt (1 - t)|)
  let Cfun : ℝ := (2 * (n : ℝ)) * Sf
  let Cder : ℝ := ((2 * (n : ℝ) * (n : ℝ) + (n : ℝ)) * μC) * Sf
  let C : ℝ := max Cfun Cder
  have hC : 0 ≤ C := by
    have hSf : 0 ≤ Sf :=
      Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    have hn0 : 0 ≤ (2 * (n : ℝ)) := by positivity
    have hμC : 0 ≤ μC := by
      have : (0 : ℝ) ≤ |Real.sqrt t| + |Real.sqrt (1 - t)| := by positivity
      nlinarith [this]
    have hCfun : 0 ≤ Cfun := mul_nonneg hn0 hSf
    have hcoeff : 0 ≤ (2 * (n : ℝ) * (n : ℝ) + (n : ℝ)) := by positivity
    have hCder : 0 ≤ Cder := by
      have : 0 ≤ ((2 * (n : ℝ) * (n : ℝ) + (n : ℝ)) * μC) * Sf :=
        mul_nonneg (mul_nonneg hcoeff hμC) hSf
      simpa [Cder, mul_assoc, mul_left_comm, mul_comm] using this
    exact le_trans hCfun (le_max_left _ _)
  have hF_growth :
      ∀ x, |A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x|
        ≤ C * (1 + ‖x‖) ^ (0 : ℕ) := by
    intro x
    have h1 :
        |A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x| ≤ Cfun := by
      simpa [Cfun, Sf] using (abs_A_disorder_explicit_le (N := N) (n := n) (h := h) (t := t) (f :=
        f) (τ := τ) x)
    have hCfun : Cfun ≤ C := le_max_left _ _
    have : |A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x| ≤ C := le_trans h1 hCfun
    simpa [pow_zero] using this
  have hF'_growth :
      ∀ x, ‖fderiv ℝ (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ) x‖
        ≤ C * (1 + ‖x‖) ^ (0 : ℕ) := by
    intro x
    have h1 :
        ‖fderiv ℝ (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ) x‖ ≤ Cder := by
      simpa [Cder, Sf, μC] using
        (norm_fderiv_A_disorder_explicit_le (N := N) (n := n) (h := h) (t := t) (f := f) (τ := τ) x)
    have hCder : Cder ≤ C := le_max_right _ _
    have : ‖fderiv ℝ (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ) x‖ ≤ C :=
      le_trans h1 hCder
    simpa [pow_zero] using this
  simpa using
    (integral_disorderPairLaw_right_apply_mul_eq
      (Ω := Ω) (N := N) (G₁ := G₁) (G₂ := G₂)
      (hindep := hindep) (σ := σ) (F := A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ)
      hF_meas hF_c1 hC hF_growth hF'_growth)

lemma A_disorder_eq_explicit (t : ℝ) (f : ReplicaFun N n) (τ : Config N) (x : DisorderSpace (N :=
    N)) :
    A_disorder (N := N) (n := n) (h := h) t f τ x
      =
      A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x := by
  classical
  have hcard :
      ∀ σs : ReplicaSpace N n,
        ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ)
          = ((Finset.univ.filter fun l : Fin n => τ = σs l).card : ℝ) := by
    intro σs
    classical
    simp [eq_comm]
  have hcount (σs : ReplicaSpace N n) :
      (∑ l : Fin n, (if τ = σs l then (1 : ℝ) else 0))
        = ((Finset.univ.filter fun l : Fin n => τ = σs l).card : ℝ) := by
    classical
    have hNat :
        (Finset.univ.filter (fun l : Fin n => τ = σs l)).card
          = ∑ l ∈ (Finset.univ : Finset (Fin n)), ite (τ = σs l) 1 0 := by
      simp
    have hCast :
        ((Finset.univ.filter (fun l : Fin n => τ = σs l)).card : ℝ)
          = ∑ l ∈ (Finset.univ : Finset (Fin n)), (if τ = σs l then (1 : ℝ) else 0) := by
      -- Cast the `Nat` identity and simplify the resulting sum.
      have := congrArg (fun m : Nat => (m : ℝ)) hNat
      simp
    simp
  -- Unfold `A_disorder` via the generic derivative formula, then rewrite the counting term using
  -- `hcount`.
  simp only [A_disorder, gibbs_average_n_det, std_basis, FiniteGibbs.std_basis,
    FiniteGibbs.fderiv_gibbs_average_n_det_apply, mul_comm, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, A_disorder_explicit,
    prod_gibbs_pmf_disorder, gibbs_pmf_disorder, gibbs_pmf_eq_FiniteGibbs_gibbs_pmf, hcard]
  apply Fintype.sum_congr
  intro σs
  -- The summands differ only by rewriting the counting term.
  rw [← hcount σs]
  -- The remaining mismatch is only the choice of `Decidable` instance in the `if`.
  have hite (x : Fin n) :
      @ite ℝ (τ = σs x) (Classical.propDecidable (τ = σs x)) 1 0
        = @ite ℝ (τ = σs x) (Fintype.decidablePiFintype τ (σs x)) 1 0 := by
    by_cases hx : τ = σs x <;> simp [hx]
  have hsum :
      (∑ x : Fin n, @ite ℝ (τ = σs x) (Classical.propDecidable (τ = σs x)) 1 0)
        =
        ∑ x : Fin n, @ite ℝ (τ = σs x) (Fintype.decidablePiFintype τ (σs x)) 1 0 := by
    refine Fintype.sum_congr _ _ (fun x => hite x)
  rw [← hsum]



lemma dgibbs_average_n_disorder_eq_sum_A (t : ℝ) (f : ReplicaFun N n) (x : DisorderSpace (N := N)) :
    dgibbs_average_n_disorder (N := N) (n := n) (h := h) t f x
      =
      ∑ τ : Config N, (gaussianInterpDeriv (E := EnergySpace N) t x) τ *
        A_disorder (N := N) (n := n) (h := h) (t := t) (f := f) (τ := τ) x := by
  classical
  -- Let `G` be the replica functional. Then `dgibbs_average_n_disorder` is the linear map
  -- `T := fderiv G` applied to the direction `v := gaussianInterpDeriv`.
  let G : EnergySpace N → ℝ := fun H' => gibbs_average_n_det (N := N) (n := n) H' f
  let H : EnergySpace N := H_t_disorder N (H_field N h) t x
  let v : EnergySpace N := gaussianInterpDeriv (E := EnergySpace N) t x
  let T : EnergySpace N →L[ℝ] ℝ := fderiv ℝ G H
  have hv : v = ∑ τ : Config N, (v τ) • std_basis N τ := by
    classical
    ext σ
    simp [std_basis, FiniteGibbs.std_basis]
  -- Start from the definition, then expand `v` in the `std_basis` and use linearity.
  have hdg : dgibbs_average_n_disorder (N := N) (n := n) (h := h) t f x = T v := by
    simp [dgibbs_average_n_disorder, G, H, v, T]
  rw [hdg, hv]
  -- Push `T` through the (finite) sum.
  have hmap :
      T (∑ τ : Config N, (v τ) • std_basis N τ)
        =
      ∑ τ : Config N, T ((v τ) • std_basis N τ) := by
    classical
    -- `∑ τ : Config N` is definitionaly `Finset.univ.sum`.
    simp
  -- Now rewrite each summand using linearity and unfold `A_disorder`.
  classical
  simp [hmap, A_disorder, G, H, v, T, smul_eq_mul]

lemma dgibbs_average_n_disorder_eq_sum_left_right (t : ℝ) (f : ReplicaFun N n)
    (x : DisorderSpace (N := N)) :
    dgibbs_average_n_disorder (N := N) (n := n) (h := h) t f x
      =
      (1 / (2 * Real.sqrt t)) *
          ∑ τ : Config N, ((WithLp.ofLp x).1 τ) *
            A_disorder (N := N) (n := n) (h := h) (t := t) (f := f) (τ := τ) x
        -
        (1 / (2 * Real.sqrt (1 - t))) *
          ∑ τ : Config N, ((WithLp.ofLp x).2 τ) *
            A_disorder (N := N) (n := n) (h := h) (t := t) (f := f) (τ := τ) x := by
  classical
  rw [dgibbs_average_n_disorder_eq_sum_A (N := N) (n := n) (h := h) (t := t) (f := f) x]
  classical
  simp [gaussianInterpDeriv, smul_eq_mul, sub_eq_add_neg, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm, mul_add]

lemma dgibbs_average_n_disorder_eq_sum_left_right_explicit (t : ℝ) (f : ReplicaFun N n)
    (x : DisorderSpace (N := N)) :
    dgibbs_average_n_disorder (N := N) (n := n) (h := h) t f x
      =
      (1 / (2 * Real.sqrt t)) *
          ∑ τ : Config N, ((WithLp.ofLp x).1 τ) *
            A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x
        -
        (1 / (2 * Real.sqrt (1 - t))) *
          ∑ τ : Config N, ((WithLp.ofLp x).2 τ) *
            A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x := by
  classical
  -- Just rewrite `A_disorder` by its explicit formula in
  -- `dgibbs_average_n_disorder_eq_sum_left_right`.
  simpa [A_disorder_eq_explicit] using
    (dgibbs_average_n_disorder_eq_sum_left_right (N := N) (n := n) (h := h) (t := t) (f := f) x)

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
@[simp] lemma gibbs_average_n_disorder_disorderPair (t : ℝ) (f : ReplicaFun N n) (w : Ω) :
    gibbs_average_n_disorder (N := N) (n := n) (h := h) t f
        (disorderPair (N := N) (G₁ := G₁) (G₂ := G₂) w)
      =
      gibbs_average_n (N := N) (h := h) (G₁ := G₁) (G₂ := G₂) n t f w := by
  simp [gibbs_average_n_disorder, gibbs_average_n, H_t_disorder_disorderPair]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
@[simp] lemma dgibbs_average_n_disorder_disorderPair (t : ℝ) (f : ReplicaFun N n) (w : Ω) :
    dgibbs_average_n_disorder (N := N) (n := n) (h := h) t f
        (disorderPair (N := N) (G₁ := G₁) (G₂ := G₂) w)
      =
      dgibbs_average_n (N := N) (h := h) (G₁ := G₁) (G₂ := G₂) n t f w := by
  simp [dgibbs_average_n_disorder, dgibbs_average_n, H_t_disorder_disorderPair,
    gaussianInterpDeriv_disorderPair]
end ReplicaCalculus

end SpinGlass
