import SpinGlass.Hopfield
import SpinGlass.LogCosh
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Hopfield `ψ`: Fréchet derivatives

Explicit Fréchet derivative of `hopfieldPsi`. Calculus for localization (critical points,
quadratic expansions). Talagrand Vol. I, §4.3.
-/

open MeasureTheory ProbabilityTheory Real BigOperators

namespace SpinGlass

variable {N M : ℕ}

/-! ### One-dimensional calculus: `d/dx log(cosh x) = tanh x` -/

lemma hasDerivAt_log_cosh (x : ℝ) :
    HasDerivAt (fun t : ℝ => Real.log (Real.cosh t)) (Real.tanh x) x := by
  have hcosh : HasDerivAt Real.cosh (Real.sinh x) x := Real.hasDerivAt_cosh x
  have hlog : HasDerivAt Real.log (Real.cosh x)⁻¹ (Real.cosh x) :=
    Real.hasDerivAt_log (ne_of_gt (Real.cosh_pos x))
  have hcomp :
      HasDerivAt (fun t : ℝ => Real.log (Real.cosh t)) ((Real.cosh x)⁻¹ * Real.sinh x) x := by
    simpa [Function.comp] using hlog.comp x hcosh
  simpa [Real.tanh_eq_sinh_div_cosh, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hcomp

lemma hasDerivAt_tanh (x : ℝ) :
    HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x := by
  have hx : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  have hdiv :
      HasDerivAt (fun t : ℝ => Real.sinh t / Real.cosh t)
        ((Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / Real.cosh x ^ 2) x := by
    simpa using (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hx
  have hfun : (fun t : ℝ => Real.sinh t / Real.cosh t) = Real.tanh := by
    funext t
    simp [Real.tanh_eq_sinh_div_cosh]
  have htanh :
      HasDerivAt Real.tanh
        ((Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / Real.cosh x ^ 2) x := by
    simpa [hfun] using hdiv
  refine htanh.congr_deriv ?_
  -- simplify the quotient-rule expression to `1 - tanh x ^ 2`
  have : ((Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / Real.cosh x ^ 2 : ℝ)
      = (1 - Real.tanh x ^ 2) := by
    -- rewrite `tanh` as `sinh/cosh`, then clear denominators
    simp [Real.tanh_eq_sinh_div_cosh, pow_two]
    field_simp [hx]
  simpa using this

/-! ### Basic inequalities: `log(cosh x) ≤ |x|` -/

lemma cosh_le_exp_abs (x : ℝ) :
    Real.cosh x ≤ Real.exp |x| := by
  have hx : Real.exp x ≤ Real.exp |x| := by
    exact Real.exp_le_exp.2 (le_abs_self x)
  have hnx : Real.exp (-x) ≤ Real.exp |x| := by
    exact Real.exp_le_exp.2 (neg_le_abs x)
  have h2 : 0 ≤ (2 : ℝ) := by norm_num
  calc
    Real.cosh x = (Real.exp x + Real.exp (-x)) / 2 := by simpa using (Real.cosh_eq x)
    _ ≤ (Real.exp |x| + Real.exp |x|) / 2 := by
          exact div_le_div_of_nonneg_right (add_le_add hx hnx) h2
    _ = Real.exp |x| := by
          simp

lemma log_cosh_le_abs (x : ℝ) :
    Real.log (Real.cosh x) ≤ |x| := by
  have hx : 0 < Real.cosh x := Real.cosh_pos x
  exact (Real.log_le_iff_le_exp hx).2 (cosh_le_exp_abs x)

/-! ### Linear algebra: `η_i · z` as a continuous linear functional -/

/-- Continuous linear functional `z ↦ η_i · z = ∑_k η_{i,k} z_k`. -/
noncomputable def hopfieldEtaDotCLM (Ξ : Patterns N M) (i : Fin N) : (Fin M → ℝ) →L[ℝ] ℝ :=
  ∑ k : Fin M, (hopfieldEta (N := N) (M := M) Ξ i k) • (ContinuousLinearMap.proj (R := ℝ) k)

lemma hopfieldEtaDotCLM_apply (Ξ : Patterns N M) (i : Fin N) (v : Fin M → ℝ) :
    hopfieldEtaDotCLM (N := N) (M := M) Ξ i v = ∑ k : Fin M, hopfieldEta (N := N) (M := M) Ξ i k * v k := by
  simp [hopfieldEtaDotCLM, ContinuousLinearMap.sum_apply, smul_eq_mul]

@[simp] lemma hopfieldEtaDotCLM_piSingle_one (Ξ : Patterns N M) (i : Fin N) (k : Fin M) :
    hopfieldEtaDotCLM (N := N) (M := M) Ξ i (Pi.single k (1 : ℝ)) = hopfieldEta (N := N) (M := M) Ξ i k := by
  -- evaluate the linear functional on a coordinate basis vector
  simp [hopfieldEtaDotCLM, ContinuousLinearMap.sum_apply, Pi.single_apply, smul_eq_mul]

@[simp] lemma hopfieldEtaDot_eq_hopfieldEtaDotCLM (Ξ : Patterns N M) (i : Fin N) :
    hopfieldEtaDot (N := N) (M := M) Ξ i = hopfieldEtaDotCLM (N := N) (M := M) Ξ i := by
  funext z
  simp [hopfieldEtaDot, hopfieldEtaDotCLM, ContinuousLinearMap.sum_apply, smul_eq_mul]

@[fun_prop] lemma hasFDerivAt_hopfieldEtaDot (Ξ : Patterns N M) (i : Fin N) (z : Fin M → ℝ) :
    HasFDerivAt (hopfieldEtaDot (N := N) (M := M) Ξ i) (hopfieldEtaDotCLM (N := N) (M := M) Ξ i) z := by
  simpa [hopfieldEtaDot_eq_hopfieldEtaDotCLM (N := N) (M := M) (Ξ := Ξ) (i := i)] using
    (hopfieldEtaDotCLM (N := N) (M := M) Ξ i).hasFDerivAt

/-! ### Quadratic term: Fréchet derivative of `finVecNormSq` -/

/-- Candidate Fréchet derivative of `finVecNormSq M` at `z`. -/
noncomputable def finVecNormSqFDeriv (z : Fin M → ℝ) : (Fin M → ℝ) →L[ℝ] ℝ :=
  ∑ k : Fin M, (2 * z k) • (ContinuousLinearMap.proj (R := ℝ) k)

lemma finVecNormSqFDeriv_apply (z v : Fin M → ℝ) :
    finVecNormSqFDeriv (M := M) z v = ∑ k : Fin M, (2 * z k) * v k := by
  simp [finVecNormSqFDeriv, ContinuousLinearMap.sum_apply, smul_eq_mul]

@[simp] lemma finVecNormSqFDeriv_piSingle_one (z : Fin M → ℝ) (k : Fin M) :
    finVecNormSqFDeriv (M := M) z (Pi.single k (1 : ℝ)) = 2 * z k := by
  simp [finVecNormSqFDeriv, ContinuousLinearMap.sum_apply, Pi.single_apply, smul_eq_mul]

@[fun_prop] lemma hasFDerivAt_finVecNormSq (z : Fin M → ℝ) :
    HasFDerivAt (finVecNormSq M) (finVecNormSqFDeriv (M := M) z) z := by
  -- differentiate `∑ k, (z k)^2` termwise
  have hterm :
      ∀ k : Fin M,
        HasFDerivAt (fun z : Fin M → ℝ => (z k) ^ 2)
          ((2 * z k) • (ContinuousLinearMap.proj (R := ℝ) k)) z := by
    intro k
    have happly :
        HasFDerivAt (fun z : Fin M → ℝ => z k) (ContinuousLinearMap.proj (R := ℝ) k) z := by
      simpa using (hasFDerivAt_apply (𝕜 := ℝ) (i := k) (f := z))
    have hsq : HasDerivAt (fun t : ℝ => t ^ 2) ((2 : ℝ) * (z k) ^ (2 - 1)) (z k) :=
      hasDerivAt_pow (n := 2) (x := z k)
    have hcomp :
        HasFDerivAt (fun z : Fin M → ℝ => (z k) ^ 2)
          (((2 : ℝ) * (z k) ^ (2 - 1)) • (ContinuousLinearMap.proj (R := ℝ) k)) z := by
      simpa [Function.comp] using (HasDerivAt.comp_hasFDerivAt (x := z) hsq happly)
    simpa using hcomp
  -- sum over `k : Fin M`
  simpa [finVecNormSq, finVecNormSqFDeriv] using
    (HasFDerivAt.fun_sum (u := (Finset.univ : Finset (Fin M)))
      (A := fun k : Fin M => fun z : Fin M → ℝ => (z k) ^ 2)
      (A' := fun k : Fin M => (2 * z k) • (ContinuousLinearMap.proj (R := ℝ) k))
      (x := z)
      (by intro k _hk; simpa using hterm k))

/-! ### Full Hopfield `ψ`: explicit Fréchet derivative -/

/-- Explicit Fréchet derivative of `hopfieldPsi` at `z`. -/
noncomputable def hopfieldPsiFDeriv (β h : ℝ) (Ξ : Patterns N M) (z : Fin M → ℝ) :
    (Fin M → ℝ) →L[ℝ] ℝ :=
  -(((N : ℝ) * β / 2) • finVecNormSqFDeriv (M := M) z)
    + ∑ i : Fin N,
        (Real.tanh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h) * β)
          • hopfieldEtaDotCLM (N := N) (M := M) Ξ i

lemma hopfieldPsiFDeriv_piSingle_one (β h : ℝ) (Ξ : Patterns N M) (z : Fin M → ℝ) (k : Fin M) :
    hopfieldPsiFDeriv (N := N) (M := M) β h Ξ z (Pi.single k (1 : ℝ))
      =
      -((N : ℝ) * β) * z k
        + ∑ i : Fin N,
            (Real.tanh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h) * β)
              * hopfieldEta (N := N) (M := M) Ξ i k := by
  -- expand the Fréchet derivative and evaluate on a basis vector
  simp [hopfieldPsiFDeriv, finVecNormSqFDeriv_piSingle_one, hopfieldEtaDotCLM_piSingle_one,
    mul_left_comm, mul_comm]
  ring

/-! ### `HasFDerivAt` for the full `ψ` (factored API) -/

lemma hopfieldPsi_eq_neg_mul_finVecNormSq_add_sum (β h : ℝ) (Ξ : Patterns N M) :
    hopfieldPsi (N := N) (M := M) β h Ξ
      =
      (fun z : Fin M → ℝ =>
        -(((N : ℝ) * β / 2) * finVecNormSq M z)
          + ∑ i : Fin N, Real.log (Real.cosh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h))) := by
  funext z
  simp [hopfieldPsi, neg_mul]

@[fun_prop] lemma hasFDerivAt_hopfieldPsi_quadratic (β : ℝ) (z : Fin M → ℝ) :
    HasFDerivAt
      (fun z : Fin M → ℝ => -(((N : ℝ) * β / 2) * finVecNormSq M z))
      (-(((N : ℝ) * β / 2) • finVecNormSqFDeriv (M := M) z)) z := by
  have hnorm : HasFDerivAt (finVecNormSq M) (finVecNormSqFDeriv (M := M) z) z :=
    hasFDerivAt_finVecNormSq (M := M) z
  simpa [smul_eq_mul, mul_assoc] using (hnorm.const_smul ((N : ℝ) * β / 2)).neg

@[fun_prop] lemma hasFDerivAt_hopfieldPsi_logcosh (β h : ℝ) (Ξ : Patterns N M) (i : Fin N)
    (z : Fin M → ℝ) :
    HasFDerivAt
        (fun z : Fin M → ℝ =>
          Real.log (Real.cosh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h)))
        ((Real.tanh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h) * β)
          • hopfieldEtaDotCLM (N := N) (M := M) Ξ i) z := by
  have hη :
      HasFDerivAt (hopfieldEtaDot (N := N) (M := M) Ξ i)
        (hopfieldEtaDotCLM (N := N) (M := M) Ξ i) z :=
    hasFDerivAt_hopfieldEtaDot (N := N) (M := M) Ξ i z
  have hinner :
      HasFDerivAt
        (fun z : Fin M → ℝ => β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h)
        (β • hopfieldEtaDotCLM (N := N) (M := M) Ξ i) z := by
    simpa [smul_eq_mul] using (hη.const_smul β).add_const h
  have houter :
      HasDerivAt (fun t : ℝ => Real.log (Real.cosh t))
        (Real.tanh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h))
        (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h) := by
    simpa using hasDerivAt_log_cosh (x := β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h)
  have hcomp :
      HasFDerivAt
        (fun z : Fin M → ℝ =>
          Real.log (Real.cosh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h)))
        ((Real.tanh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h))
          • (β • hopfieldEtaDotCLM (N := N) (M := M) Ξ i)) z := by
    simpa [Function.comp] using (HasDerivAt.comp_hasFDerivAt (x := z) houter hinner)
  simpa [smul_smul, mul_assoc, mul_left_comm, mul_comm] using hcomp

@[fun_prop] lemma hasFDerivAt_hopfieldPsi_sum_logcosh (β h : ℝ) (Ξ : Patterns N M) (z : Fin M → ℝ) :
    HasFDerivAt
      (fun z : Fin M → ℝ =>
        ∑ i : Fin N, Real.log (Real.cosh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h)))
      (∑ i : Fin N,
        (Real.tanh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h) * β)
          • hopfieldEtaDotCLM (N := N) (M := M) Ξ i) z := by
  simpa using
    (HasFDerivAt.fun_sum (u := (Finset.univ : Finset (Fin N)))
      (A := fun i : Fin N => fun z : Fin M → ℝ =>
        Real.log (Real.cosh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h)))
      (A' := fun i : Fin N =>
        (Real.tanh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h) * β)
          • hopfieldEtaDotCLM (N := N) (M := M) Ξ i)
      (x := z)
      (by
        intro i _hi
        simpa using hasFDerivAt_hopfieldPsi_logcosh (N := N) (M := M) (β := β) (h := h) Ξ i z))

@[fun_prop] lemma hasFDerivAt_hopfieldPsi (β h : ℝ) (Ξ : Patterns N M) (z : Fin M → ℝ) :
    HasFDerivAt (hopfieldPsi (N := N) (M := M) β h Ξ) (hopfieldPsiFDeriv (N := N) (M := M) β h Ξ z) z := by
  simpa [hopfieldPsiFDeriv, hopfieldPsi_eq_neg_mul_finVecNormSq_add_sum (N := N) (M := M) (β := β) (h := h) Ξ] using
    (hasFDerivAt_hopfieldPsi_quadratic (N := N) (M := M) (β := β) z).add
      (hasFDerivAt_hopfieldPsi_sum_logcosh (N := N) (M := M) (β := β) (h := h) Ξ z)

lemma fderiv_hopfieldPsi (β h : ℝ) (Ξ : Patterns N M) (z : Fin M → ℝ) :
    fderiv ℝ (hopfieldPsi (N := N) (M := M) β h Ξ) z = hopfieldPsiFDeriv (N := N) (M := M) β h Ξ z :=
  (hasFDerivAt_hopfieldPsi (N := N) (M := M) (β := β) (h := h) Ξ z).fderiv

lemma differentiable_hopfieldPsi (β h : ℝ) (Ξ : Patterns N M) :
    Differentiable ℝ (hopfieldPsi (N := N) (M := M) β h Ξ) := by
  intro z
  exact (hasFDerivAt_hopfieldPsi (N := N) (M := M) (β := β) (h := h) Ξ z).differentiableAt

/-- If `fderiv hopfieldPsi = 0`, each coordinate satisfies the fixed-point equation. Talagrand Vol. I, §4.3. -/
lemma hopfieldPsi_coord_eq_of_fderiv_eq_zero
    (β h : ℝ) (Ξ : Patterns N M) (z : Fin M → ℝ)
    (hβ : β ≠ 0) (hN : (N : ℝ) ≠ 0)
    (hz : fderiv ℝ (hopfieldPsi (N := N) (M := M) β h Ξ) z = 0) (k : Fin M) :
    z k
      =
      (1 / (N : ℝ)) *
        ∑ i : Fin N,
          (hopfieldEta (N := N) (M := M) Ξ i k)
            * Real.tanh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h) := by
  -- evaluate the derivative on the basis direction `Pi.single k 1`
  have h0 :
      fderiv ℝ (hopfieldPsi (N := N) (M := M) β h Ξ) z (Pi.single k (1 : ℝ)) = 0 := by
    simpa using congrArg (fun L => L (Pi.single k (1 : ℝ))) hz
  -- replace `fderiv` by our explicit formula
  have hder :
      fderiv ℝ (hopfieldPsi (N := N) (M := M) β h Ξ) z (Pi.single k (1 : ℝ))
        =
        -((N : ℝ) * β) * z k
          + ∑ i : Fin N,
              (Real.tanh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h) * β)
                * hopfieldEta (N := N) (M := M) Ξ i k := by
    simpa [fderiv_hopfieldPsi (N := N) (M := M) (β := β) (h := h) (Ξ := Ξ) (z := z)] using
      (hopfieldPsiFDeriv_piSingle_one (N := N) (M := M) (β := β) (h := h) (Ξ := Ξ) (z := z) k)
  -- solve for `z k`: first get the equation `((N*β) * z k) = …`
  have hsum0 :
      -((N : ℝ) * β) * z k
        + ∑ i : Fin N,
            (Real.tanh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h) * β)
              * hopfieldEta (N := N) (M := M) Ξ i k = 0 := by
    simpa [hder] using h0
  have hEq :
      ((N : ℝ) * β) * z k
        =
        ∑ i : Fin N,
          (Real.tanh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h) * β)
            * hopfieldEta (N := N) (M := M) Ξ i k := by
    -- from `(-a) + b = 0`, we get `b = a`
    -- (then flip sides)
    simpa using (eq_neg_of_add_eq_zero_right hsum0).symm
  -- factor out `β` on both sides and cancel it
  have hEq' :
      (N : ℝ) * z k
        =
        ∑ i : Fin N,
          hopfieldEta (N := N) (M := M) Ξ i k
            * Real.tanh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h) := by

    have hR :
        ∑ i : Fin N,
            (Real.tanh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h) * β)
              * hopfieldEta (N := N) (M := M) Ξ i k
          =
          β * ∑ i : Fin N,
              hopfieldEta (N := N) (M := M) Ξ i k
                * Real.tanh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h) := by
      -- move `β` to the outside of the sum, commuting scalars as needed
      simp [Finset.mul_sum, mul_left_comm, mul_comm]
    have hL :
        ((N : ℝ) * β) * z k = β * ((N : ℝ) * z k) := by
      simp [mul_left_comm, mul_comm]
    -- rewrite RHS as `β * Σ (η * tanh)` and cancel on the left
    have hEqβ :
        β * ((N : ℝ) * z k)
          =
          β * ∑ i : Fin N,
              hopfieldEta (N := N) (M := M) Ξ i k
                * Real.tanh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h) := by
      -- rewrite both sides of `hEq` into the factored form
      calc
        β * ((N : ℝ) * z k)
            = ((N : ℝ) * β) * z k := by
                simp [mul_left_comm, mul_comm]
        _ = ∑ i : Fin N,
              (Real.tanh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h) * β)
                * hopfieldEta (N := N) (M := M) Ξ i k := hEq
        _ = β * ∑ i : Fin N,
              hopfieldEta (N := N) (M := M) Ξ i k
                * Real.tanh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h) := hR
    exact mul_left_cancel₀ hβ hEqβ
  -- divide by `N`
  have hEq'' :
      z k
        =
        (1 / (N : ℝ)) *
          ∑ i : Fin N,
            hopfieldEta (N := N) (M := M) Ξ i k
              * Real.tanh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h) := by
    have h' := congrArg (fun t : ℝ => (1 / (N : ℝ)) * t) hEq'
    -- simplify `(1/N) * (N * z_k)` using `hN`
    simpa [one_div, mul_assoc, hN] using h'
  simpa [mul_assoc, mul_left_comm, mul_comm] using hEq''

lemma hopfieldPsi_coord_eq_of_isLocalMax
    (β h : ℝ) (Ξ : Patterns N M) (z : Fin M → ℝ)
    (hβ : β ≠ 0) (hN : (N : ℝ) ≠ 0)
    (hz : IsLocalMax (hopfieldPsi (N := N) (M := M) β h Ξ) z) (k : Fin M) :
    z k
      =
      (1 / (N : ℝ)) *
        ∑ i : Fin N,
          (hopfieldEta (N := N) (M := M) Ξ i k)
            * Real.tanh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h) :=
  hopfieldPsi_coord_eq_of_fderiv_eq_zero (N := N) (M := M) (β := β) (h := h) (Ξ := Ξ) (z := z)
    hβ hN (hz.fderiv_eq_zero) k

/-! ### A priori bounds for critical points / local maxima -/

lemma abs_hopfieldEta_eq_one (Ξ : Patterns N M) (i : Fin N) (k : Fin M) :
    |hopfieldEta (N := N) (M := M) Ξ i k| = 1 := by
  by_cases hk : Ξ k i = true <;> simp [hopfieldEta, spin, hk]

lemma abs_one_div_mul_sum_le_one
    (a : Fin N → ℝ) (hN : (N : ℝ) ≠ 0) (habs : ∀ i, |a i| ≤ (1 : ℝ)) :
    |(1 / (N : ℝ)) * ∑ i : Fin N, a i| ≤ (1 : ℝ) := by
  have hN0 : N ≠ 0 := by
    intro hN0
    apply hN
    simp [hN0]
  have hNpos : 0 ≤ (1 / (N : ℝ)) := by
    have hNpos' : 0 < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN0)
    exact (one_div_pos.2 hNpos').le
  have hsum_abs : |∑ i : Fin N, a i| ≤ ∑ i : Fin N, |a i| := by
    simpa using
      (Finset.abs_sum_le_sum_abs (f := a) (s := (Finset.univ : Finset (Fin N))))
  have hsum_le : (∑ i : Fin N, |a i|) ≤ ∑ _i : Fin N, (1 : ℝ) := by
    simpa using
      (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin N))) (fun i _hi => habs i))
  calc
    |(1 / (N : ℝ)) * ∑ i : Fin N, a i|
        = (1 / (N : ℝ)) * |∑ i : Fin N, a i| := by
            simp [abs_mul]
    _ ≤ (1 / (N : ℝ)) * (∑ i : Fin N, |a i|) := by
            exact mul_le_mul_of_nonneg_left hsum_abs hNpos
    _ ≤ (1 / (N : ℝ)) * (∑ _i : Fin N, (1 : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hsum_le hNpos
    _ = 1 := by
            -- `∑ i, 1 = N` and `(1/N) * N = 1`.
            simp [hN, one_div]

lemma abs_coord_le_one_of_fderiv_eq_zero
    (β h : ℝ) (Ξ : Patterns N M) (z : Fin M → ℝ)
    (hβ : β ≠ 0) (hN : (N : ℝ) ≠ 0)
    (hz : fderiv ℝ (hopfieldPsi (N := N) (M := M) β h Ξ) z = 0) (k : Fin M) :
    |z k| ≤ 1 := by
  have hcoord :=
    hopfieldPsi_coord_eq_of_fderiv_eq_zero (N := N) (M := M) (β := β) (h := h) (Ξ := Ξ)
      (z := z) hβ hN hz k
  -- abbreviate the summand
  set a : Fin N → ℝ :=
    fun i => hopfieldEta (N := N) (M := M) Ξ i k * Real.tanh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h)
  have ha : z k = (1 / (N : ℝ)) * ∑ i : Fin N, a i := by
    simpa [a] using hcoord
  have habs_le : ∀ i : Fin N, |a i| ≤ (1 : ℝ) := by
    intro i
    have ht : |Real.tanh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h)| ≤ (1 : ℝ) :=
      (le_of_lt (Real.abs_tanh_lt_one _))
    calc
      |a i|
          = |hopfieldEta (N := N) (M := M) Ξ i k|
              * |Real.tanh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h)| := by
                simp [a, abs_mul]
      _ = 1 * |Real.tanh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h)| := by
            simp [abs_hopfieldEta_eq_one (N := N) (M := M) (Ξ := Ξ) (i := i) (k := k)]
      _ = |Real.tanh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h)| := by simp
      _ ≤ 1 := ht
  have hbound : |(1 / (N : ℝ)) * ∑ i : Fin N, a i| ≤ (1 : ℝ) :=
    abs_one_div_mul_sum_le_one (N := N) (a := a) hN habs_le
  simpa [ha] using hbound

lemma abs_coord_le_one_of_isLocalMax
    (β h : ℝ) (Ξ : Patterns N M) (z : Fin M → ℝ)
    (hβ : β ≠ 0) (hN : (N : ℝ) ≠ 0)
    (hz : IsLocalMax (hopfieldPsi (N := N) (M := M) β h Ξ) z) (k : Fin M) :
    |z k| ≤ 1 :=
  abs_coord_le_one_of_fderiv_eq_zero (N := N) (M := M) (β := β) (h := h) (Ξ := Ξ) (z := z)
    hβ hN (hz.fderiv_eq_zero) k

/-! ### Existence of a maximizer on the cube `[-1,1]^M` -/

theorem exists_isMaxOn_hopfieldPsi_Icc (β h : ℝ) (Ξ : Patterns N M) :
    ∃ z ∈ Set.Icc (fun _ : Fin M => (-1 : ℝ)) (fun _ : Fin M => (1 : ℝ)),
      IsMaxOn (hopfieldPsi (N := N) (M := M) β h Ξ)
        (Set.Icc (fun _ : Fin M => (-1 : ℝ)) (fun _ : Fin M => (1 : ℝ))) z := by
  have hdiff : Differentiable ℝ (hopfieldPsi (N := N) (M := M) β h Ξ) := by
    intro z
    exact (hasFDerivAt_hopfieldPsi (N := N) (M := M) (β := β) (h := h) Ξ z).differentiableAt
  have hcont :
      ContinuousOn (hopfieldPsi (N := N) (M := M) β h Ξ)
        (Set.Icc (fun _ : Fin M => (-1 : ℝ)) (fun _ : Fin M => (1 : ℝ))) :=
    hdiff.continuous.continuousOn
  have hne :
      (Set.Icc (fun _ : Fin M => (-1 : ℝ)) (fun _ : Fin M => (1 : ℝ))).Nonempty := by
    refine ⟨0, ?_⟩
    constructor <;> intro i <;> norm_num
  simpa using (isCompact_Icc.exists_isMaxOn hne hcont)

/-! ### Global maximizers (coercivity) -/

lemma abs_hopfieldEtaDot_le (Ξ : Patterns N M) (i : Fin N) (z : Fin M → ℝ) :
    |hopfieldEtaDot (N := N) (M := M) Ξ i z| ≤ (M : ℝ) * ‖z‖ := by
  set b : Fin M → ℝ := fun k => hopfieldEta (N := N) (M := M) Ξ i k * z k
  have hsum : hopfieldEtaDot (N := N) (M := M) Ξ i z = ∑ k : Fin M, b k := by
    simp [hopfieldEtaDot, b]
  have hsum_abs : |∑ k : Fin M, b k| ≤ ∑ k : Fin M, |b k| := by
    simpa using
      (Finset.abs_sum_le_sum_abs (f := b) (s := (Finset.univ : Finset (Fin M))))
  have habs : ∀ k : Fin M, |b k| = |z k| := by
    intro k
    have hη : |hopfieldEta (N := N) (M := M) Ξ i k| = 1 := by
      simpa [hopfieldEta] using (abs_spin_eq_one (N := N) (σ := Ξ k) (i := i))
    simp [b, abs_mul, hη]
  have hsum' : ∑ k : Fin M, |z k| ≤ (M : ℝ) * ‖z‖ := by
    have hterm : ∀ k : Fin M, |z k| ≤ ‖z‖ := by
      intro k
      simpa [Real.norm_eq_abs] using (norm_le_pi_norm z k)
    have hle : (∑ k : Fin M, |z k|) ≤ ∑ _k : Fin M, ‖z‖ := by
      refine Finset.sum_le_sum ?_
      intro k _hk
      exact hterm k
    simpa [Finset.sum_const, nsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hle
  calc
    |hopfieldEtaDot (N := N) (M := M) Ξ i z|
        = |∑ k : Fin M, b k| := by simp [hsum]
    _ ≤ ∑ k : Fin M, |b k| := hsum_abs
    _ = ∑ k : Fin M, |z k| := by
          refine Finset.sum_congr rfl ?_
          intro k _hk
          simpa using habs k
    _ ≤ (M : ℝ) * ‖z‖ := hsum'

lemma norm_sq_le_finVecNormSq (z : Fin M → ℝ) :
    ‖z‖ ^ 2 ≤ finVecNormSq M z := by
  cases M with
  | zero =>
      have hz : z = 0 := by
        funext i
        exact (Fin.elim0 i)
      simp [hz, finVecNormSq]
  | succ M =>
      have hne : (Finset.univ : Finset (Fin (M + 1))).Nonempty := Finset.univ_nonempty
      rcases (Finset.sup_mem_of_nonempty (s := (Finset.univ : Finset (Fin (M + 1))))
        (f := fun k : Fin (M + 1) => ‖z k‖₊) hne) with ⟨k0, hk0, hk0eq⟩
      have hzk0 : ‖z‖ = ‖z k0‖ := by
        have : (Finset.univ.sup fun k : Fin (M + 1) => ‖z k‖₊) = ‖z k0‖₊ := hk0eq.symm
        calc
          ‖z‖ = (↑(Finset.univ.sup fun k : Fin (M + 1) => ‖z k‖₊) : ℝ) := by
                  simpa using (Pi.norm_def (f := z))
          _ = (↑(‖z k0‖₊) : ℝ) := by
                  simp [this]
          _ = ‖z k0‖ := by
                  simp
      have hterm : ‖z k0‖ ^ 2 ≤ finVecNormSq (M + 1) z := by
        have hnonneg : ∀ k : Fin (M + 1), 0 ≤ (z k) ^ 2 := fun k => sq_nonneg (z k)
        have hsingle : (z k0) ^ 2 ≤ ∑ k : Fin (M + 1), (z k) ^ 2 := by
          simpa using
            (Finset.single_le_sum (s := (Finset.univ : Finset (Fin (M + 1))))
              (f := fun k : Fin (M + 1) => (z k) ^ 2)
              (fun k _hk => hnonneg k) (by simp))
        simpa [Real.norm_eq_abs, sq_abs] using hsingle
      have hpow : ‖z‖ ^ 2 = ‖z k0‖ ^ 2 := by simp [hzk0]
      have hsq : ‖z k0‖ ^ 2 = (z k0) ^ 2 := by
        simp [Real.norm_eq_abs, sq_abs]
      calc
        ‖z‖ ^ 2 = ‖z k0‖ ^ 2 := hpow
        _ = (z k0) ^ 2 := hsq
        _ ≤ finVecNormSq (M + 1) z := by
              simpa [hsq] using hterm

lemma hopfieldPsi_le_quadratic_norm
    (β h : ℝ) (Ξ : Patterns N M) (z : Fin M → ℝ) (hβ : 0 ≤ β) :
    hopfieldPsi (N := N) (M := M) β h Ξ z
      ≤
      -((N : ℝ) * β / 2) * (‖z‖ ^ 2)
        + (N : ℝ) * (|β| * (M : ℝ) * ‖z‖ + |h|) := by
  have hc : -((N : ℝ) * β / 2) ≤ 0 := by
    have hnonneg : 0 ≤ (N : ℝ) * β / 2 := by
      have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
      have hNβ : 0 ≤ (N : ℝ) * β := mul_nonneg hN hβ
      exact div_nonneg hNβ (by norm_num)
    exact neg_nonpos.2 hnonneg
  have hquad :
      -((N : ℝ) * β / 2) * finVecNormSq M z
        ≤ -((N : ℝ) * β / 2) * (‖z‖ ^ 2) := by
    simpa [mul_assoc] using
      (mul_le_mul_of_nonpos_left (norm_sq_le_finVecNormSq (M := M) z) hc)
  have hlog :
      ∑ i : Fin N, Real.log (Real.cosh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h))
        ≤ (N : ℝ) * (|β| * (M : ℝ) * ‖z‖ + |h|) := by
    have hterm :
        ∀ i : Fin N,
          Real.log (Real.cosh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h))
            ≤ |β| * (M : ℝ) * ‖z‖ + |h| := by
      intro i
      have hcosh :
          Real.log (Real.cosh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h))
            ≤ |β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h| := by
        simpa using log_cosh_le_abs (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h)
      have habs :
          |β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h|
            ≤ |β| * |hopfieldEtaDot (N := N) (M := M) Ξ i z| + |h| := by
        calc
          |β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h|
              ≤ |β * hopfieldEtaDot (N := N) (M := M) Ξ i z| + |h| := abs_add_le _ _
          _ = |β| * |hopfieldEtaDot (N := N) (M := M) Ξ i z| + |h| := by
                simp [abs_mul]
      have hη :
          |β| * |hopfieldEtaDot (N := N) (M := M) Ξ i z|
            ≤ |β| * ((M : ℝ) * ‖z‖) := by
        exact mul_le_mul_of_nonneg_left
          (abs_hopfieldEtaDot_le (N := N) (M := M) (Ξ := Ξ) (i := i) (z := z))
          (abs_nonneg β)
      have hη' :
          |β| * |hopfieldEtaDot (N := N) (M := M) Ξ i z| + |h|
            ≤ |β| * (M : ℝ) * ‖z‖ + |h| := by
        have : |β| * ((M : ℝ) * ‖z‖) + |h| = |β| * (M : ℝ) * ‖z‖ + |h| := by
          ring_nf
        exact (add_le_add_left hη |h|).trans_eq this
      exact hcosh.trans (habs.trans hη')
    have hsum :
        (∑ i : Fin N,
          Real.log (Real.cosh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h)))
          ≤ ∑ _i : Fin N, (|β| * (M : ℝ) * ‖z‖ + |h|) := by
      refine Finset.sum_le_sum ?_
      intro i _hi
      exact hterm i
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hsum
  have hψ :
      hopfieldPsi (N := N) (M := M) β h Ξ z
        = -((N : ℝ) * β / 2) * finVecNormSq M z
          + ∑ i : Fin N, Real.log (Real.cosh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h)) := by
    simp [hopfieldPsi]
  calc
    hopfieldPsi (N := N) (M := M) β h Ξ z
        = -((N : ℝ) * β / 2) * finVecNormSq M z
            + ∑ i : Fin N, Real.log (Real.cosh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h)) := hψ
    _ ≤ -((N : ℝ) * β / 2) * (‖z‖ ^ 2)
          + (N : ℝ) * (|β| * (M : ℝ) * ‖z‖ + |h|) := by
          exact add_le_add hquad hlog

lemma tendsto_hopfieldPsi_cocompact_atBot
    (β h : ℝ) (Ξ : Patterns N M) (hβ : 0 < β) (hN : N ≠ 0) :
    Filter.Tendsto (hopfieldPsi (N := N) (M := M) β h Ξ) (Filter.cocompact (Fin M → ℝ))
      Filter.atBot := by
  have hβ0 : 0 ≤ β := hβ.le
  have hN0 : 0 < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hcoeff_neg : -((N : ℝ) * β / 4) < 0 := by
    have : 0 < (N : ℝ) * β / 4 := by
      have : 0 < (N : ℝ) * β := mul_pos hN0 hβ
      exact div_pos this (by norm_num)
    simpa using (neg_neg_of_pos this)
  have hnorm :
      Filter.Tendsto (fun z : Fin M → ℝ => ‖z‖) (Filter.cocompact (Fin M → ℝ)) Filter.atTop := by
    simpa using (tendsto_norm_cocompact_atTop (E := (Fin M → ℝ)))
  have hnegquad :
      Filter.Tendsto
          (fun z : Fin M → ℝ => (-((N : ℝ) * β / 4)) * (‖z‖ ^ (2 : ℕ)))
          (Filter.cocompact (Fin M → ℝ)) Filter.atBot := by
    have h' :
        Filter.Tendsto (fun x : ℝ => (-((N : ℝ) * β / 4)) * x ^ (2 : ℕ)) Filter.atTop
          Filter.atBot :=
      Filter.tendsto_neg_const_mul_pow_atTop (c := -((N : ℝ) * β / 4)) (n := 2) (by decide)
        hcoeff_neg
    exact h'.comp hnorm
  have hdom :
      (fun z : Fin M → ℝ => hopfieldPsi (N := N) (M := M) β h Ξ z)
        ≤ᶠ[Filter.cocompact (Fin M → ℝ)]
        (fun z : Fin M → ℝ => (-((N : ℝ) * β / 4)) * (‖z‖ ^ (2 : ℕ))) := by
    -- reduce to the quadratic upper bound and dominate the linear term for large `‖z‖`
    have hR :
        ∀ᶠ z : Fin M → ℝ in Filter.cocompact (Fin M → ℝ),
          (N : ℝ) * (|β| * (M : ℝ) * ‖z‖ + |h|)
            ≤ ((N : ℝ) * β / 4) * (‖z‖ ^ (2 : ℕ)) := by
      have hR' :
          ∀ᶠ z : Fin M → ℝ in Filter.cocompact (Fin M → ℝ),
            max (1 : ℝ) (4 * ((M : ℝ) + |h| / β)) ≤ ‖z‖ :=
        hnorm.eventually (Filter.eventually_ge_atTop (max (1 : ℝ) (4 * ((M : ℝ) + |h| / β))))
      filter_upwards [hR'] with z hz
      have hz1 : (1 : ℝ) ≤ ‖z‖ := (le_max_left _ _).trans hz
      have hzM : 4 * ((M : ℝ) + |h| / β) ≤ ‖z‖ := (le_max_right _ _).trans hz
      have hz0 : 0 ≤ ‖z‖ := (norm_nonneg z)
      have habsβ : |β| = β := by simp [abs_of_nonneg hβ0]
      have hh : |h| ≤ |h| * ‖z‖ := by
        simpa [one_mul] using (mul_le_mul_of_nonneg_left hz1 (abs_nonneg h))
      have hlin :
          |β| * (M : ℝ) * ‖z‖ + |h| ≤ β / 4 * (‖z‖ ^ (2 : ℕ)) := by
        -- use `‖z‖ ≥ 1` to absorb `|h|`, then use `‖z‖ ≥ 4 * (M + |h|/β)`
        have hsum :
            |β| * (M : ℝ) * ‖z‖ + |h| ≤ (β * (M : ℝ) + |h|) * ‖z‖ := by
          calc
            |β| * (M : ℝ) * ‖z‖ + |h|
                ≤ |β| * (M : ℝ) * ‖z‖ + (|h| * ‖z‖) := add_le_add_right hh _
            _ = (β * (M : ℝ) + |h|) * ‖z‖ := by
                  simp [habsβ, mul_assoc, add_mul]
        have hbound :
            (β * (M : ℝ) + |h|) * ‖z‖ ≤ (β / 4) * (‖z‖ ^ (2 : ℕ)) := by
          have : (β * (M : ℝ) + |h|) ≤ (β / 4) * ‖z‖ := by
            -- from `hzM : 4 * (M + |h|/β) ≤ ‖z‖`
            have hmul :=
              mul_le_mul_of_nonneg_left hzM (show (0 : ℝ) ≤ β / 4 by positivity)
            have hβne : β ≠ 0 := ne_of_gt hβ
            have hsim :
                (β / 4) * (4 * ((M : ℝ) + |h| / β)) = β * (M : ℝ) + |h| := by
              calc
                (β / 4) * (4 * ((M : ℝ) + |h| / β))
                    = ((β / 4) * 4) * ((M : ℝ) + |h| / β) := by
                        simpa using (mul_assoc (β / 4) 4 ((M : ℝ) + |h| / β)).symm
                _ = β * ((M : ℝ) + |h| / β) := by
                      have h4 : (4 : ℝ) ≠ 0 := by norm_num
                      have hβ4 : (β / 4) * 4 = β := by
                        -- `β / 4 * 4 = β`
                        simp [h4]
                      simp [hβ4]
                _ = β * (M : ℝ) + β * (|h| / β) := by
                      simp [mul_add]
                _ = β * (M : ℝ) + |h| := by
                      have : β * (|h| / β) = (β * |h|) / β := by
                        simpa using (mul_div_assoc β |h| β).symm
                      -- `((β * |h|) / β) = |h|`
                      simp [this, hβne]
            simpa [hsim] using hmul
          have hmul' : (β * (M : ℝ) + |h|) * ‖z‖ ≤ ((β / 4) * ‖z‖) * ‖z‖ :=
            mul_le_mul_of_nonneg_right this hz0
          simpa [pow_two, mul_assoc] using hmul'
        -- combine and rewrite `‖z‖ * ‖z‖` as `‖z‖ ^ 2`
        have : (β * (M : ℝ) + |h|) * ‖z‖ ≤ (β / 4) * (‖z‖ ^ (2 : ℕ)) := hbound
        exact hsum.trans this
      have hNnonneg : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
      have := mul_le_mul_of_nonneg_left (by simpa [habsβ] using hlin) hNnonneg
      -- put the RHS in the standard `((N:ℝ) * β / 4) * ‖z‖^2` shape
      simpa [mul_add, mul_assoc, habsβ, div_eq_mul_inv] using this
    filter_upwards [hR] with z hz
    have hψ :=
      hopfieldPsi_le_quadratic_norm (N := N) (M := M) (β := β) (h := h) (Ξ := Ξ) (z := z) hβ0
    have hpow : (‖z‖ ^ 2) = (‖z‖ ^ (2 : ℕ)) := by simp
    calc
      hopfieldPsi (N := N) (M := M) β h Ξ z
          ≤ -((N : ℝ) * β / 2) * (‖z‖ ^ 2)
              + (N : ℝ) * (|β| * (M : ℝ) * ‖z‖ + |h|) := hψ
      _ ≤ -((N : ℝ) * β / 2) * (‖z‖ ^ (2 : ℕ))
              + ((N : ℝ) * β / 4) * (‖z‖ ^ (2 : ℕ)) := by
            simpa [hpow, mul_assoc, add_assoc, add_left_comm, add_comm] using
              add_le_add_left hz (-((N : ℝ) * β / 2) * (‖z‖ ^ (2 : ℕ)))
      _ = (-((N : ℝ) * β / 4)) * (‖z‖ ^ (2 : ℕ)) := by ring
  exact (Filter.tendsto_atBot_mono' (l := Filter.cocompact (Fin M → ℝ)) hdom) hnegquad

theorem exists_maximizer_hopfieldPsi
    (β h : ℝ) (Ξ : Patterns N M) (hβ : 0 < β) (hN : N ≠ 0) :
    ∃ z : Fin M → ℝ, ∀ y : Fin M → ℝ,
      hopfieldPsi (N := N) (M := M) β h Ξ y ≤ hopfieldPsi (N := N) (M := M) β h Ξ z := by
  have hcont : Continuous (hopfieldPsi (N := N) (M := M) β h Ξ) :=
    (differentiable_hopfieldPsi (N := N) (M := M) (β := β) (h := h) (Ξ := Ξ)).continuous
  have hlim :
      Filter.Tendsto (hopfieldPsi (N := N) (M := M) β h Ξ) (Filter.cocompact (Fin M → ℝ))
        Filter.atBot :=
    tendsto_hopfieldPsi_cocompact_atBot (N := N) (M := M) (β := β) (h := h) (Ξ := Ξ) hβ hN
  simpa using (hcont.exists_forall_ge hlim)

/-! ### Specialization: axis critical points under `IsConstantPattern` -/

lemma hopfieldEtaDot_smul_piSingle_one
    (Ξ : Patterns N M) (i : Fin N) (m : ℝ) (k : Fin M) :
    hopfieldEtaDot (N := N) (M := M) Ξ i (m • Pi.single (M := fun _ : Fin M => ℝ) k (1 : ℝ))
      =
      m * hopfieldEta (N := N) (M := M) Ξ i k := by
  simp [hopfieldEtaDot, Pi.single_apply, smul_eq_mul, mul_comm]

lemma hopfieldEtaDot_smul_piSingle_one_of_isConstantPattern
    {Ξ : Patterns N M} {k0 : Fin M} (hΞ : IsConstantPattern (N := N) Ξ k0)
    (i : Fin N) (m : ℝ) :
    hopfieldEtaDot (N := N) (M := M) Ξ i (m • Pi.single (M := fun _ : Fin M => ℝ) k0 (1 : ℝ)) = m := by
  simp [hopfieldEta_eq_one_of_isConstantPattern (N := N) (hΞ := hΞ) (i := i),
    hopfieldEtaDot_smul_piSingle_one (N := N) (M := M) (Ξ := Ξ) (i := i) (m := m) (k := k0)]

lemma fixedPoint_tanh_of_hopfieldPsi_critical_on_axis
    (β h : ℝ) {Ξ : Patterns N M} {k0 : Fin M} (hΞ : IsConstantPattern (N := N) Ξ k0)
    (m : ℝ) (hβ : β ≠ 0) (hN : (N : ℝ) ≠ 0)
    (hm : fderiv ℝ (hopfieldPsi (N := N) (M := M) β h Ξ)
            (m • Pi.single (M := fun _ : Fin M => ℝ) k0 (1 : ℝ)) = 0) :
    m = Real.tanh (β * m + h) := by
  -- apply the coordinate fixed-point equation at `k0`
  have hcoord :=
    hopfieldPsi_coord_eq_of_fderiv_eq_zero (N := N) (M := M) (β := β) (h := h) (Ξ := Ξ)
      (z := m • Pi.single (M := fun _ : Fin M => ℝ) k0 (1 : ℝ)) hβ hN hm k0
  -- simplify the RHS using the constant-pattern assumption
  simpa [Pi.single_apply, hopfieldEta_eq_one_of_isConstantPattern (N := N) (hΞ := hΞ),
    hopfieldEtaDot_smul_piSingle_one_of_isConstantPattern (N := N) (M := M) (hΞ := hΞ),
    Finset.sum_const, hN, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using hcoord

/-! ### Second derivative: Hessian of `hopfieldPsi` -/

/-- Second derivative of `finVecNormSq`. Constant map (as a bilinear map). -/
noncomputable def finVecNormSqFDeriv2 : (Fin M → ℝ) →L[ℝ] (Fin M → ℝ) →L[ℝ] ℝ :=
  ∑ k : Fin M, (2 : ℝ) • (ContinuousLinearMap.proj (R := ℝ) k).smulRight (ContinuousLinearMap.proj (R := ℝ) k)

lemma finVecNormSqFDeriv_eq_finVecNormSqFDeriv2 (z : Fin M → ℝ) :
    finVecNormSqFDeriv (M := M) z = finVecNormSqFDeriv2 (M := M) z := by
  ext v
  -- unfold both sides and compare coefficients
  simp [finVecNormSqFDeriv_apply, finVecNormSqFDeriv2, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]

@[fun_prop] lemma hasFDerivAt_finVecNormSqFDeriv (z : Fin M → ℝ) :
    HasFDerivAt (finVecNormSqFDeriv (M := M)) (finVecNormSqFDeriv2 (M := M)) z := by
  -- `finVecNormSqFDeriv` is linear, so its derivative is itself (as a constant bilinear map)
  rw [funext finVecNormSqFDeriv_eq_finVecNormSqFDeriv2]
  exact (finVecNormSqFDeriv2 (M := M)).hasFDerivAt

/-- Hessian (second Fréchet derivative) of `hopfieldPsi` at `z`. -/
noncomputable def hopfieldPsiFDeriv2 (β h : ℝ) (Ξ : Patterns N M) (z : Fin M → ℝ) :
    (Fin M → ℝ) →L[ℝ] (Fin M → ℝ) →L[ℝ] ℝ :=
  -(((N : ℝ) * β / 2) • finVecNormSqFDeriv2 (M := M))
    + ∑ i : Fin N,
        ((1 - Real.tanh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h) ^ 2) * β ^ 2)
          • (hopfieldEtaDotCLM (N := N) (M := M) Ξ i).smulRight (hopfieldEtaDotCLM (N := N) (M := M) Ξ i)

@[fun_prop] lemma hasFDerivAt_hopfieldPsiFDeriv (β h : ℝ) (Ξ : Patterns N M) (z : Fin M → ℝ) :
    HasFDerivAt (hopfieldPsiFDeriv (N := N) (M := M) β h Ξ) (hopfieldPsiFDeriv2 (N := N) (M := M) β h Ξ z) z := by
  -- term 1: quadratic part
  have h1 : HasFDerivAt (fun z => -(((N : ℝ) * β / 2) • finVecNormSqFDeriv (M := M) z))
      (-(((N : ℝ) * β / 2) • finVecNormSqFDeriv2 (M := M))) z := by
    -- `finVecNormSqFDeriv` is linear in `z`, so the derivative is constant.
    have hlin : HasFDerivAt (finVecNormSqFDeriv (M := M)) (finVecNormSqFDeriv2 (M := M)) z :=
      hasFDerivAt_finVecNormSqFDeriv (M := M) z
    -- scale and negate
    simpa using (hlin.const_smul ((N : ℝ) * β / 2)).neg
  -- term 2: sum of log-cosh derivatives
  have h2 : HasFDerivAt
      (fun z => ∑ i : Fin N, (Real.tanh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h) * β)
          • hopfieldEtaDotCLM (N := N) (M := M) Ξ i)
      (∑ i : Fin N,
        ((1 - Real.tanh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h) ^ 2) * β ^ 2)
          • (hopfieldEtaDotCLM (N := N) (M := M) Ξ i).smulRight (hopfieldEtaDotCLM (N := N) (M := M) Ξ i)) z := by
    -- use the generic `SpinGlass.LogCosh` calculus (termwise differentiation + rank-one Hessians)
    simpa [SpinGlass.LogCosh.sumFDeriv, SpinGlass.LogCosh.sumFDeriv2, SpinGlass.LogCosh.termFDeriv,
      SpinGlass.LogCosh.termFDeriv2, hopfieldEtaDot_eq_hopfieldEtaDotCLM] using
      (SpinGlass.LogCosh.hasFDerivAt_sumFDeriv (V := (Fin M → ℝ)) (β := β) (h := h)
        (L := fun i : Fin N => hopfieldEtaDotCLM (N := N) (M := M) Ξ i) (z := z))
  convert h1.add h2

end SpinGlass
