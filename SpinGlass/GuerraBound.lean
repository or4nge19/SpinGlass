import SpinGlass.Algebra

open MeasureTheory ProbabilityTheory Real BigOperators

namespace SpinGlass

/-!
# Guerra's interpolation bound: the finite-`N` derivative inequality

Guerra's replica-symmetric comparison rests on one exact identity and one sign. For the
replica-symmetric reference `ξ_ref x = β² q x`, the half-difference of the SK and reference
Hessian traces is
`(β²/4) ((1 - q)² - ⟨(R₁₂ - q)²⟩)`,
so it never exceeds `(β²/4)(1 - q)²`. Combined with
`hasDerivAt_guerraPhi_eq_trace_integral` this bounds `φ'(t)` uniformly in `t`, which is the
analytic input to Guerra's bound. Talagrand Vol. I, §1.3, Eq. (1.65)–(1.71).

## Main statements

- `guerra_trace_sub_rs_eq`: the exact identity, with the overlap defect `⟨(R₁₂ - q)²⟩` isolated.
- `guerra_trace_sub_rs_le`: the resulting inequality `≤ (β²/4)(1 - q)²`.
- `guerra_trace_sub_overlapCovKernel_eq`: the same identity for an arbitrary pair `ξ₁, ξ₂`, from
  which the replica-symmetric case is the specialization.
-/

variable {N : ℕ} {β : ℝ}

/-- Half-difference of two overlap-driven Hessian traces, in bracket form. This is the general
identity behind Guerra's scheme: only `ξ₁ - ξ₂` enters. Talagrand Vol. I, Eq. (1.65). -/
theorem guerra_trace_sub_overlapCovKernel_eq (hN : 0 < N) (H : EnergySpace N) (xi₁ xi₂ : ℝ → ℝ) :
    (1 / 2 : ℝ) *
        ((∑ σ, ∑ τ, overlapCovKernel (N := N) xi₁ σ τ *
              hessian_free_energy N H (std_basis N σ) (std_basis N τ))
          - (∑ σ, ∑ τ, overlapCovKernel (N := N) xi₂ σ τ *
              hessian_free_energy N H (std_basis N σ) (std_basis N τ)))
      = (1 / 2 : ℝ) *
          ((xi₁ 1 - xi₂ 1)
            - gibbs_average₂ (N := N) H
                (fun σ τ => xi₁ (overlap N σ τ) - xi₂ (overlap N σ τ))) :=
  half_trace_sub_overlapCovKernel (N := N) hN H xi₁ xi₂

/-- **Guerra's interpolation identity (replica-symmetric reference).** The overlap defect
`⟨(R₁₂ - q)²⟩` is isolated by completing the square. Talagrand Vol. I, §1.3, Eq. (1.65)–(1.71). -/
theorem guerra_trace_sub_rs_eq (hN : 0 < N) (H : EnergySpace N) (q : ℝ) :
    (1 / 2 : ℝ) *
        ((∑ σ, ∑ τ, sk_cov_kernel N β σ τ *
              hessian_free_energy N H (std_basis N σ) (std_basis N τ))
          - (∑ σ, ∑ τ, simple_cov_kernel N β (fun r => q * r) σ τ *
              hessian_free_energy N H (std_basis N σ) (std_basis N τ)))
      = (β ^ 2 / 4) *
          ((1 - q) ^ 2 - gibbs_average₂ (N := N) H fun σ τ => (overlap N σ τ - q) ^ 2) := by
  classical
  simp only [sk_cov_kernel_def, simple_cov_kernel_def]
  rw [guerra_trace_sub_overlapCovKernel_eq (N := N) hN H (skCovXi β) (refCovXi β fun r => q * r)]
  -- Pointwise, `ξ_SK r - ξ_ref r = β² * ((1/2 - q) - ½((1-q)² - (r-q)²))`-free form:
  -- write the integrand as `β² * ((r²/2) - q*r)` and complete the square inside the bracket.
  have hpt : (fun σ τ => skCovXi β (overlap N σ τ) - refCovXi β (fun r => q * r) (overlap N σ τ))
      = fun σ τ => β ^ 2 * ((1 / 2 - q) - (1 / 2) * ((1 - q) ^ 2 - (overlap N σ τ - q) ^ 2)) := by
    funext σ τ; simp only [skCovXi, refCovXi]; ring
  rw [hpt, gibbs_average₂_const_mul (N := N) (H := H) (c := β ^ 2)
      (f := fun σ τ => (1 / 2 - q) - (1 / 2) * ((1 - q) ^ 2 - (overlap N σ τ - q) ^ 2)),
    gibbs_average₂_sub (N := N) (H := H) (f := fun _ _ => (1 / 2 - q))
      (g := fun σ τ => (1 / 2) * ((1 - q) ^ 2 - (overlap N σ τ - q) ^ 2)),
    gibbs_average₂_const (N := N) (H := H) (c := (1 / 2 - q)),
    gibbs_average₂_const_mul (N := N) (H := H) (c := (1 / 2 : ℝ))
      (f := fun σ τ => (1 - q) ^ 2 - (overlap N σ τ - q) ^ 2),
    gibbs_average₂_sub (N := N) (H := H) (f := fun _ _ => (1 - q) ^ 2)
      (g := fun σ τ => (overlap N σ τ - q) ^ 2),
    gibbs_average₂_const (N := N) (H := H) (c := (1 - q) ^ 2)]
  simp only [skCovXi, refCovXi]
  ring

/-- The overlap defect is nonnegative. -/
lemma gibbs_average₂_overlap_sub_sq_nonneg (H : EnergySpace N) (q : ℝ) :
    0 ≤ gibbs_average₂ (N := N) H fun σ τ => (overlap N σ τ - q) ^ 2 :=
  gibbs_average₂_nonneg (N := N) (H := H) fun _ _ => sq_nonneg _

/-- **Guerra's derivative bound (finite `N`).** The interpolation derivative integrand never
exceeds `(β²/4)(1 - q)²`, the defect being `(β²/4)⟨(R₁₂ - q)²⟩ ≥ 0`.
Talagrand Vol. I, §1.3, Eq. (1.71). -/
theorem guerra_trace_sub_rs_le (hN : 0 < N) (H : EnergySpace N) (q : ℝ) :
    (1 / 2 : ℝ) *
        ((∑ σ, ∑ τ, sk_cov_kernel N β σ τ *
              hessian_free_energy N H (std_basis N σ) (std_basis N τ))
          - (∑ σ, ∑ τ, simple_cov_kernel N β (fun r => q * r) σ τ *
              hessian_free_energy N H (std_basis N σ) (std_basis N τ)))
      ≤ (β ^ 2 / 4) * (1 - q) ^ 2 := by
  rw [guerra_trace_sub_rs_eq (N := N) (β := β) hN H q]
  have hdefect := gibbs_average₂_overlap_sub_sq_nonneg (N := N) (H := H) q
  have hcoef : (0 : ℝ) ≤ β ^ 2 / 4 := by positivity
  have hle : (1 - q) ^ 2 - gibbs_average₂ (N := N) H (fun σ τ => (overlap N σ τ - q) ^ 2)
      ≤ (1 - q) ^ 2 := by linarith
  exact mul_le_mul_of_nonneg_left hle hcoef

end SpinGlass
