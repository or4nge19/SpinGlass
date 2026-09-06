import SpinGlass.Algebra

open MeasureTheory ProbabilityTheory Real BigOperators

namespace SpinGlass

/-!
# Guerra's bound: algebraic core

Finite-`N` algebraic inequality after Gaussian IBP reduces the interpolated free-energy derivative
to a covariance/Hessian trace. Talagrand Vol. I, §1.3, Eq. (1.65).
-/

variable {N : ℕ} {β : ℝ}

/-- Algebraic Guerra derivative bound after IBP, for RSB order parameter `xi`. Talagrand Vol. I, Eq. (1.65). -/
theorem guerra_derivative_bound_algebra_core (hN : 0 < N) (H : EnergySpace N) (xi : ℝ → ℝ) :
    let term_sk := (∑ σ, ∑ τ, sk_cov_kernel N β σ τ * hessian_free_energy N H (std_basis N σ) (std_basis N τ))
    let term_simple := (∑ σ, ∑ τ, simple_cov_kernel N β xi σ τ * hessian_free_energy N H (std_basis N σ) (std_basis N τ))
    (1 / 2) * (term_sk - term_simple) = (β^2 / 2) * ((1/2 - xi 1) - ∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * ((overlap N σ τ)^2 / 2 - xi (overlap N σ τ))) :=
  SpinGlass.guerra_derivative_bound_algebra (N := N) (β := β) (xi := xi) hN H

end SpinGlass
