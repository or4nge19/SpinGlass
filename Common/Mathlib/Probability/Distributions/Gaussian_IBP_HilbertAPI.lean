import Common.Mathlib.Probability.Distributions.Gaussian_IBP_Hilbert

/-!
# Gaussian integration by parts on Hilbert spaces (public API)

This file is the **public-facing** entry point for the finite-dimensional Hilbert-space Gaussian
integration-by-parts development in this repository.

It re-exports only the intrinsic/public statements, phrased using Mathlib's covariance operator
(`ProbabilityTheory.covarianceOperator`) of the law `(ℙ).map g`, so that downstream users do not
need to interact with the coordinate/Fintype implementation details.
-/

export PhysLean.Probability.GaussianIBP
  (covOp_eq_covarianceOperator_map
   gaussian_integration_by_parts_hilbert_covarianceOperator
   cmCoe_cmOfDual_innerSL_eq_covarianceOperator
   gaussian_integral_inner_mul_eq_integral_fderiv_covarianceOperator_polyGrowth)
