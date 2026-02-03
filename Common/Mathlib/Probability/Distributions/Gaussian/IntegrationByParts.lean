import Common.Mathlib.Probability.Distributions.Gaussian.CameronMartinIBPAnalyticAPI

/-!
# Gaussian integration by parts (intrinsic Cameron–Martin interface)

This file is intended as the **single** intrinsic entry point for Gaussian integration by parts.

The core statement is the Cameron–Martin integration-by-parts identity for a Gaussian measure `μ`
on a real Banach space:

`∫ y, (x y) * F y ∂μ = ∫ y, (fderiv ℝ F y) (cmCoe x) ∂μ`,

for `x : cameronMartin μ`, with analytic assumptions provided in tiers:
- a maximally general dominated/integrability form;
- a powerful polynomial-growth corollary (discharging integrability via Fernique).

All other formulations (1D Stein, Hilbert covariance-operator phrasing, RV-facing versions) should
be derived as corollaries of these theorems.
-/

export ProbabilityTheory
  (cameronMartin_integral_by_parts_bounded
   cameronMartin_integral_by_parts_polyGrowth
   cameronMartin_integral_by_parts_of_integrable_bound)
