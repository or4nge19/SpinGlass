/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Common.Mathlib.Probability.Distributions.Gaussian.CameronMartinIBPAnalytic

/-!
# Gaussian IBP (Cameron–Martin)

For Gaussian `μ` and `x : cameronMartin μ`:
`∫ (x y) * F y ∂μ = ∫ (fderiv ℝ F y) (cmCoe x) ∂μ`.
Main: `cameronMartin_integral_by_parts_of_integrable_bound`,
`cameronMartin_integral_by_parts_bounded`, `cameronMartin_integral_by_parts_polyGrowth`.
-/

export ProbabilityTheory
  (cameronMartin_integral_by_parts_bounded
   cameronMartin_integral_by_parts_polyGrowth
   cameronMartin_integral_by_parts_of_integrable_bound)
