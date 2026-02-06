/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Common.Mathlib.Probability.Distributions.Gaussian.CameronMartinIBPAnalytic

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

## Main results

- `ProbabilityTheory.cameronMartin_integral_by_parts_of_integrable_bound`
- `ProbabilityTheory.cameronMartin_integral_by_parts_bounded`
- `ProbabilityTheory.cameronMartin_integral_by_parts_polyGrowth`
-/

export ProbabilityTheory
  (cameronMartin_integral_by_parts_bounded
   cameronMartin_integral_by_parts_polyGrowth
   cameronMartin_integral_by_parts_of_integrable_bound)
