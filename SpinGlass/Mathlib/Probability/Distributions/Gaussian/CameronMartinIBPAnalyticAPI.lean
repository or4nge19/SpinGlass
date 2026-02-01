import SpinGlass.Mathlib.Probability.Distributions.Gaussian.CameronMartinIBPAnalytic

/-!
# Cameron–Martin IBP: public API (analytic layer)

This file provides the **public-facing** statements from `CameronMartinIBPAnalytic.lean`.

The implementation details (dominated differentiation, domination profiles) are kept in the
implementation file; downstream developments should import this file and use the theorems here.
-/

/-!
Re-export:
- `ProbabilityTheory.cameronMartin_integral_by_parts_bounded`
-/

export ProbabilityTheory (cameronMartin_integral_by_parts_bounded)

