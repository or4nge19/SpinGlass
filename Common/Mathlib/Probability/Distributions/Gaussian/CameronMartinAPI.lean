import Common.Mathlib.Probability.Distributions.Gaussian.CameronMartinThm
import Common.Mathlib.Probability.Distributions.Gaussian.CameronMartinFernique
import Common.Mathlib.Probability.Distributions.Gaussian.IntegrationByParts
import Common.Mathlib.Probability.Distributions.Gaussian.CameronMartinRV

/-!
# Cameron–Martin toolkit: public API

This file is the **public-facing** entry point for the Cameron–Martin toolkit in this repo:

- Cameron–Martin theorem / laws (`hasLaw_cameronMartin`, ...)
- Fernique consequences (`exists_C_pos_integrable_rexp_sq_dual`, ...)
- Gaussian integration by parts in Cameron–Martin form
  (`cameronMartin_integral_by_parts_bounded`,
   `cameronMartin_integral_by_parts_of_integrable_bound`).

Downstream developments should prefer importing this file over the implementation files.
-/

export ProbabilityTheory
  (hasLaw_cameronMartin
   cameronMartin_integral_by_parts_bounded
   cameronMartin_integral_by_parts_polyGrowth
   cameronMartin_integral_by_parts_of_integrable_bound)

export ProbabilityTheory.HasLaw
  (lintegral_add_cmCoe_smul_eq
   hasLaw_add_cmCoe_smul_withDensity_raw
   cameronMartin_integral_by_parts_bounded
   cameronMartin_integral_by_parts_polyGrowth
   cameronMartin_integral_by_parts_of_integrable_bound)

export ProbabilityTheory.IsGaussian
  (exists_C_pos_integrable_rexp_norm_sq
   integrable_norm_pow
   integrable_one_add_norm_pow
   integrable_of_abs_le_mul_one_add_norm_pow
   memLp_strongDual
   integrable_abs_pow_strongDual
   exists_C_pos_integrable_rexp_sq_dual)
