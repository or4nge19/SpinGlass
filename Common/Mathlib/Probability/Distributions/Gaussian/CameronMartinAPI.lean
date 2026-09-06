import Common.Mathlib.Probability.Distributions.Gaussian.CameronMartinThm
import Common.Mathlib.Probability.Distributions.Gaussian.CameronMartinFernique
import Common.Mathlib.Probability.Distributions.Gaussian.IntegrationByParts
import Common.Mathlib.Probability.Distributions.Gaussian.CameronMartinRV

/-!
# Cameron–Martin toolkit

Public API: Cameron–Martin theorem (`hasLaw_cameronMartin`), Fernique
(`exists_C_pos_integrable_rexp_sq_dual`), and Gaussian IBP
(`cameronMartin_integral_by_parts_bounded`, `cameronMartin_integral_by_parts_of_integrable_bound`).
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
