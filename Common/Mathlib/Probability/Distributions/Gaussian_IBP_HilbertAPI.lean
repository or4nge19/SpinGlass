/-
Copyright (c) 2026 Maria Grazia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maria Grazia
-/

import Common.Mathlib.Probability.Distributions.Gaussian_IBP_Hilbert

/-!
# Hilbert-space Gaussian IBP

Public API for the covariance-operator form of Gaussian IBP.
-/

export ProbabilityTheory
  (cmCoe_cmOfDual_innerSL_eq_covarianceOperator)

export ProbabilityTheory.IsGaussian
  (integral_inner_mul_eq_integral_fderiv_covarianceOperator_polyGrowth)

