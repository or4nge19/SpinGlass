/-
Copyright (c) 2026 Maria Grazia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maria Grazia
-/

import Common.Mathlib.Probability.Distributions.Gaussian_IBP_Hilbert

/-!
# Gaussian integration by parts on Hilbert spaces: public API

This file is the public-facing entry point for the Hilbert-space covariance-operator formulation
of Gaussian integration by parts.

Downstream developments should import this file (or
`Common.Mathlib.Probability.Distributions.Gaussian.IntegrationByParts`), rather than relying on any
coordinate model.
-/

export ProbabilityTheory
  (cmCoe_cmOfDual_innerSL_eq_covarianceOperator)

export ProbabilityTheory.IsGaussian
  (integral_inner_mul_eq_integral_fderiv_covarianceOperator_polyGrowth)

