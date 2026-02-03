import Common.Mathlib.Probability.Distributions.GaussianIntegrationByParts

/-!
# Gaussian integration by parts (public API)

This file is the **public-facing** entry point for the 1D Gaussian integration-by-parts (Stein)
toolkit in this repository.

For Mathlib upstreaming, downstream developments should prefer importing this file rather than the
implementation file `Common.Mathlib.Probability.Distributions.GaussianIntegrationByParts`.
-/

export ProbabilityTheory
  (stein_lemma_gaussianReal
   gaussianReal_integration_by_parts
   gaussianRV_integration_by_parts
   gaussian_integration_by_parts_general)
