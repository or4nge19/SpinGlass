import SpinGlass.HopfieldConvolution
import SpinGlass.HopfieldLocalization
import SpinGlass.Cascades.GhirlandaGuerra
import SpinGlass.Replicas

/-!
# Talagrand Vol I/II: main results index (work-in-progress)

This module is an **index** of the statement/proof objects corresponding to the “main results”
flagged in:

- `Notes/BovierGayrard.md`
- `Notes/Vol1-Vol2.md`
- `Notes/Talagrand/`

The philosophy is:

- whenever a result is already proved, we re-export the theorem;
- whenever only the *statement layer* is in place so far (e.g. Hopfield localization), we expose
  the canonical `Prop` representing the result in a Vol II kernel/law shape.
-/

namespace SpinGlass

/-! ## Hopfield (Talagrand Vol I Ch.4 / Vol II Ch.10) -/

-- Talagrand §4.2 / Lemma 4.2.1: ψ-density formula for the Gaussian-convolved overlap law.
-- See `SpinGlass/HopfieldConvolution.lean`:
--   `hopfieldConvolution_overlapImage_talagrandGaussian_eq_withDensity_psi`
-- and the normalization lemma:
--   `lintegral_hopfieldPsi_density_eq_one`.

-- Bovier–Gayrard / Talagrand Vol I Thm 4.3.2, in annealed overlap-law form:
-- See `SpinGlass/HopfieldLocalization.lean`:
--   `SpinGlass.Cascades.HopfieldLocalizationLumps`.

-- Talagrand Vol II Thm 10.3.1, in annealed overlap-law form:
-- See `SpinGlass/HopfieldLocalization.lean`:
--   `SpinGlass.Cascades.HopfieldLocalizationCenter`.

/-! ## Ghirlanda–Guerra (Talagrand Vol II Ch.12) -/

-- Structural GG₁ predicate on a replica law, and its conditional-expectation interface:
-- `SpinGlass.Cascades.GG1`, `SpinGlass.Cascades.GG1_prefix`,
-- `SpinGlass.Cascades.GG1_prefix_of_condExp_lastReplica_ae`.
--
-- Note: model-specific proofs of GG₁ identities will live in dedicated files (e.g. SK via Gaussian IBP).

/-! ## Guerra interpolation / Vol I Chapter 1 engine -/

-- Differentiation under the disorder expectation for the replica functional `nu`:
-- `SpinGlass.hasDerivAt_nu` in `SpinGlass/Replicas.lean`.
--
-- The algebraic core inequality (Talagrand Eq. 1.65):
-- `SpinGlass.guerra_derivative_bound_algebra_core` in `SpinGlass/GuerraBound.lean`.

end SpinGlass

