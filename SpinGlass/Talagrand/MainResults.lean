import SpinGlass.HopfieldConvolution
import SpinGlass.HopfieldLocalization
import SpinGlass.Cascades.GhirlandaGuerra
import SpinGlass.Replicas

/-!
# Talagrand Vol. I–II: main results index

Proved theorems and statement-layer `Prop`s. Plans: `Notes/Vol1##.md`, `Notes/Vol2##.md`.
-/

namespace SpinGlass

/-! ## Hopfield (Vol. I Ch. 4 / Vol. II Ch. 10) -/

-- §4.2 / Lemma 4.2.1: `hopfieldConvolution_overlapImage_talagrandGaussian_eq_withDensity_psi`
-- Thm 4.3.2: `SpinGlass.Cascades.HopfieldLocalizationLumps`
-- Vol. II Thm 10.3.1: `SpinGlass.Cascades.HopfieldLocalizationCenter`

/-! ## Ghirlanda–Guerra (Vol. II Ch. 12) -/

-- `GG1`, `GG1_prefix`, `GG1_prefix_of_condExp_lastReplica_ae`

/-! ## Guerra interpolation (Vol. I Ch. 1) -/

-- `hasDerivAt_nu` (Replicas)
-- Eq. (1.65): `guerra_derivative_bound_algebra_core`

end SpinGlass
