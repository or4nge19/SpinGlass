import SpinGlass.Lattice.Zd
import GibbsMeasure.Observables.Correlations

/-!
# Correlation functions on `ℤ^d` configuration spaces

This file is a thin adapter layer: it specializes the model-agnostic correlation API from
`GibbsMeasure.Observables.Correlations` to configuration spaces of the form `ZLattice d → S`.

It exists so lattice-based papers can write `twoPoint (d := d) spin μ x y` etc. without threading
the explicit index type parameter `ι := ZLattice d` everywhere.
-/

open scoped BigOperators

open MeasureTheory ProbabilityTheory

namespace SpinGlass

namespace Lattice

namespace Zd

namespace Correlations

variable {d : ℕ} {S : Type*} [MeasurableSpace S]
variable (spin : S → ℝ)
variable (μ : Measure (ZLattice d → S))

/-- Real-valued spin at site `x` (specialized to `ZLattice d`). -/
def spinAt (x : ZLattice d) : (ZLattice d → S) → ℝ :=
  GibbsMeasure.Observables.Correlations.spinAt (ι := ZLattice d) spin x

omit [MeasurableSpace S] in
lemma spinAt_apply (x : ZLattice d) (η : ZLattice d → S) :
    spinAt (d := d) spin x η = spin (η x) := rfl

attribute [simp] spinAt_apply

/-! ### Core API: measurability -/

lemma measurable_spinAt {spin : S → ℝ} (hspin : Measurable spin) (x : ZLattice d) :
    Measurable (spinAt (d := d) spin x) := by
  simpa [spinAt] using
    (GibbsMeasure.Observables.Correlations.measurable_spinAt (ι := ZLattice d) (spin := spin) hspin x)

/-- One-point function `⟨σ_x⟩` on `ZLattice d`. -/
noncomputable def onePoint (x : ZLattice d) : ℝ :=
  GibbsMeasure.Observables.Correlations.onePoint (ι := ZLattice d) spin μ x

/-- Two-point function `⟨σ_x σ_y⟩` on `ZLattice d`. -/
noncomputable def twoPoint (x y : ZLattice d) : ℝ :=
  GibbsMeasure.Observables.Correlations.twoPoint (ι := ZLattice d) spin μ x y

lemma twoPoint_comm (x y : ZLattice d) :
    twoPoint (d := d) spin μ x y = twoPoint (d := d) spin μ y x := by
  simpa [twoPoint] using
    (GibbsMeasure.Observables.Correlations.twoPoint_comm (ι := ZLattice d) (spin := spin) (μ := μ) x y)

lemma twoPoint_self (x : ZLattice d) :
    twoPoint (d := d) spin μ x x =
      ∫ η, (spinAt (d := d) spin x η) ^ (2 : ℕ) ∂μ := by
  simpa [twoPoint, spinAt] using
    (GibbsMeasure.Observables.Correlations.twoPoint_self (ι := ZLattice d) (spin := spin) (μ := μ) x)

/--
Truncated / connected two-point function
`⟨σ_x ; σ_y⟩ := ⟨σ_x σ_y⟩ - ⟨σ_x⟩⟨σ_y⟩` on `ZLattice d`.
-/
noncomputable def truncTwoPoint (x y : ZLattice d) : ℝ :=
  GibbsMeasure.Observables.Correlations.truncTwoPoint (ι := ZLattice d) spin μ x y

lemma truncTwoPoint_comm (x y : ZLattice d) :
    truncTwoPoint (d := d) spin μ x y = truncTwoPoint (d := d) spin μ y x := by
  simpa [truncTwoPoint] using
    (GibbsMeasure.Observables.Correlations.truncTwoPoint_comm
      (ι := ZLattice d) (spin := spin) (μ := μ) x y)

/-- Four-point function `⟨σ_x σ_y σ_z σ_t⟩` on `ZLattice d`. -/
noncomputable def fourPoint (x y z t : ZLattice d) : ℝ :=
  GibbsMeasure.Observables.Correlations.fourPoint (ι := ZLattice d) spin μ x y z t

lemma fourPoint_comm_xy (x y z t : ZLattice d) :
    fourPoint (d := d) spin μ x y z t = fourPoint (d := d) spin μ y x z t := by
  simpa [fourPoint] using
    (GibbsMeasure.Observables.Correlations.fourPoint_comm_xy
      (ι := ZLattice d) (spin := spin) (μ := μ) x y z t)

/-- The 4-point Ursell function (connected 4-point function) on `ZLattice d`. -/
noncomputable def ursell4 (x y z t : ZLattice d) : ℝ :=
  GibbsMeasure.Observables.Correlations.ursell4 (ι := ZLattice d) spin μ x y z t

lemma ursell4_comm_xy (x y z t : ZLattice d) :
    ursell4 (d := d) spin μ x y z t = ursell4 (d := d) spin μ y x z t := by
  simpa [ursell4] using
    (GibbsMeasure.Observables.Correlations.ursell4_comm_xy
      (ι := ZLattice d) (spin := spin) (μ := μ) x y z t)

end Correlations

end Zd

end Lattice

end SpinGlass

