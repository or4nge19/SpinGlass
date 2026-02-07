import SpinGlass.Lattice.Zd
import SpinGlass.Lattice.Zd.Correlations

/-!
# Infrared bounds (interface layer)

This file provides paper-facing *predicates* for infrared-type bounds on two-point functions.

In the TeX, the x-space Infrared Bound (Eq. `\label{eq:IB}`) has the form
\[
S_{\rho,\beta}(x) \le \frac{C}{\beta |J|\,|x|^{d-2}},
\]
and in the GS setting an equivalent formulation includes the natural normalization
`⟨τ₀^2⟩ = S(0,0)` (Eq. `\label{eq:IB GS}`).

We do **not** prove any infrared bounds here yet; this is only the reusable statement layer.
-/

open scoped BigOperators

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Papers.Triviality4D

namespace InfraredBound

open SpinGlass.Lattice.Zd
open SpinGlass.Lattice.Zd.Correlations

variable {d : ℕ} {S : Type*} [MeasurableSpace S]
variable (spin : S → ℝ) (μ : Measure (ZLattice d → S))

/-- The \(ℓ^\infty\) “radius” of a lattice point, used as a stand-in for `|x|` in x-space bounds. -/
noncomputable def rInf (x : ZLattice d) : ℕ :=
  distInf d 0 x

lemma rInf_zero : rInf (d := d) (x := (0 : ZLattice d)) = 0 := by
  simp [rInf, distInf]

/--
An x-space infrared bound at dimension `d` expressed using `rInf`:
`twoPoint(0,x) ≤ C / rInf(x)^(d-2)` for `x ≠ 0`.

This is the qualitative form needed by the paper; quantitative constants (`β|J|`, etc.) can be
absorbed into `C` in interface statements.
-/
def HasInfraredBound : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ x : ZLattice d, x ≠ 0 →
      twoPoint (d := d) (spin := spin) (μ := μ) 0 x
        ≤ C / ((rInf (d := d) x : ℝ) ^ (d - 2))

/--
GS-normalized infrared bound (Eq. `\label{eq:IB GS}` style):
`twoPoint(0,x) ≤ C * twoPoint(0,0) / rInf(x)^(d-2)` for `x ≠ 0`.
-/
def HasInfraredBound_GS : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ x : ZLattice d, x ≠ 0 →
      twoPoint (d := d) (spin := spin) (μ := μ) 0 x
        ≤ (C * twoPoint (d := d) (spin := spin) (μ := μ) 0 0) /
            ((rInf (d := d) x : ℝ) ^ (d - 2))

end InfraredBound

end SpinGlass.Papers.Triviality4D

