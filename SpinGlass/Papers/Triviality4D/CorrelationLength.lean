import SpinGlass.Lattice.Zd
import SpinGlass.Lattice.Zd.Correlations
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Correlation length `ξ` (paper-facing definition)

The 4D-triviality paper defines the (inverse) correlation length through an asymptotic logarithmic
decay rate, e.g. along the `e₁`-ray
\[
\xi = \lim_{n\to\infty} -n / \log \langle \sigma_0 ; \sigma_{n e_1}\rangle.
\]

In Lean, we package this as a **predicate** `IsCorrelationLength` with codomain `ℝ≥0∞`.
This avoids committing to existence/uniqueness of the limit as a global `def`, and it makes the
required positivity assumptions explicit.
-/

open scoped BigOperators Topology ENNReal

open MeasureTheory ProbabilityTheory Filter Topology Real

namespace SpinGlass.Papers.Triviality4D

open SpinGlass.Lattice.Zd
open SpinGlass.Lattice.Zd.Correlations

universe u

section

variable {d : ℕ} {S : Type u} [MeasurableSpace S]
variable (spin : S → ℝ) (μ : Measure (ZLattice d → S))

/-- The truncated two-point function along the ray `x + n·e_i`. -/
noncomputable def truncTwoPointRay (x : ZLattice d) (i : Fin d) : ℕ → ℝ :=
  fun n => truncTwoPoint (d := d) spin μ x (x + n • stdBasis i)

/-- The `n`-th term in the correlation length limit, for a positive sequence `g`. -/
noncomputable def corrLenTerm (g : ℕ → ℝ) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((n : ℝ) / (-Real.log (g n)))

/--
`IsCorrelationLength spin μ x i ξ` means: along the ray `x + n·e_i`, the truncated two-point
function is eventually in `(0,1)`, and the paper’s correlation-length expression converges to `ξ`.

We work in `ℝ≥0∞` to allow the critical case `ξ = ∞`.
-/
def IsCorrelationLength (x : ZLattice d) (i : Fin d) (ξ : ℝ≥0∞) : Prop :=
  (∀ᶠ n in atTop, 0 < truncTwoPointRay (d := d) (spin := spin) (μ := μ) x i n ∧
      truncTwoPointRay (d := d) (spin := spin) (μ := μ) x i n < 1) ∧
    Tendsto (fun n : ℕ =>
        corrLenTerm (g := truncTwoPointRay (d := d) (spin := spin) (μ := μ) x i) n) atTop (𝓝 ξ)

namespace IsCorrelationLength

variable {spin : S → ℝ} {μ : Measure (ZLattice d → S)}
variable {x : ZLattice d} {i : Fin d} {ξ ξ' : ℝ≥0∞}

lemma eventually_pos (h : IsCorrelationLength (d := d) (spin := spin) (μ := μ) x i ξ) :
    ∀ᶠ n in atTop, 0 < truncTwoPointRay (d := d) (spin := spin) (μ := μ) x i n :=
  h.1.mono fun _ hn => hn.1

lemma eventually_lt_one (h : IsCorrelationLength (d := d) (spin := spin) (μ := μ) x i ξ) :
    ∀ᶠ n in atTop, truncTwoPointRay (d := d) (spin := spin) (μ := μ) x i n < 1 :=
  h.1.mono fun _ hn => hn.2

lemma tendsto_corrLenTerm (h : IsCorrelationLength (d := d) (spin := spin) (μ := μ) x i ξ) :
    Tendsto (fun n : ℕ =>
        corrLenTerm (g := truncTwoPointRay (d := d) (spin := spin) (μ := μ) x i) n) atTop (𝓝 ξ) :=
  h.2

lemma unique
    (h : IsCorrelationLength (d := d) (spin := spin) (μ := μ) x i ξ)
    (h' : IsCorrelationLength (d := d) (spin := spin) (μ := μ) x i ξ') :
    ξ = ξ' :=
  tendsto_nhds_unique h.tendsto_corrLenTerm h'.tendsto_corrLenTerm

lemma eventually_log_neg (h : IsCorrelationLength (d := d) (spin := spin) (μ := μ) x i ξ) :
    ∀ᶠ n in atTop, Real.log (truncTwoPointRay (d := d) (spin := spin) (μ := μ) x i n) < 0 := by
  have hpos := h.eventually_pos
  have hlt := h.eventually_lt_one
  filter_upwards [hpos, hlt] with n hnpos hnlt
  exact (Real.log_neg_iff hnpos).2 hnlt

end IsCorrelationLength

end

end SpinGlass.Papers.Triviality4D

