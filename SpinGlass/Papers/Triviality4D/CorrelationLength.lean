import SpinGlass.Lattice.Zd
import SpinGlass.Lattice.Zd.Correlations
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.OrderClosed

/-!
# Correlation length `ξ` (paper-facing definition)

The 4D-triviality paper defines the (inverse) correlation length through an asymptotic logarithmic
decay rate, e.g. along the `e₁`-ray
\[
\xi = \lim_{n\to\infty} -n / \log \langle \sigma_0 ; \sigma_{n e_1}\rangle.
\]

In Lean, we bundle this as a **predicate** `IsCorrelationLength` with codomain `ℝ≥0∞`.
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
  ENNReal.ofReal (n : ℝ) / ENNReal.ofReal (-Real.log (g n))

lemma corrLenTerm_eq_of_neglog_pos {g : ℕ → ℝ} {n : ℕ} (h : 0 < -Real.log (g n)) :
    corrLenTerm (g := g) n = ENNReal.ofReal ((n : ℝ) / (-Real.log (g n))) := by
  unfold corrLenTerm
  simpa using
    (ENNReal.ofReal_div_of_pos (x := (n : ℝ)) (y := (-Real.log (g n))) h).symm

lemma le_exp_neg_div_of_corrLenTerm_le
    {g : ℕ → ℝ} {n : ℕ} {L : ℝ}
    (hgpos : 0 < g n) (hglt : g n < 1) (hLpos : 0 < L)
    (h : corrLenTerm (g := g) n ≤ ENNReal.ofReal L) :
    g n ≤ Real.exp (-((n : ℝ) / L)) := by
  have hneglog : 0 < -Real.log (g n) := by
    have : Real.log (g n) < 0 := (Real.log_neg_iff hgpos).2 hglt
    simpa using (neg_pos.2 this)
  have h' : (n : ℝ) / (-Real.log (g n)) ≤ L := by
    have hENN :
        ENNReal.ofReal ((n : ℝ) / (-Real.log (g n))) ≤ ENNReal.ofReal L := by
      simpa [corrLenTerm_eq_of_neglog_pos hneglog] using h
    exact (ENNReal.ofReal_le_ofReal_iff hLpos.le).1 hENN
  have hnle : (n : ℝ) ≤ L * (-Real.log (g n)) :=
    (div_le_iff₀ hneglog).1 h'
  have hnle' : (n : ℝ) ≤ (-Real.log (g n)) * L := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hnle
  have hdiv : (n : ℝ) / L ≤ -Real.log (g n) :=
    (div_le_iff₀ hLpos).2 hnle'
  have hlog : Real.log (g n) ≤ -((n : ℝ) / L) := by
    simpa using (neg_le_neg hdiv)
  have hexp : Real.exp (Real.log (g n)) ≤ Real.exp (-((n : ℝ) / L)) :=
    (Real.exp_le_exp).2 hlog
  simpa [Real.exp_log hgpos] using hexp

lemma exp_neg_div_le_of_le_corrLenTerm
    {g : ℕ → ℝ} {n : ℕ} {L : ℝ}
    (hgpos : 0 < g n) (hglt : g n < 1) (hLpos : 0 < L)
    (h : ENNReal.ofReal L ≤ corrLenTerm (g := g) n) :
    Real.exp (-((n : ℝ) / L)) ≤ g n := by
  have hneglog : 0 < -Real.log (g n) := by
    have : Real.log (g n) < 0 := (Real.log_neg_iff hgpos).2 hglt
    simpa using (neg_pos.2 this)
  have h' : L ≤ (n : ℝ) / (-Real.log (g n)) := by
    have hENN :
        ENNReal.ofReal L ≤ ENNReal.ofReal ((n : ℝ) / (-Real.log (g n))) := by
      simpa [corrLenTerm_eq_of_neglog_pos hneglog] using h
    exact (ENNReal.ofReal_le_ofReal_iff (by
      have : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
      exact div_nonneg this (le_of_lt hneglog))).1 hENN
  have hnle : L * (-Real.log (g n)) ≤ (n : ℝ) := by
    exact (le_div_iff₀ hneglog).1 h'
  have hnle' : (-Real.log (g n)) ≤ (n : ℝ) / L := by
    have hnle'' : (-Real.log (g n)) * L ≤ (n : ℝ) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hnle
    exact (le_div_iff₀ hLpos).2 hnle''
  have hlog : -((n : ℝ) / L) ≤ Real.log (g n) := by
    simpa using (neg_le_neg hnle')
  have hexp : Real.exp (-((n : ℝ) / L)) ≤ Real.exp (Real.log (g n)) :=
    (Real.exp_le_exp).2 hlog
  simpa [Real.exp_log hgpos] using hexp

/--
If `limsup corrLenTerm < L`, then eventually `g n ≤ exp (-n/L)` (under the standing positivity
assumptions `0 < g n < 1`).
-/
lemma eventually_le_exp_neg_div_of_limsup_corrLenTerm_lt
    {g : ℕ → ℝ} {L : ℝ}
    (hg : ∀ᶠ n : ℕ in atTop, 0 < g n ∧ g n < 1) (hLpos : 0 < L)
    (hL : Filter.limsup (fun n : ℕ => corrLenTerm (g := g) n) atTop < ENNReal.ofReal L) :
    ∀ᶠ n : ℕ in atTop, g n ≤ Real.exp (-((n : ℝ) / L)) := by
  have hterm :
      ∀ᶠ n : ℕ in atTop, corrLenTerm (g := g) n ≤ ENNReal.ofReal L :=
    (eventually_lt_of_limsup_lt hL).mono fun _ hn => le_of_lt hn
  filter_upwards [hg, hterm] with n hn hnt
  exact le_exp_neg_div_of_corrLenTerm_le (g := g) (n := n) hn.1 hn.2 hLpos hnt

/--
If `L < limsup corrLenTerm`, then frequently `exp (-n/L) ≤ g n` (again under `0 < g n < 1`).
-/
lemma frequently_exp_neg_div_le_of_lt_limsup_corrLenTerm
    {g : ℕ → ℝ} {L : ℝ}
    (hg : ∀ᶠ n : ℕ in atTop, 0 < g n ∧ g n < 1) (hLpos : 0 < L)
    (hL : ENNReal.ofReal L < Filter.limsup (fun n : ℕ => corrLenTerm (g := g) n) atTop) :
    ∃ᶠ n : ℕ in atTop, Real.exp (-((n : ℝ) / L)) ≤ g n := by
  have hfreq :
      ∃ᶠ n : ℕ in atTop, ENNReal.ofReal L < corrLenTerm (g := g) n :=
    frequently_lt_of_lt_limsup (u := fun n : ℕ => corrLenTerm (g := g) n) (h := hL)
  have hfreq' :
      ∃ᶠ n : ℕ in atTop, ENNReal.ofReal L ≤ corrLenTerm (g := g) n :=
    hfreq.mono fun _ hn => le_of_lt hn
  refine (hfreq'.and_eventually hg).mono ?_
  intro n hn
  exact exp_neg_div_le_of_le_corrLenTerm (g := g) (n := n) hn.2.1 hn.2.2 hLpos hn.1

/--
The (always-defined) `limsup`-based correlation length along a ray, as an element of `ℝ≥0∞`.

This is the canonical `def` one can attach to any input data. When the paper’s limit exists,
`IsCorrelationLength` identifies this value with the claimed limit.
-/
noncomputable def corrLenLimsup (x : ZLattice d) (i : Fin d) : ℝ≥0∞ :=
  Filter.limsup (fun n : ℕ =>
      corrLenTerm (g := truncTwoPointRay (d := d) (spin := spin) (μ := μ) x i) n) atTop

/-- The correlation length based at the origin along direction `i`, defined via `limsup`. -/
noncomputable abbrev corrLen0 (i : Fin d) : ℝ≥0∞ :=
  corrLenLimsup (d := d) (spin := spin) (μ := μ) (x := (0 : ZLattice d)) i

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

lemma corrLenLimsup_eq (h : IsCorrelationLength (d := d) (spin := spin) (μ := μ) x i ξ) :
    corrLenLimsup (d := d) (spin := spin) (μ := μ) x i = ξ := by
  simpa [corrLenLimsup] using (h.tendsto_corrLenTerm.limsup_eq)

lemma corrLen0_eq (h : IsCorrelationLength (d := d) (spin := spin) (μ := μ) (x := (0 : ZLattice d)) i ξ) :
    corrLen0 (d := d) (spin := spin) (μ := μ) i = ξ := by
  simpa [corrLen0] using (corrLenLimsup_eq (d := d) (spin := spin) (μ := μ) (x := (0 : ZLattice d)) (i := i) h)

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

lemma eventually_neglog_pos (h : IsCorrelationLength (d := d) (spin := spin) (μ := μ) x i ξ) :
    ∀ᶠ n in atTop, 0 < -Real.log (truncTwoPointRay (d := d) (spin := spin) (μ := μ) x i n) := by
  filter_upwards [h.eventually_log_neg] with n hn
  simpa using (neg_pos.2 hn)

lemma eventually_denom_ne_zero (h : IsCorrelationLength (d := d) (spin := spin) (μ := μ) x i ξ) :
    ∀ᶠ n in atTop, ENNReal.ofReal (-Real.log (truncTwoPointRay (d := d) (spin := spin) (μ := μ) x i n)) ≠ 0 := by
  filter_upwards [h.eventually_neglog_pos] with n hn
  intro h0
  have : (-Real.log (truncTwoPointRay (d := d) (spin := spin) (μ := μ) x i n)) ≤ 0 :=
    (ENNReal.ofReal_eq_zero).1 h0
  exact (not_le_of_gt hn) this

lemma eventually_corrLenTerm_ne_top (h : IsCorrelationLength (d := d) (spin := spin) (μ := μ) x i ξ) :
    ∀ᶠ n in atTop,
      corrLenTerm (g := truncTwoPointRay (d := d) (spin := spin) (μ := μ) x i) n ≠ ∞ := by
  filter_upwards [h.eventually_denom_ne_zero] with n hn0
  simpa [corrLenTerm] using (ENNReal.div_ne_top (x := (n : ℝ≥0∞)) (y := ENNReal.ofReal
    (-Real.log (truncTwoPointRay (d := d) (spin := spin) (μ := μ) x i n))) (by simp) hn0)

lemma eventually_lt_corrLenTerm_of_lt
    (h : IsCorrelationLength (d := d) (spin := spin) (μ := μ) x i ξ) {L : ℝ≥0∞} (hL : L < ξ) :
    ∀ᶠ n in atTop,
      L < corrLenTerm (g := truncTwoPointRay (d := d) (spin := spin) (μ := μ) x i) n :=
  h.tendsto_corrLenTerm.eventually (Ioi_mem_nhds hL)

lemma eventually_corrLenTerm_lt_of_lt
    (h : IsCorrelationLength (d := d) (spin := spin) (μ := μ) x i ξ) {L : ℝ≥0∞} (hL : ξ < L) :
    ∀ᶠ n in atTop,
      corrLenTerm (g := truncTwoPointRay (d := d) (spin := spin) (μ := μ) x i) n < L :=
  h.tendsto_corrLenTerm.eventually (Iio_mem_nhds hL)

lemma eventually_truncTwoPointRay_le_exp_neg_div_of_lt
    (h : IsCorrelationLength (d := d) (spin := spin) (μ := μ) x i ξ)
    {L : ℝ} (hLpos : 0 < L) (hξ : ξ < ENNReal.ofReal L) :
    ∀ᶠ n : ℕ in atTop,
      truncTwoPointRay (d := d) (spin := spin) (μ := μ) x i n ≤ Real.exp (-((n : ℝ) / L)) := by
  have hterm :
      ∀ᶠ n in atTop,
        corrLenTerm (g := truncTwoPointRay (d := d) (spin := spin) (μ := μ) x i) n ≤ ENNReal.ofReal L := by
    refine (h.eventually_corrLenTerm_lt_of_lt (L := ENNReal.ofReal L) hξ).mono ?_
    intro n hn
    exact le_of_lt hn
  filter_upwards [h.eventually_pos, h.eventually_lt_one, hterm] with n hnpos hnlt hnle
  exact
    le_exp_neg_div_of_corrLenTerm_le (g := truncTwoPointRay (d := d) (spin := spin) (μ := μ) x i)
      (n := n) hnpos hnlt hLpos hnle

lemma eventually_exp_neg_div_le_truncTwoPointRay_of_lt
    (h : IsCorrelationLength (d := d) (spin := spin) (μ := μ) x i ξ)
    {L : ℝ} (hLpos : 0 < L) (hξ : ENNReal.ofReal L < ξ) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (-((n : ℝ) / L)) ≤ truncTwoPointRay (d := d) (spin := spin) (μ := μ) x i n := by
  have hterm :
      ∀ᶠ n in atTop,
        ENNReal.ofReal L ≤ corrLenTerm (g := truncTwoPointRay (d := d) (spin := spin) (μ := μ) x i) n := by
    refine (h.eventually_lt_corrLenTerm_of_lt (L := ENNReal.ofReal L) hξ).mono ?_
    intro n hn
    exact le_of_lt hn
  filter_upwards [h.eventually_pos, h.eventually_lt_one, hterm] with n hnpos hnlt hnle
  exact
    exp_neg_div_le_of_le_corrLenTerm (g := truncTwoPointRay (d := d) (spin := spin) (μ := μ) x i)
      (n := n) hnpos hnlt hLpos hnle

end IsCorrelationLength

end

end SpinGlass.Papers.Triviality4D
