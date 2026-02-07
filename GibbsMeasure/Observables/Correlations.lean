import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Probability.Distributions.Gaussian.Basic

/-!
# Correlation functions and basic diagrams for spin systems

This file provides reusable, model-agnostic definitions on configuration spaces of the form
`ι → S` equipped with a probability measure `μ`, together with a real-valued “spin” map
`spin : S → ℝ`.

The main definitions are:
- `spinAt`, `onePoint`, `twoPoint`, `truncTwoPoint`,
- `fourPoint`, `ursell4`,
- basic diagrammatic sums over a finite region `Λ : Finset ι`: `bubbleRaw`, `bubble`, `chi`.

Implementation note:
these are *interfaces* suitable for stating research-level results. They deliberately avoid hardcoding
in any geometry on `ι` (boxes/balls/etc.), which should be supplied by the caller.
-/

open scoped BigOperators

open MeasureTheory ProbabilityTheory

namespace GibbsMeasure

namespace Observables

namespace Correlations

variable {ι : Type*} {S : Type*} [MeasurableSpace S]
variable (spin : S → ℝ)
variable (μ : Measure (ι → S))

/-- Real-valued spin at site `x`. -/
def spinAt (x : ι) : (ι → S) → ℝ :=
  fun η => spin (η x)

omit [MeasurableSpace S] in
lemma spinAt_apply (x : ι) (η : ι → S) : spinAt (ι := ι) spin x η = spin (η x) := rfl

attribute [simp] spinAt_apply

/-! ### Core API: measurability of basic observables -/

lemma measurable_spinAt {spin : S → ℝ} (hspin : Measurable spin) (x : ι) :
    Measurable (spinAt (ι := ι) spin x) := by
  simpa [spinAt] using hspin.comp (measurable_pi_apply x)

/-- One-point function `⟨σ_x⟩`. -/
noncomputable def onePoint (x : ι) : ℝ :=
  ∫ η, spinAt (ι := ι) spin x η ∂μ

/-- Two-point function `⟨σ_x σ_y⟩`. -/
noncomputable def twoPoint (x y : ι) : ℝ :=
  ∫ η, spinAt (ι := ι) spin x η * spinAt (ι := ι) spin y η ∂μ

/-! ### Core API: basic symmetries -/

lemma twoPoint_comm (x y : ι) :
    twoPoint (ι := ι) spin μ x y = twoPoint (ι := ι) spin μ y x := by
  simp [twoPoint, mul_comm]

lemma twoPoint_self (x : ι) :
    twoPoint (ι := ι) spin μ x x = ∫ η, (spinAt (ι := ι) spin x η) ^ (2 : ℕ) ∂μ := by
  simp [twoPoint, pow_two]

/--
Truncated / connected two-point function
`⟨σ_x ; σ_y⟩ := ⟨σ_x σ_y⟩ - ⟨σ_x⟩⟨σ_y⟩`.
-/
noncomputable def truncTwoPoint (x y : ι) : ℝ :=
  twoPoint (ι := ι) spin μ x y - onePoint (ι := ι) spin μ x * onePoint (ι := ι) spin μ y

lemma truncTwoPoint_comm (x y : ι) :
    truncTwoPoint (ι := ι) spin μ x y = truncTwoPoint (ι := ι) spin μ y x := by
  simp [truncTwoPoint, twoPoint_comm (ι := ι) (spin := spin) (μ := μ), mul_comm]

/-- Four-point function `⟨σ_x σ_y σ_z σ_t⟩`. -/
noncomputable def fourPoint (x y z t : ι) : ℝ :=
  ∫ η,
    spinAt (ι := ι) spin x η *
      spinAt (ι := ι) spin y η *
      spinAt (ι := ι) spin z η *
      spinAt (ι := ι) spin t η ∂μ

lemma fourPoint_comm_xy (x y z t : ι) :
    fourPoint (ι := ι) spin μ x y z t = fourPoint (ι := ι) spin μ y x z t := by
  simp [fourPoint, mul_left_comm, mul_assoc]

/-- The 4-point Ursell function \(U_4\) (connected 4-point function). -/
noncomputable def ursell4 (x y z t : ι) : ℝ :=
  fourPoint (ι := ι) spin μ x y z t
    - (twoPoint (ι := ι) spin μ x y * twoPoint (ι := ι) spin μ z t
        + twoPoint (ι := ι) spin μ x z * twoPoint (ι := ι) spin μ y t
        + twoPoint (ι := ι) spin μ x t * twoPoint (ι := ι) spin μ y z)

lemma ursell4_comm_xy (x y z t : ι) :
    ursell4 (ι := ι) spin μ x y z t = ursell4 (ι := ι) spin μ y x z t := by
  simp [ursell4, fourPoint_comm_xy (ι := ι) (spin := spin) (μ := μ),
    twoPoint_comm (ι := ι) (spin := spin) (μ := μ),
    add_comm, add_left_comm, mul_comm]

/-!
## Finite linear combinations and moment expansions

The scaling-limit literature constantly uses identities like
\[
\mathbb E\Big[\Big(\sum_{x\in\Lambda} a_x \sigma_x\Big)^2\Big]
= \sum_{x,y\in\Lambda} a_x a_y \,\mathbb E[\sigma_x \sigma_y].
\]

These are purely algebraic, but in Lean they require `Integrable` hypotheses to justify commuting
finite sums with the Bochner integral.
-/

section LinearCombination

variable (Λ : Finset ι) (a : ι → ℝ)

/-- Finite linear combination of spins over `Λ` with weights `a`. -/
noncomputable def linComb : (ι → S) → ℝ :=
  fun η => ∑ x ∈ Λ, a x * spinAt (ι := ι) spin x η

omit [MeasurableSpace S] in
lemma linComb_apply (η : ι → S) :
    linComb (ι := ι) (spin := spin) Λ a η = ∑ x ∈ Λ, a x * spin (η x) := by
  simp [linComb, spinAt]

lemma integral_linComb_sq_eq_sum_twoPoint
    (hI : ∀ x ∈ Λ, ∀ y ∈ Λ,
      Integrable (fun η : ι → S =>
        spinAt (ι := ι) spin x η * spinAt (ι := ι) spin y η) μ) :
    (∫ η, (linComb (ι := ι) (spin := spin) Λ a η) ^ (2 : ℕ) ∂μ)
      =
      ∑ x ∈ Λ, ∑ y ∈ Λ, a x * a y * twoPoint (ι := ι) spin μ x y := by
  have h1 :
      (fun η : ι → S => (linComb (ι := ι) (spin := spin) Λ a η) ^ (2 : ℕ))
        =
      (fun η : ι → S =>
        ∑ x ∈ Λ, ∑ y ∈ Λ,
          (a x * spinAt (ι := ι) spin x η) * (a y * spinAt (ι := ι) spin y η)) := by
    funext η
    simp [linComb, pow_two, Finset.sum_mul_sum]
  have hXY : ∀ x ∈ Λ, ∀ y ∈ Λ,
      Integrable (fun η : ι → S =>
        (a x * spinAt (ι := ι) spin x η) * (a y * spinAt (ι := ι) spin y η)) μ := by
    intro x hx y hy
    have hxy : Integrable (fun η : ι → S =>
        spinAt (ι := ι) spin x η * spinAt (ι := ι) spin y η) μ :=
      hI x hx y hy
    have : Integrable (fun η : ι → S =>
        (a x * a y) * (spinAt (ι := ι) spin x η * spinAt (ι := ι) spin y η)) μ :=
      hxy.const_mul (a x * a y)
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  have hInner : ∀ x ∈ Λ,
      Integrable (fun η : ι → S =>
        ∑ y ∈ Λ,
          (a x * spinAt (ι := ι) spin x η) * (a y * spinAt (ι := ι) spin y η)) μ := by
    intro x hx
    have : ∀ y ∈ Λ,
        Integrable (fun η : ι → S =>
          (a x * spinAt (ι := ι) spin x η) * (a y * spinAt (ι := ι) spin y η)) μ :=
      fun y hy => hXY x hx y hy
    simpa using
      (integrable_finset_sum (μ := μ) (s := Λ)
        (f := fun y η =>
          (a x * spinAt (ι := ι) spin x η) * (a y * spinAt (ι := ι) spin y η)) this)
  calc
    (∫ η, (linComb (ι := ι) (spin := spin) Λ a η) ^ (2 : ℕ) ∂μ)
        = ∫ η, (∑ x ∈ Λ, ∑ y ∈ Λ,
            (a x * spinAt (ι := ι) spin x η) * (a y * spinAt (ι := ι) spin y η)) ∂μ := by
            simp [h1]
    _ = ∑ x ∈ Λ, ∫ η, (∑ y ∈ Λ,
            (a x * spinAt (ι := ι) spin x η) * (a y * spinAt (ι := ι) spin y η)) ∂μ := by
            simpa using
              (integral_finset_sum (μ := μ) (s := Λ)
                (f := fun x η => ∑ y ∈ Λ,
                  (a x * spinAt (ι := ι) spin x η) * (a y * spinAt (ι := ι) spin y η)) hInner)
    _ = ∑ x ∈ Λ, ∑ y ∈ Λ,
          ∫ η, (a x * spinAt (ι := ι) spin x η) * (a y * spinAt (ι := ι) spin y η) ∂μ := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          have hThis : ∀ y ∈ Λ,
              Integrable (fun η : ι → S =>
                (a x * spinAt (ι := ι) spin x η) * (a y * spinAt (ι := ι) spin y η)) μ :=
            fun y hy => hXY x hx y hy
          simpa using
            (integral_finset_sum (μ := μ) (s := Λ)
              (f := fun y η =>
                (a x * spinAt (ι := ι) spin x η) * (a y * spinAt (ι := ι) spin y η)) hThis)
    _ = ∑ x ∈ Λ, ∑ y ∈ Λ, a x * a y * twoPoint (ι := ι) spin μ x y := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          refine Finset.sum_congr rfl ?_
          intro y hy
          have :
              (∫ η, (a x * spinAt (ι := ι) spin x η) * (a y * spinAt (ι := ι) spin y η) ∂μ)
                =
              (a x * a y) * (∫ η, spinAt (ι := ι) spin x η * spinAt (ι := ι) spin y η ∂μ) := by
            simp [mul_assoc, mul_left_comm, mul_comm, integral_const_mul]
          simpa [twoPoint, mul_assoc] using this

lemma integral_linComb_pow_four_eq_sum_fourPoint
    (hI : ∀ x ∈ Λ, ∀ y ∈ Λ, ∀ z ∈ Λ, ∀ t ∈ Λ,
      Integrable (fun η : ι → S =>
        spinAt (ι := ι) spin x η * spinAt (ι := ι) spin y η *
          spinAt (ι := ι) spin z η * spinAt (ι := ι) spin t η) μ) :
    (∫ η, (linComb (ι := ι) (spin := spin) Λ a η) ^ (4 : ℕ) ∂μ)
      =
      ∑ x ∈ Λ, ∑ y ∈ Λ, ∑ z ∈ Λ, ∑ t ∈ Λ,
        a x * a y * a z * a t * fourPoint (ι := ι) spin μ x y z t := by
  let A : ι → (ι → S) → ℝ := fun x η => a x * spinAt (ι := ι) spin x η
  have hpow4 :
      (fun η : ι → S => (linComb (ι := ι) (spin := spin) Λ a η) ^ (4 : ℕ))
        =
      (fun η : ι → S =>
        ∑ x ∈ Λ, ∑ y ∈ Λ, ∑ z ∈ Λ, ∑ t ∈ Λ,
          (A x η) * (A y η) * (A z η) * (A t η)) := by
    funext η
    have hpow :
        (∑ x ∈ Λ, A x η) ^ (4 : ℕ)
          =
        ∑ x ∈ Λ, ∑ y ∈ Λ, ∑ z ∈ Λ, ∑ t ∈ Λ, (A x η) * (A y η) * (A z η) * (A t η) := by
      have hpow' :
          (∑ x ∈ Λ, A x η) ^ (4 : ℕ)
            =
          (∑ x ∈ Λ, A x η) ^ (2 : ℕ) * (∑ x ∈ Λ, A x η) ^ (2 : ℕ) := by
        simpa [show (2 + 2 : ℕ) = 4 by decide] using
          (pow_add (∑ x ∈ Λ, A x η) (2 : ℕ) (2 : ℕ))
      calc
        (∑ x ∈ Λ, A x η) ^ (4 : ℕ)
            = (∑ x ∈ Λ, A x η) ^ (2 : ℕ) * (∑ x ∈ Λ, A x η) ^ (2 : ℕ) := hpow'
        _ = ((∑ x ∈ Λ, A x η) * (∑ y ∈ Λ, A y η)) * ((∑ z ∈ Λ, A z η) * (∑ t ∈ Λ, A t η)) := by
              simp [pow_two, mul_assoc]
        _ = (∑ p ∈ Λ ×ˢ Λ, A p.1 η * A p.2 η) * (∑ q ∈ Λ ×ˢ Λ, A q.1 η * A q.2 η) := by
              simp [Finset.sum_mul_sum, Finset.sum_product]
        _ = ∑ p ∈ Λ ×ˢ Λ, ∑ q ∈ Λ ×ˢ Λ, (A p.1 η * A p.2 η) * (A q.1 η * A q.2 η) := by
              simp [Finset.sum_mul_sum]
        _ = ∑ x ∈ Λ, ∑ y ∈ Λ, ∑ z ∈ Λ, ∑ t ∈ Λ, (A x η * A y η) * (A z η * A t η) := by
              simp [Finset.sum_product]
        _ = ∑ x ∈ Λ, ∑ y ∈ Λ, ∑ z ∈ Λ, ∑ t ∈ Λ, A x η * A y η * A z η * A t η := by
              simp [mul_assoc]
    simpa [linComb, A, spinAt, mul_assoc, mul_left_comm, mul_comm] using hpow
  have hInt : ∀ x ∈ Λ, ∀ y ∈ Λ, ∀ z ∈ Λ, ∀ t ∈ Λ,
      Integrable (fun η : ι → S => (A x η) * (A y η) * (A z η) * (A t η)) μ := by
    intro x hx y hy z hz t ht
    have hxyzt :
        Integrable (fun η : ι → S =>
          spinAt (ι := ι) spin x η * spinAt (ι := ι) spin y η *
            spinAt (ι := ι) spin z η * spinAt (ι := ι) spin t η) μ :=
      hI x hx y hy z hz t ht
    have :
        Integrable (fun η : ι → S =>
          (a x * a y * a z * a t) *
            (spinAt (ι := ι) spin x η * spinAt (ι := ι) spin y η *
              spinAt (ι := ι) spin z η * spinAt (ι := ι) spin t η)) μ :=
      hxyzt.const_mul (a x * a y * a z * a t)
    simpa [A, mul_assoc, mul_left_comm, mul_comm] using this
  have hInner3 : ∀ x ∈ Λ, ∀ y ∈ Λ, ∀ z ∈ Λ,
      Integrable (fun η : ι → S =>
        ∑ t ∈ Λ, (A x η) * (A y η) * (A z η) * (A t η)) μ := by
    intro x hx y hy z hz
    have : ∀ t ∈ Λ, Integrable (fun η : ι → S =>
        (A x η) * (A y η) * (A z η) * (A t η)) μ := fun t ht =>
      hInt x hx y hy z hz t ht
    simpa using
      (integrable_finset_sum (μ := μ) (s := Λ)
        (f := fun t η => (A x η) * (A y η) * (A z η) * (A t η)) this)

  have hInner2 : ∀ x ∈ Λ, ∀ y ∈ Λ,
      Integrable (fun η : ι → S =>
        ∑ z ∈ Λ, ∑ t ∈ Λ, (A x η) * (A y η) * (A z η) * (A t η)) μ := by
    intro x hx y hy
    have : ∀ z ∈ Λ, Integrable (fun η : ι → S =>
        ∑ t ∈ Λ, (A x η) * (A y η) * (A z η) * (A t η)) μ := fun z hz =>
      hInner3 x hx y hy z hz
    simpa using
      (integrable_finset_sum (μ := μ) (s := Λ)
        (f := fun z η => ∑ t ∈ Λ, (A x η) * (A y η) * (A z η) * (A t η)) this)

  have hInner1 : ∀ x ∈ Λ,
      Integrable (fun η : ι → S =>
        ∑ y ∈ Λ, ∑ z ∈ Λ, ∑ t ∈ Λ, (A x η) * (A y η) * (A z η) * (A t η)) μ := by
    intro x hx
    have : ∀ y ∈ Λ, Integrable (fun η : ι → S =>
        ∑ z ∈ Λ, ∑ t ∈ Λ, (A x η) * (A y η) * (A z η) * (A t η)) μ := fun y hy =>
      hInner2 x hx y hy
    simpa using
      (integrable_finset_sum (μ := μ) (s := Λ)
        (f := fun y η => ∑ z ∈ Λ, ∑ t ∈ Λ, (A x η) * (A y η) * (A z η) * (A t η)) this)

  -- Now commute integral with the four sums.
  calc
    (∫ η, (linComb (ι := ι) (spin := spin) Λ a η) ^ (4 : ℕ) ∂μ)
        = ∫ η, (∑ x ∈ Λ, ∑ y ∈ Λ, ∑ z ∈ Λ, ∑ t ∈ Λ,
            (A x η) * (A y η) * (A z η) * (A t η)) ∂μ := by
            simp [hpow4]
    _ = ∑ x ∈ Λ, ∫ η, (∑ y ∈ Λ, ∑ z ∈ Λ, ∑ t ∈ Λ,
            (A x η) * (A y η) * (A z η) * (A t η)) ∂μ := by
            simpa using
              (integral_finset_sum (μ := μ) (s := Λ)
                (f := fun x η => ∑ y ∈ Λ, ∑ z ∈ Λ, ∑ t ∈ Λ,
                  (A x η) * (A y η) * (A z η) * (A t η)) hInner1)
    _ = ∑ x ∈ Λ, ∑ y ∈ Λ, ∫ η, (∑ z ∈ Λ, ∑ t ∈ Λ,
            (A x η) * (A y η) * (A z η) * (A t η)) ∂μ := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          have : ∀ y ∈ Λ, Integrable (fun η : ι → S =>
              ∑ z ∈ Λ, ∑ t ∈ Λ, (A x η) * (A y η) * (A z η) * (A t η)) μ :=
            fun y hy => hInner2 x hx y hy
          simpa using
            (integral_finset_sum (μ := μ) (s := Λ)
              (f := fun y η => ∑ z ∈ Λ, ∑ t ∈ Λ,
                (A x η) * (A y η) * (A z η) * (A t η)) this)
    _ = ∑ x ∈ Λ, ∑ y ∈ Λ, ∑ z ∈ Λ, ∫ η, (∑ t ∈ Λ,
            (A x η) * (A y η) * (A z η) * (A t η)) ∂μ := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          refine Finset.sum_congr rfl ?_
          intro y hy
          have : ∀ z ∈ Λ, Integrable (fun η : ι → S =>
              ∑ t ∈ Λ, (A x η) * (A y η) * (A z η) * (A t η)) μ :=
            fun z hz => hInner3 x hx y hy z hz
          simpa using
            (integral_finset_sum (μ := μ) (s := Λ)
              (f := fun z η => ∑ t ∈ Λ, (A x η) * (A y η) * (A z η) * (A t η)) this)
    _ = ∑ x ∈ Λ, ∑ y ∈ Λ, ∑ z ∈ Λ, ∑ t ∈ Λ,
          ∫ η, (A x η) * (A y η) * (A z η) * (A t η) ∂μ := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          refine Finset.sum_congr rfl ?_
          intro y hy
          refine Finset.sum_congr rfl ?_
          intro z hz
          have : ∀ t ∈ Λ, Integrable (fun η : ι → S =>
              (A x η) * (A y η) * (A z η) * (A t η)) μ :=
            fun t ht => hInt x hx y hy z hz t ht
          simpa using
            (integral_finset_sum (μ := μ) (s := Λ)
              (f := fun t η => (A x η) * (A y η) * (A z η) * (A t η)) this)
    _ = ∑ x ∈ Λ, ∑ y ∈ Λ, ∑ z ∈ Λ, ∑ t ∈ Λ,
          a x * a y * a z * a t * fourPoint (ι := ι) spin μ x y z t := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          refine Finset.sum_congr rfl ?_
          intro y hy
          refine Finset.sum_congr rfl ?_
          intro z hz
          refine Finset.sum_congr rfl ?_
          intro t ht
          have :
              (∫ η, (A x η) * (A y η) * (A z η) * (A t η) ∂μ)
                =
              (a x * a y * a z * a t) *
                (∫ η, spinAt (ι := ι) spin x η * spinAt (ι := ι) spin y η *
                  spinAt (ι := ι) spin z η * spinAt (ι := ι) spin t η ∂μ) := by
            simp [A, mul_assoc, mul_left_comm, mul_comm, integral_const_mul]
          simpa [fourPoint, mul_assoc, mul_left_comm, mul_comm] using this

lemma sum_ursell4_eq_sum_fourPoint_sub_three_mul_sq_sum_twoPoint :
    (∑ x ∈ Λ, ∑ y ∈ Λ, ∑ z ∈ Λ, ∑ t ∈ Λ,
        a x * a y * a z * a t * ursell4 (ι := ι) spin μ x y z t)
      =
      (∑ x ∈ Λ, ∑ y ∈ Λ, ∑ z ∈ Λ, ∑ t ∈ Λ,
        a x * a y * a z * a t * fourPoint (ι := ι) spin μ x y z t)
        - 3 * (∑ x ∈ Λ, ∑ y ∈ Λ, a x * a y * twoPoint (ι := ι) spin μ x y) ^ (2 : ℕ) := by
  let sum4 : (ι → ι → ι → ι → ℝ) → ℝ := fun F =>
    ∑ x ∈ Λ, ∑ y ∈ Λ, ∑ z ∈ Λ, ∑ t ∈ Λ, F x y z t
  have sum4_add (F G : ι → ι → ι → ι → ℝ) :
      sum4 (fun x y z t => F x y z t + G x y z t) = sum4 F + sum4 G := by
    simp [sum4, Finset.sum_add_distrib]
  have sum4_sub (F G : ι → ι → ι → ι → ℝ) :
      sum4 (fun x y z t => F x y z t - G x y z t) = sum4 F - sum4 G := by
    simp [sum4, Finset.sum_sub_distrib]
  -- Abbreviations: the weighted 2-point sum and the three pairing kernels.
  let S2 : ℝ := ∑ x ∈ Λ, ∑ y ∈ Λ, a x * a y * twoPoint (ι := ι) spin μ x y
  let F4 : ι → ι → ι → ι → ℝ := fun x y z t =>
    a x * a y * a z * a t * fourPoint (ι := ι) spin μ x y z t
  let Pxyzt : ι → ι → ι → ι → ℝ := fun x y z t =>
    a x * a y * a z * a t * (twoPoint (ι := ι) spin μ x y * twoPoint (ι := ι) spin μ z t)
  let Pxzyt : ι → ι → ι → ι → ℝ := fun x y z t =>
    a x * a y * a z * a t * (twoPoint (ι := ι) spin μ x z * twoPoint (ι := ι) spin μ y t)
  let Pxtyz : ι → ι → ι → ι → ℝ := fun x y z t =>
    a x * a y * a z * a t * (twoPoint (ι := ι) spin μ x t * twoPoint (ι := ι) spin μ y z)
  have hPxzyt : sum4 Pxzyt = S2 ^ (2 : ℕ) := by
    simp [sum4, Pxzyt, S2, pow_two, Finset.sum_mul_sum, mul_assoc, mul_left_comm]
  have hPxyzt : sum4 Pxyzt = sum4 Pxzyt := by
    unfold sum4 Pxyzt Pxzyt
    refine Finset.sum_congr rfl ?_
    intro x hx
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (Finset.sum_comm (s := Λ) (t := Λ)
        (f := fun y z =>
          ∑ t ∈ Λ,
            a x * a y * a z * a t *
              (twoPoint (ι := ι) spin μ x z * twoPoint (ι := ι) spin μ y t))).symm
  have hPxtyz : sum4 Pxtyz = sum4 Pxzyt := by
    unfold sum4 Pxtyz Pxzyt
    refine Finset.sum_congr rfl ?_
    intro x hx
    refine Finset.sum_congr rfl ?_
    intro y hy
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (Finset.sum_comm (s := Λ) (t := Λ)
        (f := fun z t =>
          a x * a y * a z * a t *
            (twoPoint (ι := ι) spin μ x t * twoPoint (ι := ι) spin μ y z)))
  have hU :
      sum4 (fun x y z t => a x * a y * a z * a t * ursell4 (ι := ι) spin μ x y z t)
        =
        sum4 F4 - (sum4 Pxyzt + sum4 Pxzyt + sum4 Pxtyz) := by
    have hfun :
        (fun x y z t => a x * a y * a z * a t * ursell4 (ι := ι) spin μ x y z t)
          =
        (fun x y z t =>
          F4 x y z t - (Pxyzt x y z t + Pxzyt x y z t + Pxtyz x y z t)) := by
      funext x y z t
      simp [ursell4, F4, Pxyzt, Pxzyt, Pxtyz, mul_add, sub_eq_add_neg, add_assoc,
        mul_assoc, mul_left_comm, mul_comm]
    rw [hfun]
    rw [sum4_sub (F := F4) (G := fun x y z t => Pxyzt x y z t + Pxzyt x y z t + Pxtyz x y z t)]
    have hG1 :
        sum4 (fun x y z t => Pxyzt x y z t + (Pxzyt x y z t + Pxtyz x y z t))
          =
          sum4 Pxyzt + sum4 (fun x y z t => Pxzyt x y z t + Pxtyz x y z t) := by
      simpa [add_assoc] using
        (sum4_add (F := Pxyzt) (G := fun x y z t => Pxzyt x y z t + Pxtyz x y z t))
    have hG2 :
        sum4 (fun x y z t => Pxzyt x y z t + Pxtyz x y z t)
          =
          sum4 Pxzyt + sum4 Pxtyz :=
      sum4_add (F := Pxzyt) (G := Pxtyz)
    calc
      sum4 F4 - sum4 (fun x y z t => Pxyzt x y z t + Pxzyt x y z t + Pxtyz x y z t)
          =
          sum4 F4 - sum4 (fun x y z t => Pxyzt x y z t + (Pxzyt x y z t + Pxtyz x y z t)) := by
            simp [add_assoc]
      _ = sum4 F4 - (sum4 Pxyzt + sum4 (fun x y z t => Pxzyt x y z t + Pxtyz x y z t)) := by
            simp [hG1]
      _ = sum4 F4 - (sum4 Pxyzt + (sum4 Pxzyt + sum4 Pxtyz)) := by
            simp [hG2]
      _ = sum4 F4 - (sum4 Pxyzt + sum4 Pxzyt + sum4 Pxtyz) := by
            ring_nf
  have hPair : (sum4 Pxyzt + sum4 Pxzyt + sum4 Pxtyz) = 3 * (S2 ^ (2 : ℕ)) := by
    calc
      (sum4 Pxyzt + sum4 Pxzyt + sum4 Pxtyz)
          = (sum4 Pxzyt + sum4 Pxzyt + sum4 Pxzyt) := by
              simp [hPxyzt, hPxtyz, add_assoc]
      _ = (S2 ^ (2 : ℕ) + (S2 ^ (2 : ℕ) + S2 ^ (2 : ℕ))) := by
              simp [hPxzyt, add_assoc]
      _ = 3 * (S2 ^ (2 : ℕ)) := by
              ring_nf
  calc
    (∑ x ∈ Λ, ∑ y ∈ Λ, ∑ z ∈ Λ, ∑ t ∈ Λ,
        a x * a y * a z * a t * ursell4 (ι := ι) spin μ x y z t)
        = sum4 (fun x y z t => a x * a y * a z * a t * ursell4 (ι := ι) spin μ x y z t) := by
          rfl
    _ = sum4 F4 - (sum4 Pxyzt + sum4 Pxzyt + sum4 Pxtyz) := hU
    _ = sum4 F4 - 3 * (S2 ^ (2 : ℕ)) := by
          simp [hPair]
    _ =
        (∑ x ∈ Λ, ∑ y ∈ Λ, ∑ z ∈ Λ, ∑ t ∈ Λ,
          a x * a y * a z * a t * fourPoint (ι := ι) spin μ x y z t)
          - 3 * (∑ x ∈ Λ, ∑ y ∈ Λ, a x * a y * twoPoint (ι := ι) spin μ x y) ^ (2 : ℕ) := by
          simp [sum4, F4, S2]

lemma integral_linComb_pow_four_sub_three_mul_sq_integral_linComb_sq_eq_sum_ursell4
    (hI2 : ∀ x ∈ Λ, ∀ y ∈ Λ,
      Integrable (fun η : ι → S =>
        spinAt (ι := ι) spin x η * spinAt (ι := ι) spin y η) μ)
    (hI4 : ∀ x ∈ Λ, ∀ y ∈ Λ, ∀ z ∈ Λ, ∀ t ∈ Λ,
      Integrable (fun η : ι → S =>
        spinAt (ι := ι) spin x η * spinAt (ι := ι) spin y η *
          spinAt (ι := ι) spin z η * spinAt (ι := ι) spin t η) μ) :
    (∫ η, (linComb (ι := ι) (spin := spin) Λ a η) ^ (4 : ℕ) ∂μ)
        - 3 * (∫ η, (linComb (ι := ι) (spin := spin) Λ a η) ^ (2 : ℕ) ∂μ) ^ (2 : ℕ)
      =
      ∑ x ∈ Λ, ∑ y ∈ Λ, ∑ z ∈ Λ, ∑ t ∈ Λ,
        a x * a y * a z * a t * ursell4 (ι := ι) spin μ x y z t := by
  have h2 :=
    integral_linComb_sq_eq_sum_twoPoint (ι := ι) (S := S) (spin := spin) (μ := μ)
      (Λ := Λ) (a := a) hI2
  have h4 :=
    integral_linComb_pow_four_eq_sum_fourPoint (ι := ι) (S := S) (spin := spin) (μ := μ)
      (Λ := Λ) (a := a) hI4
  -- rewrite both integrals as correlation sums, then apply the algebraic cumulant identity
  calc
    (∫ η, (linComb (ι := ι) (spin := spin) Λ a η) ^ (4 : ℕ) ∂μ)
        - 3 * (∫ η, (linComb (ι := ι) (spin := spin) Λ a η) ^ (2 : ℕ) ∂μ) ^ (2 : ℕ)
        =
        (∑ x ∈ Λ, ∑ y ∈ Λ, ∑ z ∈ Λ, ∑ t ∈ Λ,
            a x * a y * a z * a t * fourPoint (ι := ι) spin μ x y z t)
          - 3 * (∑ x ∈ Λ, ∑ y ∈ Λ, a x * a y * twoPoint (ι := ι) spin μ x y) ^ (2 : ℕ) := by
          simp [h4, h2]
    _ =
        (∑ x ∈ Λ, ∑ y ∈ Λ, ∑ z ∈ Λ, ∑ t ∈ Λ,
          a x * a y * a z * a t * ursell4 (ι := ι) spin μ x y z t) := by
          simpa using
            (sum_ursell4_eq_sum_fourPoint_sub_three_mul_sq_sum_twoPoint
              (ι := ι) (S := S) (spin := spin) (μ := μ) (Λ := Λ) (a := a)).symm

end LinearCombination

/-! ## Diagrammatic sums over finite regions -/

namespace Diagrams

/--
Unnormalized bubble diagram over a finite region `Λ` with basepoint `o`:
\[
  B(Λ) := \sum_{x\inΛ} \langle σ_o σ_x\rangle^2 .
\]
-/
noncomputable def bubbleRaw (Λ : Finset ι) (o : ι) : ℝ :=
  Finset.sum Λ fun x => (twoPoint (ι := ι) spin μ o x) ^ (2 : ℕ)

/--
Normalized bubble diagram (GS normalization) over `Λ` with basepoint `o`:
\[
  \frac{1}{\langle σ_o^2\rangle} \sum_{x\inΛ} \langle σ_o σ_x\rangle^2.
\]
-/
noncomputable def bubble (Λ : Finset ι) (o : ι) : ℝ :=
  bubbleRaw (ι := ι) spin μ Λ o / twoPoint (ι := ι) spin μ o o

/-- Truncated susceptibility over a finite region `Λ` with basepoint `o`. -/
noncomputable def chi (Λ : Finset ι) (o : ι) : ℝ :=
  Finset.sum Λ fun x => twoPoint (ι := ι) spin μ o x

/-! ### Core API: bubble diagram -/

lemma bubbleRaw_nonneg (Λ : Finset ι) (o : ι) : 0 ≤ bubbleRaw (ι := ι) spin μ Λ o := by
  unfold bubbleRaw
  refine Finset.sum_nonneg ?_
  intro x _hx
  exact sq_nonneg (twoPoint (ι := ι) spin μ o x)

lemma bubbleRaw_mono {Λ Λ' : Finset ι} (o : ι) (hΛ : Λ ⊆ Λ') :
    bubbleRaw (ι := ι) spin μ Λ o ≤ bubbleRaw (ι := ι) spin μ Λ' o := by
  unfold bubbleRaw
  refine Finset.sum_le_sum_of_subset_of_nonneg hΛ ?_
  intro x _hx _hxnot
  exact sq_nonneg (twoPoint (ι := ι) spin μ o x)

lemma bubble_nonneg (Λ : Finset ι) (o : ι) (h00 : 0 ≤ twoPoint (ι := ι) spin μ o o) :
    0 ≤ bubble (ι := ι) spin μ Λ o := by
  unfold bubble
  exact div_nonneg (bubbleRaw_nonneg (ι := ι) (spin := spin) (μ := μ) Λ o) h00

lemma bubble_mono {Λ Λ' : Finset ι} (o : ι) (hΛ : Λ ⊆ Λ')
    (h00 : 0 ≤ twoPoint (ι := ι) spin μ o o) :
    bubble (ι := ι) spin μ Λ o ≤ bubble (ι := ι) spin μ Λ' o := by
  unfold bubble
  exact div_le_div_of_nonneg_right
    (bubbleRaw_mono (ι := ι) (spin := spin) (μ := μ) o hΛ) h00

lemma bubble_eq_bubbleRaw_of_twoPoint00_eq_one
    (Λ : Finset ι) (o : ι) (h00 : twoPoint (ι := ι) spin μ o o = 1) :
    bubble (ι := ι) spin μ Λ o = bubbleRaw (ι := ι) spin μ Λ o := by
  simp [bubble, h00]

/-! ### Core API: susceptibility -/

lemma chi_mono {Λ Λ' : Finset ι} (o : ι) (hΛ : Λ ⊆ Λ')
    (hnonneg : ∀ x : ι, 0 ≤ twoPoint (ι := ι) spin μ o x) :
    chi (ι := ι) spin μ Λ o ≤ chi (ι := ι) spin μ Λ' o := by
  unfold chi
  refine Finset.sum_le_sum_of_subset_of_nonneg hΛ ?_
  intro x _hx _hxnot
  exact hnonneg x

end Diagrams

end Correlations

end Observables

end GibbsMeasure
