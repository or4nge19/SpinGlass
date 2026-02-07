import SpinGlass.Lattice.Zd
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Probability.Notation
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import GibbsMeasure.Observables.Correlations

/-!
# Scaling observables on `ℤ^d`

This file provides the basic scaling/smearing observable
\[
T_{f,L}(\phi) := \frac{1}{\sqrt{\Sigma_L}} \sum_{x\in\mathbb Z^d} f(x/L)\,\phi_x
\]
in a reusable form on `ZLattice d` (i.e. `Fin d → ℤ`).

The key technical point (used throughout 4D triviality / scaling-limit arguments) is that when
`L > 0` the `tsum` in the definition is actually a **finite sum**, because `f` has compact support.
We expose:

- `Tf_summable_summand`: summability of the smeared summand for `L > 0`;
- `Tf_tsum_eq_sum_box`: a reduction of the `tsum` to a `Finset.sum` over a suitable box.
-/

open scoped BigOperators CompactlySupported ProbabilityTheory

open MeasureTheory Topology GibbsMeasure.Observables.Correlations

namespace SpinGlass
namespace Lattice
namespace Zd

noncomputable section

variable {d : ℕ}

/-- The rescaled embedding `x ↦ x/L` from `ℤ^d` into `ℝ^d`. -/
noncomputable def scalePoint (L : ℝ) (x : ZLattice d) : (Fin d → ℝ) :=
  fun i => (x i : ℝ) / L

@[simp]
lemma scalePoint_apply (L : ℝ) (x : ZLattice d) (i : Fin d) :
    scalePoint (d := d) (L := L) x i = (x i : ℝ) / L := rfl

section SigmaTf

variable {S : Type*} [MeasurableSpace S]
variable (spin : S → ℝ) (μ : Measure (ZLattice d → S))

/-- The variance proxy `Σ_L := ⟨(∑_{x∈Λ_L} φ_x)^2⟩` used to normalize `T_{f,L}`. -/
noncomputable def sigmaL (L : ℕ) : ℝ :=
  μ[fun η => (Finset.sum (box d L) fun x => spin (η x)) ^ (2 : ℕ)]

lemma sigmaL_nonneg (L : ℕ) : 0 ≤ sigmaL (d := d) (spin := spin) μ L := by
  unfold sigmaL
  refine integral_nonneg ?_
  intro η
  exact sq_nonneg _

lemma sigmaL_eq_sum_twoPoint
    (L : ℕ)
    (hI : ∀ x ∈ box d L, ∀ y ∈ box d L,
      Integrable (fun η : ZLattice d → S => spin (η x) * spin (η y)) μ) :
    sigmaL (d := d) (spin := spin) μ L
      =
      ∑ x ∈ box d L, ∑ y ∈ box d L,
        twoPoint (ι := ZLattice d) spin μ x y := by
  have hI' :
      ∀ x ∈ box d L, ∀ y ∈ box d L,
        Integrable (fun η : ZLattice d → S =>
          spinAt (ι := ZLattice d) spin x η *
            spinAt (ι := ZLattice d) spin y η) μ := by
    intro x hx y hy
    simpa [spinAt] using hI x hx y hy
  unfold sigmaL
  simpa [linComb,
    spinAt, one_mul] using
    (integral_linComb_sq_eq_sum_twoPoint
      (ι := ZLattice d) (S := S) (spin := spin) (μ := μ)
      (Λ := box d L) (a := fun _ : ZLattice d => (1 : ℝ)) hI')

variable (f : C_c(Fin d → ℝ, ℝ))

/--
The smeared/averaged observable \(T_{f,L}\) from the paper:
\[
T_{f,L}(\phi) :=  \frac{1}{\sqrt{\Sigma_L}}\sum_{x\in \mathbb Z^d} f(x/L)\,\phi_x.
\]

We implement the `x`-sum using `tsum`; when `L > 0` this sum is finite (see `Tf_tsum_eq_sum_box`).
-/
noncomputable def Tf (L : ℕ) (η : ZLattice d → S) : ℝ :=
  (1 / Real.sqrt (sigmaL (d := d) (spin := spin) μ L)) *
    (∑' x : ZLattice d, (f (scalePoint (d := d) (L := (L : ℝ)) x)) * spin (η x))

@[simp] lemma Tf_zero (L : ℕ) (η : ZLattice d → S) :
    Tf (d := d) (S := S) (spin := spin) (μ := μ) (f := (0 : C_c(Fin d → ℝ, ℝ))) L η = 0 := by
  simp [Tf]

/-!
## Finite support and summability of the smeared sum

The next lemmas are the basic “compact support ⇒ finite sum on a lattice” bridge.
-/

private lemma tsupport_subset_closedBall (f : C_c(Fin d → ℝ, ℝ)) :
    ∃ R : ℝ,
      tsupport (f : (Fin d → ℝ) → ℝ) ⊆ Metric.closedBall (0 : Fin d → ℝ) R := by
  have hcompact : IsCompact (tsupport (f : (Fin d → ℝ) → ℝ)) := by
    simpa [HasCompactSupport] using (CompactlySupportedContinuousMap.hasCompactSupport f)
  rcases (hcompact.isBounded.subset_closedBall (c := (0 : Fin d → ℝ))) with ⟨R, hR⟩
  exact ⟨R, hR⟩

private lemma mem_box_of_mem_tsupport_scalePoint
    {L : ℕ} (hL : 0 < L) {f : C_c(Fin d → ℝ, ℝ)} {R : ℝ}
    (hR : tsupport (f : (Fin d → ℝ) → ℝ) ⊆ Metric.closedBall (0 : Fin d → ℝ) R)
    {x : ZLattice d}
    (hx : scalePoint (d := d) (L := (L : ℝ)) x ∈ tsupport (f : (Fin d → ℝ) → ℝ)) :
    x ∈ box d (Nat.ceil (R * (L : ℝ))) := by
  set N : ℕ := Nat.ceil (R * (L : ℝ))
  have hN : R * (L : ℝ) ≤ (N : ℝ) := by
    simpa [N] using (Nat.le_ceil (R * (L : ℝ)))
  have hLpos : 0 < (L : ℝ) := by exact_mod_cast hL
  have hx_ball : scalePoint (d := d) (L := (L : ℝ)) x ∈ Metric.closedBall (0 : Fin d → ℝ) R :=
    hR hx
  have hdist0 : dist (scalePoint (d := d) (L := (L : ℝ)) x) (0 : Fin d → ℝ) ≤ R := by
    simpa [Metric.mem_closedBall] using hx_ball
  refine (mem_box_iff (d := d) (L := N) (x := x)).2 ?_
  intro i
  have hcoord_dist :
      dist ((scalePoint (d := d) (L := (L : ℝ)) x) i) 0 ≤ R := by
    have := dist_le_pi_dist (scalePoint (d := d) (L := (L : ℝ)) x) (0 : Fin d → ℝ) i
    exact this.trans hdist0
  have habs_div : |(x i : ℝ) / (L : ℝ)| ≤ R := by
    simpa [scalePoint, Real.dist_eq, abs_div, abs_of_pos hLpos] using hcoord_dist
  have habs : |(x i : ℝ)| ≤ R * (L : ℝ) := by
    have : |(x i : ℝ)| / (L : ℝ) ≤ R := by
      simpa [abs_div, abs_of_pos hLpos] using habs_div
    have := (div_le_iff₀ hLpos).1 this
    simpa [mul_comm, abs_of_pos hLpos] using this
  have habsN : |(x i : ℝ)| ≤ (N : ℝ) :=
    le_trans habs (by simpa using hN)
  have hx' : (-(N : ℝ)) ≤ (x i : ℝ) ∧ (x i : ℝ) ≤ (N : ℝ) := abs_le.1 habsN
  have hxIcc : (x i : ℤ) ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    refine Finset.mem_Icc.2 ?_
    constructor
    · have h : (-(N : ℝ)) ≤ (x i : ℝ) := hx'.1
      have h' : ((-(N : ℤ)) : ℝ) ≤ ((x i : ℤ) : ℝ) := by
        -- Keep the left side as an `Int.cast` to match `Int.cast_le`.
        simpa [Int.cast_neg] using h
      have h'' : ((Int.castRingHom ℝ) (-(N : ℤ))) ≤ (Int.castRingHom ℝ) (x i) := by
        simpa using h'
      exact (Int.cast_le).1 h''
    · have : ((x i : ℤ) : ℝ) ≤ (N : ℝ) := by
        simpa using hx'.2
      exact (Int.cast_le).1 this
  simpa using hxIcc

omit [MeasurableSpace S] in
lemma Tf_summable_summand {L : ℕ} (hL : 0 < L) (η : ZLattice d → S) :
    Summable (fun x : ZLattice d =>
      (f (scalePoint (d := d) (L := (L : ℝ)) x)) * spin (η x)) := by
  rcases tsupport_subset_closedBall (d := d) f with ⟨R, hR⟩
  let N : ℕ := Nat.ceil (R * (L : ℝ))
  have hzero :
      ∀ x : ZLattice d, x ∉ box d N →
        (f (scalePoint (d := d) (L := (L : ℝ)) x)) * spin (η x) = 0 := by
    intro x hxbox
    have : f (scalePoint (d := d) (L := (L : ℝ)) x) = 0 := by
      by_contra hf0
      have hts : scalePoint (d := d) (L := (L : ℝ)) x ∈ tsupport (f : (Fin d → ℝ) → ℝ) := by
        by_contra hnot
        exact hf0 (image_eq_zero_of_notMem_tsupport hnot)
      have hxmem : x ∈ box d N := by
        simpa [N] using
          (mem_box_of_mem_tsupport_scalePoint (d := d) (L := L) hL (f := f) (R := R) hR hts)
      exact hxbox hxmem
    simp [this]
  refine summable_of_finite_support ?_
  refine (Finset.finite_toSet (box d N)).subset ?_
  intro x hx
  by_contra hxbox
  have := hzero x hxbox
  exact hx (by simpa [Function.mem_support] using this)

lemma Tf_tsum_eq_sum_box_uniform {L : ℕ} (hL : 0 < L) :
    ∃ N : ℕ,
      ∀ η : ZLattice d → S,
        Tf (d := d) (S := S) (spin := spin) (μ := μ) (f := f) L η
          =
          (1 / Real.sqrt (sigmaL (d := d) (spin := spin) μ L)) *
            (∑ x ∈ box d N, (f (scalePoint (d := d) (L := (L : ℝ)) x)) * spin (η x)) := by
  rcases tsupport_subset_closedBall (d := d) f with ⟨R, hR⟩
  refine ⟨Nat.ceil (R * (L : ℝ)), ?_⟩
  intro η
  let N : ℕ := Nat.ceil (R * (L : ℝ))
  have hzero :
      ∀ x : ZLattice d, x ∉ box d N →
        (f (scalePoint (d := d) (L := (L : ℝ)) x)) * spin (η x) = 0 := by
    intro x hxbox
    have : f (scalePoint (d := d) (L := (L : ℝ)) x) = 0 := by
      by_contra hf0
      have hts : scalePoint (d := d) (L := (L : ℝ)) x ∈ tsupport (f : (Fin d → ℝ) → ℝ) := by
        by_contra hnot
        exact hf0 (image_eq_zero_of_notMem_tsupport hnot)
      have hxmem : x ∈ box d N := by
        simpa [N] using
          (mem_box_of_mem_tsupport_scalePoint (d := d) (L := L) hL (f := f) (R := R) hR hts)
      exact hxbox hxmem
    simp [this]
  simp [Tf, N, tsum_eq_sum (s := box d N) hzero]

lemma Tf_tsum_eq_sum_box {L : ℕ} (hL : 0 < L) (η : ZLattice d → S) :
    ∃ N : ℕ,
      Tf (d := d) (S := S) (spin := spin) (μ := μ) (f := f) L η
        =
        (1 / Real.sqrt (sigmaL (d := d) (spin := spin) μ L)) *
          (∑ x ∈ box d N, (f (scalePoint (d := d) (L := (L : ℝ)) x)) * spin (η x)) := by
  rcases Tf_tsum_eq_sum_box_uniform (d := d) (S := S) (spin := spin) (μ := μ) (f := f) hL with
    ⟨N, hN⟩
  exact ⟨N, hN η⟩

/-!
## Measurability/integrability utilities

These are the basic lemmas needed to justify that the paper's expressions like `μ[fun σ => exp (z * Tf ... σ)]`
are measurable/integrable once the underlying one-site observable is.
-/

lemma measurable_Tf {L : ℕ} (hL : 0 < L) (hspin : Measurable spin) :
    Measurable (fun η : ZLattice d → S =>
      Tf (d := d) (S := S) (spin := spin) (μ := μ) (f := f) L η) := by
  rcases Tf_tsum_eq_sum_box_uniform (d := d) (S := S) (spin := spin) (μ := μ) (f := f) hL with
    ⟨N, hN⟩
  have hEq :
      (fun η : ZLattice d → S =>
        Tf (d := d) (S := S) (spin := spin) (μ := μ) (f := f) L η)
        =
      (fun η : ZLattice d → S =>
        (1 / Real.sqrt (sigmaL (d := d) (spin := spin) μ L)) *
          (∑ x ∈ box d N,
            (f (scalePoint (d := d) (L := (L : ℝ)) x)) * spin (η x))) := by
    funext η
    simpa using hN η
  rw [hEq]
  refine (measurable_const.mul ?_)
  let g : ZLattice d → (ZLattice d → S) → ℝ :=
    fun x η => (f (scalePoint (d := d) (L := (L : ℝ)) x)) * spin (η x)
  have hg : ∀ x ∈ box d N, Measurable (g x) := by
    intro x _hx
    have hspin_x : Measurable (fun η : ZLattice d → S => spin (η x)) :=
      hspin.comp (measurable_pi_apply x)
    simpa [g] using (measurable_const.mul hspin_x)
  simpa [g] using (Finset.measurable_sum (s := box d N) (f := g) hg)

lemma integrable_Tf_of_integrable_spin_apply {L : ℕ} (hL : 0 < L)
    (hI : ∀ x : ZLattice d, Integrable (fun η : ZLattice d → S => spin (η x)) μ) :
    Integrable (fun η : ZLattice d → S =>
      Tf (d := d) (S := S) (spin := spin) (μ := μ) (f := f) L η) μ := by
  rcases Tf_tsum_eq_sum_box_uniform (d := d) (S := S) (spin := spin) (μ := μ) (f := f) hL with
    ⟨N, hN⟩
  have hEq :
      (fun η : ZLattice d → S =>
        Tf (d := d) (S := S) (spin := spin) (μ := μ) (f := f) L η)
        =
      (fun η : ZLattice d → S =>
        (1 / Real.sqrt (sigmaL (d := d) (spin := spin) μ L)) *
          (∑ x ∈ box d N,
            (f (scalePoint (d := d) (L := (L : ℝ)) x)) * spin (η x))) := by
    funext η
    simpa using hN η
  rw [hEq]
  have hsum :
      Integrable
        (fun η : ZLattice d → S =>
          ∑ x ∈ box d N, (f (scalePoint (d := d) (L := (L : ℝ)) x)) * spin (η x)) μ := by
    let g : ZLattice d → (ZLattice d → S) → ℝ :=
      fun x η => (f (scalePoint (d := d) (L := (L : ℝ)) x)) * spin (η x)
    have hg : ∀ x ∈ box d N, Integrable (g x) μ := by
      intro x _hx
      have hxI : Integrable (fun η : ZLattice d → S => spin (η x)) μ := hI x
      simpa [g] using hxI.const_mul (f (scalePoint (d := d) (L := (L : ℝ)) x))
    simpa [g] using (integrable_finset_sum (μ := μ) (s := box d N) hg)
  simpa [mul_assoc] using hsum.const_mul (1 / Real.sqrt (sigmaL (d := d) (spin := spin) μ L))

lemma Tf_eq_of_eqOn_box {L : ℕ} (hL : 0 < L) :
    ∃ N : ℕ,
      ∀ {η η' : ZLattice d → S},
        (∀ x ∈ box d N, η x = η' x) →
          Tf (d := d) (S := S) (spin := spin) (μ := μ) (f := f) L η
            =
            Tf (d := d) (S := S) (spin := spin) (μ := μ) (f := f) L η' := by
  rcases Tf_tsum_eq_sum_box_uniform (d := d) (S := S) (spin := spin) (μ := μ) (f := f) hL with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro η η' hEq
  have hsum :
      (∑ x ∈ box d N, (f (scalePoint (d := d) (L := (L : ℝ)) x)) * spin (η x))
        =
      (∑ x ∈ box d N, (f (scalePoint (d := d) (L := (L : ℝ)) x)) * spin (η' x)) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    have : η x = η' x := hEq x hx
    simp [this]
  calc
    Tf (d := d) (S := S) (spin := spin) (μ := μ) (f := f) L η
        =
        (1 / Real.sqrt (sigmaL (d := d) (spin := spin) μ L)) *
          (∑ x ∈ box d N, (f (scalePoint (d := d) (L := (L : ℝ)) x)) * spin (η x)) := hN η
    _ = (1 / Real.sqrt (sigmaL (d := d) (spin := spin) μ L)) *
          (∑ x ∈ box d N, (f (scalePoint (d := d) (L := (L : ℝ)) x)) * spin (η' x)) := by
          simp [hsum]
    _ = Tf (d := d) (S := S) (spin := spin) (μ := μ) (f := f) L η' := (hN η').symm

lemma integral_Tf_sq_eq_sum_twoPoint
    {L : ℕ} (hL : 0 < L)
    (hI : ∀ x y : ZLattice d,
      Integrable (fun η : ZLattice d → S => spin (η x) * spin (η y)) μ) :
    ∃ N : ℕ,
      (∫ η, (Tf (d := d) (S := S) (spin := spin) (μ := μ) (f := f) L η) ^ (2 : ℕ) ∂μ)
        =
        (1 / Real.sqrt (sigmaL (d := d) (spin := spin) μ L)) ^ (2 : ℕ) *
          (∑ x ∈ box d N, ∑ y ∈ box d N,
            (f (scalePoint (d := d) (L := (L : ℝ)) x)) *
              (f (scalePoint (d := d) (L := (L : ℝ)) y)) *
              twoPoint (ι := ZLattice d) spin μ x y) := by
  rcases Tf_tsum_eq_sum_box_uniform (d := d) (S := S) (spin := spin) (μ := μ) (f := f) hL with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  let a : ZLattice d → ℝ := fun x => f (scalePoint (d := d) (L := (L : ℝ)) x)
  have hI' : ∀ x ∈ box d N, ∀ y ∈ box d N,
      Integrable (fun η : ZLattice d → S =>
        spinAt (ι := ZLattice d) spin x η *
          spinAt (ι := ZLattice d) spin y η) μ := by
    intro x _hx y _hy
    simpa [spinAt] using hI x y
  have hTf : ∀ η : ZLattice d → S,
      Tf (d := d) (S := S) (spin := spin) (μ := μ) (f := f) L η
        =
        (1 / Real.sqrt (sigmaL (d := d) (spin := spin) μ L)) *
          (∑ x ∈ box d N, a x * spin (η x)) := by
    intro η
    simpa [a, mul_assoc] using hN η
  calc
    (∫ η, (Tf (d := d) (S := S) (spin := spin) (μ := μ) (f := f) L η) ^ (2 : ℕ) ∂μ)
        = ∫ η, ((1 / Real.sqrt (sigmaL (d := d) (spin := spin) μ L)) *
            (∑ x ∈ box d N, a x * spin (η x))) ^ (2 : ℕ) ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards with η
            simp [hTf η]
    _ = (1 / Real.sqrt (sigmaL (d := d) (spin := spin) μ L)) ^ (2 : ℕ) *
          ∫ η, (∑ x ∈ box d N, a x * spin (η x)) ^ (2 : ℕ) ∂μ := by
          simp [mul_pow, integral_const_mul, mul_comm]
    _ = (1 / Real.sqrt (sigmaL (d := d) (spin := spin) μ L)) ^ (2 : ℕ) *
          (∑ x ∈ box d N, ∑ y ∈ box d N,
            a x * a y *
              twoPoint (ι := ZLattice d) spin μ x y) := by
          have hLin :
              (∫ η, (∑ x ∈ box d N, a x * spin (η x)) ^ (2 : ℕ) ∂μ)
                =
              (∑ x ∈ box d N, ∑ y ∈ box d N,
                a x * a y *
                  twoPoint (ι := ZLattice d) spin μ x y) := by
            simpa [a, linComb,
              spinAt, one_mul, mul_assoc, mul_left_comm, mul_comm]
              using
                (integral_linComb_sq_eq_sum_twoPoint
                  (ι := ZLattice d) (S := S) (spin := spin) (μ := μ)
                  (Λ := box d N) (a := a) hI')
          simpa [mul_assoc] using congrArg (fun t =>
            (1 / Real.sqrt (sigmaL (d := d) (spin := spin) μ L)) ^ (2 : ℕ) * t) hLin
    _ = (1 / Real.sqrt (sigmaL (d := d) (spin := spin) μ L)) ^ (2 : ℕ) *
          (∑ x ∈ box d N, ∑ y ∈ box d N,
            (f (scalePoint (d := d) (L := (L : ℝ)) x)) *
              (f (scalePoint (d := d) (L := (L : ℝ)) y)) *
              twoPoint (ι := ZLattice d) spin μ x y) := by
          simp [a, mul_comm]

lemma integral_Tf_pow_four_eq_sum_fourPoint
    {L : ℕ} (hL : 0 < L)
    (hI : ∀ x y z t : ZLattice d,
      Integrable (fun η : ZLattice d → S =>
        spin (η x) * spin (η y) * spin (η z) * spin (η t)) μ) :
    ∃ N : ℕ,
      (∫ η, (Tf (d := d) (S := S) (spin := spin) (μ := μ) (f := f) L η) ^ (4 : ℕ) ∂μ)
        =
        (1 / Real.sqrt (sigmaL (d := d) (spin := spin) μ L)) ^ (4 : ℕ) *
          (∑ x ∈ box d N, ∑ y ∈ box d N, ∑ z ∈ box d N, ∑ t ∈ box d N,
            (f (scalePoint (d := d) (L := (L : ℝ)) x)) *
              (f (scalePoint (d := d) (L := (L : ℝ)) y)) *
              (f (scalePoint (d := d) (L := (L : ℝ)) z)) *
              (f (scalePoint (d := d) (L := (L : ℝ)) t)) *
              fourPoint (ι := ZLattice d) spin μ x y z t) := by
  rcases Tf_tsum_eq_sum_box_uniform (d := d) (S := S) (spin := spin) (μ := μ) (f := f) hL with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  let a : ZLattice d → ℝ := fun x => f (scalePoint (d := d) (L := (L : ℝ)) x)
  have hI' : ∀ x ∈ box d N, ∀ y ∈ box d N, ∀ z ∈ box d N, ∀ t ∈ box d N,
      Integrable (fun η : ZLattice d → S =>
        spinAt (ι := ZLattice d) spin x η *
          spinAt (ι := ZLattice d) spin y η *
          spinAt (ι := ZLattice d) spin z η *
          spinAt (ι := ZLattice d) spin t η) μ := by
    intro x _hx y _hy z _hz t _ht
    simpa [spinAt, mul_assoc, mul_left_comm, mul_comm] using hI x y z t
  have hTf : ∀ η : ZLattice d → S,
      Tf (d := d) (S := S) (spin := spin) (μ := μ) (f := f) L η
        =
        (1 / Real.sqrt (sigmaL (d := d) (spin := spin) μ L)) *
          (∑ x ∈ box d N, a x * spin (η x)) := by
    intro η
    simpa [a, mul_assoc] using hN η
  calc
    (∫ η, (Tf (d := d) (S := S) (spin := spin) (μ := μ) (f := f) L η) ^ (4 : ℕ) ∂μ)
        = ∫ η, ((1 / Real.sqrt (sigmaL (d := d) (spin := spin) μ L)) *
            (∑ x ∈ box d N, a x * spin (η x))) ^ (4 : ℕ) ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards with η
            simp [hTf η]
    _ = (1 / Real.sqrt (sigmaL (d := d) (spin := spin) μ L)) ^ (4 : ℕ) *
          ∫ η, (∑ x ∈ box d N, a x * spin (η x)) ^ (4 : ℕ) ∂μ := by
          simp [mul_pow, integral_const_mul, mul_comm]
    _ = (1 / Real.sqrt (sigmaL (d := d) (spin := spin) μ L)) ^ (4 : ℕ) *
          (∑ x ∈ box d N, ∑ y ∈ box d N, ∑ z ∈ box d N, ∑ t ∈ box d N,
            a x * a y * a z * a t *
              fourPoint (ι := ZLattice d) spin μ x y z t) := by
          have hLin :
              (∫ η, (∑ x ∈ box d N, a x * spin (η x)) ^ (4 : ℕ) ∂μ)
                =
              (∑ x ∈ box d N, ∑ y ∈ box d N, ∑ z ∈ box d N, ∑ t ∈ box d N,
                a x * a y * a z * a t *
                  fourPoint (ι := ZLattice d) spin μ x y z t) := by
            simpa [a, linComb,
              spinAt, one_mul, mul_assoc, mul_left_comm, mul_comm]
              using
                (integral_linComb_pow_four_eq_sum_fourPoint
                  (ι := ZLattice d) (S := S) (spin := spin) (μ := μ)
                  (Λ := box d N) (a := a) hI')
          simpa [mul_assoc] using congrArg (fun t =>
            (1 / Real.sqrt (sigmaL (d := d) (spin := spin) μ L)) ^ (4 : ℕ) * t) hLin
    _ = (1 / Real.sqrt (sigmaL (d := d) (spin := spin) μ L)) ^ (4 : ℕ) *
          (∑ x ∈ box d N, ∑ y ∈ box d N, ∑ z ∈ box d N, ∑ t ∈ box d N,
            (f (scalePoint (d := d) (L := (L : ℝ)) x)) *
              (f (scalePoint (d := d) (L := (L : ℝ)) y)) *
              (f (scalePoint (d := d) (L := (L : ℝ)) z)) *
              (f (scalePoint (d := d) (L := (L : ℝ)) t)) *
              fourPoint (ι := ZLattice d) spin μ x y z t) := by
          simp [a, mul_left_comm, mul_comm]

lemma integral_Tf_pow_four_sub_three_mul_sq_integral_Tf_sq_eq_sum_ursell4
    {L : ℕ} (hL : 0 < L)
    (hI2 : ∀ x y : ZLattice d,
      Integrable (fun η : ZLattice d → S => spin (η x) * spin (η y)) μ)
    (hI4 : ∀ x y z t : ZLattice d,
      Integrable (fun η : ZLattice d → S =>
        spin (η x) * spin (η y) * spin (η z) * spin (η t)) μ) :
    ∃ N : ℕ,
      (∫ η, (Tf (d := d) (S := S) (spin := spin) (μ := μ) (f := f) L η) ^ (4 : ℕ) ∂μ)
          - 3 * (∫ η, (Tf (d := d) (S := S) (spin := spin) (μ := μ) (f := f) L η) ^ (2 : ℕ) ∂μ) ^ (2 : ℕ)
        =
        (1 / Real.sqrt (sigmaL (d := d) (spin := spin) μ L)) ^ (4 : ℕ) *
          (∑ x ∈ box d N, ∑ y ∈ box d N, ∑ z ∈ box d N, ∑ t ∈ box d N,
            (f (scalePoint (d := d) (L := (L : ℝ)) x)) *
              (f (scalePoint (d := d) (L := (L : ℝ)) y)) *
              (f (scalePoint (d := d) (L := (L : ℝ)) z)) *
              (f (scalePoint (d := d) (L := (L : ℝ)) t)) *
              ursell4 (ι := ZLattice d) spin μ x y z t) := by
  rcases Tf_tsum_eq_sum_box_uniform (d := d) (S := S) (spin := spin) (μ := μ) (f := f) hL with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  let c : ℝ := (1 / Real.sqrt (sigmaL (d := d) (spin := spin) μ L))
  let a : ZLattice d → ℝ := fun x => f (scalePoint (d := d) (L := (L : ℝ)) x)
  let X : (ZLattice d → S) → ℝ :=
    linComb (ι := ZLattice d) (spin := spin) (Λ := box d N) (a := a)
  have hTf : ∀ η : ZLattice d → S,
      Tf (d := d) (S := S) (spin := spin) (μ := μ) (f := f) L η = c * X η := by
    intro η
    simpa [c, a, X, linComb,
      spinAt, mul_assoc] using hN η
  have hI2' : ∀ x ∈ box d N, ∀ y ∈ box d N,
      Integrable (fun η : ZLattice d → S =>
        spinAt (ι := ZLattice d) spin x η *
          spinAt (ι := ZLattice d) spin y η) μ := by
    intro x _hx y _hy
    simpa [spinAt] using hI2 x y
  have hI4' : ∀ x ∈ box d N, ∀ y ∈ box d N, ∀ z ∈ box d N, ∀ t ∈ box d N,
      Integrable (fun η : ZLattice d → S =>
        spinAt (ι := ZLattice d) spin x η *
          spinAt (ι := ZLattice d) spin y η *
          spinAt (ι := ZLattice d) spin z η *
          spinAt (ι := ZLattice d) spin t η) μ := by
    intro x _hx y _hy z _hz t _ht
    simpa [spinAt, mul_assoc, mul_left_comm, mul_comm] using hI4 x y z t
  have hCumulX :
      (∫ η, (X η) ^ (4 : ℕ) ∂μ) - 3 * (∫ η, (X η) ^ (2 : ℕ) ∂μ) ^ (2 : ℕ)
        =
        ∑ x ∈ box d N, ∑ y ∈ box d N, ∑ z ∈ box d N, ∑ t ∈ box d N,
          a x * a y * a z * a t *
            ursell4 (ι := ZLattice d) spin μ x y z t := by
    simpa [X] using
      (integral_linComb_pow_four_sub_three_mul_sq_integral_linComb_sq_eq_sum_ursell4
        (ι := ZLattice d) (S := S) (spin := spin) (μ := μ)
        (Λ := box d N) (a := a) hI2' hI4')
  have hE4 :
      (∫ η, (Tf (d := d) (S := S) (spin := spin) (μ := μ) (f := f) L η) ^ (4 : ℕ) ∂μ)
        =
        c ^ (4 : ℕ) * (∫ η, (X η) ^ (4 : ℕ) ∂μ) := by
    calc
      (∫ η, (Tf (d := d) (S := S) (spin := spin) (μ := μ) (f := f) L η) ^ (4 : ℕ) ∂μ)
          = ∫ η, (c * X η) ^ (4 : ℕ) ∂μ := by
                refine integral_congr_ae ?_
                filter_upwards with η
                simp [hTf η]
      _ = ∫ η, (c ^ (4 : ℕ)) * (X η) ^ (4 : ℕ) ∂μ := by
            simp [mul_pow]
      _ = c ^ (4 : ℕ) * (∫ η, (X η) ^ (4 : ℕ) ∂μ) := by
            simpa [mul_assoc] using (integral_const_mul (μ := μ) (c ^ (4 : ℕ)) fun η => (X η) ^ (4 : ℕ))
  have hE2 :
      (∫ η, (Tf (d := d) (S := S) (spin := spin) (μ := μ) (f := f) L η) ^ (2 : ℕ) ∂μ)
        =
        c ^ (2 : ℕ) * (∫ η, (X η) ^ (2 : ℕ) ∂μ) := by
    calc
      (∫ η, (Tf (d := d) (S := S) (spin := spin) (μ := μ) (f := f) L η) ^ (2 : ℕ) ∂μ)
          = ∫ η, (c * X η) ^ (2 : ℕ) ∂μ := by
                refine integral_congr_ae ?_
                filter_upwards with η
                simp [hTf η]
      _ = ∫ η, (c ^ (2 : ℕ)) * (X η) ^ (2 : ℕ) ∂μ := by
            simp [mul_pow]
      _ = c ^ (2 : ℕ) * (∫ η, (X η) ^ (2 : ℕ) ∂μ) := by
            simpa [mul_assoc] using (integral_const_mul (μ := μ) (c ^ (2 : ℕ)) fun η => (X η) ^ (2 : ℕ))
  calc
    (∫ η, (Tf (d := d) (S := S) (spin := spin) (μ := μ) (f := f) L η) ^ (4 : ℕ) ∂μ)
        - 3 * (∫ η, (Tf (d := d) (S := S) (spin := spin) (μ := μ) (f := f) L η) ^ (2 : ℕ) ∂μ) ^ (2 : ℕ)
        =
        c ^ (4 : ℕ) *
          ((∫ η, (X η) ^ (4 : ℕ) ∂μ) - 3 * (∫ η, (X η) ^ (2 : ℕ) ∂μ) ^ (2 : ℕ)) := by
          simp [hE4, hE2]
          ring_nf
    _ =
        c ^ (4 : ℕ) *
          (∑ x ∈ box d N, ∑ y ∈ box d N, ∑ z ∈ box d N, ∑ t ∈ box d N,
            a x * a y * a z * a t *
              ursell4 (ι := ZLattice d) spin μ x y z t) := by
          simp [hCumulX]
    _ =
        (1 / Real.sqrt (sigmaL (d := d) (spin := spin) μ L)) ^ (4 : ℕ) *
          (∑ x ∈ box d N, ∑ y ∈ box d N, ∑ z ∈ box d N, ∑ t ∈ box d N,
            (f (scalePoint (d := d) (L := (L : ℝ)) x)) *
              (f (scalePoint (d := d) (L := (L : ℝ)) y)) *
              (f (scalePoint (d := d) (L := (L : ℝ)) z)) *
              (f (scalePoint (d := d) (L := (L : ℝ)) t)) *
              ursell4 (ι := ZLattice d) spin μ x y z t) := by
          simp [c, a]

end SigmaTf

end

end Zd
end Lattice
end SpinGlass
