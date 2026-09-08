/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.Limit.AsymptoticArrayLaws
import Common.Mathlib.Probability.Kernel.Module
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosedProd
import Mathlib.Probability.Kernel.CondDistrib

/-!
# The Ghirlanda–Guerra identities as a disintegration

Talagrand states the Ghirlanda–Guerra identities (Vol. II, Definition 15.3.4, eq. (15.40)) and
Panchenko states them (Ann. of Math. **177** (2013), eq. (1.1)) as a family of integral identities
against *continuous* test functions. That is the form in which they are *verified*. It is not the
form in which they are *used*: every downstream argument — Talagrand's Theorem 15.3.6, Panchenko's
proof of ultrametricity, the Parisi formula — reads them as a statement about the conditional law
of the new overlap:

> given the overlaps of the first `n` replicas, the overlap `R_{0,n}` of replica `0` with a fresh
> replica is distributed as `(1/n) ν + (1/n) ∑_{l=1}^{n-1} δ_{R_{0,l}}`,

where `ν` is the law of a single overlap. This file proves that the second statement follows from
the first, by identifying the *joint* law of `(R^n, R_{0,n})` with a composition-product
`ρ ⊗ₘ ggKernel n ν`. Two things come out of it:

* the identities extend from continuous to arbitrary **bounded measurable** test functions, and
  the test function may depend on the new overlap as well — no separate monotone-class argument is
  needed downstream;
* the conditional distribution `ProbabilityTheory.condDistrib` is computed outright.

The proof is a disintegration argument, not an approximation argument. Both sides of (15.40)
assemble into finite measures on `(Fin n → Fin n → OverlapValue) × OverlapValue`; the identity says
they integrate products of bounded continuous functions equally; and a finite Borel measure on a
product of spaces satisfying `HasOuterApproxClosed` is determined by those integrals
(`MeasureTheory.Measure.ext_of_integral_mul_boundedContinuousFunction`).

## Main statements

- `SpinGlass.ggKernel`: the Ghirlanda–Guerra kernel `x ↦ (1/n) ν + (1/n) ∑_{l=1}^{n-1} δ_{x_{0,l}}`,
  a Markov kernel on the space of `n × n` overlap blocks.
- `SpinGlass.map_prod_blockRestrict_eq_compProd`: **the disintegration form of the identities**.
- `SpinGlass.condDistrib_entry_eq_ggKernel`: the conditional law of `R_{0,n}` given `R^n`.
- `SpinGlass.integral_ghirlandaGuerra`: the identities for **bounded measurable** test functions.
- `SpinGlass.SatisfiesGhirlandaGuerra.map_prod_blockRestrict_eq_compProd` and
  `SpinGlass.SatisfiesGhirlandaGuerra.integral_measurable`: the same for a law satisfying
  Talagrand's (15.40), whose one-overlap law is `SpinGlass.oneOverlapLaw`.
-/

open Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SpinGlass

noncomputable section

variable {n : ℕ}

/-! ### Reindexing the replica sum

The identities sum over replicas `1, …, n-1`, indexed by `ℕ`; the conditioning variable is the
`n × n` overlap block, indexed by `Fin n`. -/

/-- `Fin.val` is a bijection from `{l : Fin n // l ≠ 0}` onto `Finset.Ico 1 n`. -/
lemma sum_finErase_zero {M : Type*} [AddCommMonoid M] [NeZero n] (f : ℕ → M) :
    ∑ l ∈ (Finset.univ : Finset (Fin n)).erase 0, f (l : ℕ) = ∑ l ∈ Finset.Ico 1 n, f l := by
  classical
  have hinj : ∀ x ∈ (Finset.univ : Finset (Fin n)).erase 0,
      ∀ y ∈ (Finset.univ : Finset (Fin n)).erase 0, (x : ℕ) = (y : ℕ) → x = y :=
    fun x _ y _ h => Fin.ext h
  have himg : ((Finset.univ : Finset (Fin n)).erase 0).image Fin.val = Finset.Ico 1 n := by
    ext i
    simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_Ico]
    constructor
    · rintro ⟨l, hl, rfl⟩
      have : (l : ℕ) ≠ 0 := by simpa [Fin.val_eq_zero_iff] using hl
      exact ⟨Nat.one_le_iff_ne_zero.2 this, l.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨i, h2⟩, by simp [Fin.ext_iff]; omega, rfl⟩
  rw [← himg, Finset.sum_image hinj]

/-! ### The Ghirlanda–Guerra kernel -/

/-- **The Ghirlanda–Guerra kernel.** Given the `n × n` block `x` of overlaps of the first `n`
replicas and a reference one-overlap law `ν`, this is the mixture

`(1/n) ν + (1/n) ∑_{l=1}^{n-1} δ_{x_{0,l}}`,

Talagrand Vol. II (15.40) / Panchenko (1.1) read as a conditional distribution. It is a genuine
Markov kernel: the `n` weights are each `1/n`. -/
def ggKernel (n : ℕ) [NeZero n] (ν : Measure OverlapValue) :
    Kernel (Fin n → Fin n → OverlapValue) OverlapValue :=
  (n : ℝ≥0∞)⁻¹ •
    (Kernel.const _ ν + ∑ l ∈ (Finset.univ : Finset (Fin n)).erase 0,
      Kernel.deterministic (fun x : Fin n → Fin n → OverlapValue => x 0 l)
        ((measurable_pi_apply l).comp (measurable_pi_apply 0)))

lemma ggKernel_apply [NeZero n] (ν : Measure OverlapValue)
    (x : Fin n → Fin n → OverlapValue) :
    ggKernel n ν x = (n : ℝ≥0∞)⁻¹ •
      (ν + ∑ l ∈ (Finset.univ : Finset (Fin n)).erase 0, Measure.dirac (x 0 l)) := by
  simp [ggKernel, Kernel.const_apply, Kernel.deterministic_apply]

instance isMarkovKernel_ggKernel [NeZero n] (ν : Measure OverlapValue)
    [IsProbabilityMeasure ν] : IsMarkovKernel (ggKernel n ν) := by
  refine ⟨fun x => ⟨?_⟩⟩
  have hcard : ((Finset.univ : Finset (Fin n)).erase (0 : Fin n)).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hn : n ≠ 0 := NeZero.ne n
  have hsum : (1 : ℝ≥0∞) + ((n - 1 : ℕ) : ℝ≥0∞) = (n : ℝ≥0∞) := by
    rw [← Nat.cast_one (R := ℝ≥0∞), ← Nat.cast_add]
    exact congrArg _ (by omega)
  rw [ggKernel_apply]
  simp only [Measure.smul_apply, Measure.coe_add, Pi.add_apply, Measure.finsetSum_apply,
    measure_univ, Finset.sum_const, hcard, smul_eq_mul, mul_one, nsmul_eq_mul]
  rw [hsum, ENNReal.inv_mul_cancel (by exact_mod_cast hn) (ENNReal.natCast_ne_top n)]

/-- **The integral of a bounded measurable function against the Ghirlanda–Guerra kernel.** -/
lemma integral_ggKernel_of_bounded [NeZero n] (ν : Measure OverlapValue) [IsProbabilityMeasure ν]
    {f : OverlapValue → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ y, ‖f y‖ ≤ C)
    (x : Fin n → Fin n → OverlapValue) :
    (∫ y, f y ∂(ggKernel n ν x))
      = (n : ℝ)⁻¹ *
          ((∫ y, f y ∂ν) + ∑ l ∈ (Finset.univ : Finset (Fin n)).erase 0, f (x 0 l)) := by
  classical
  have hfin : IsFiniteMeasure
      (∑ l ∈ (Finset.univ : Finset (Fin n)).erase (0 : Fin n), Measure.dirac (x 0 l)) := by
    refine ⟨?_⟩
    simp only [Measure.finsetSum_apply, measure_univ, Finset.sum_const, nsmul_eq_mul, mul_one]
    exact ENNReal.natCast_lt_top _
  have hb : ∀ (m : Measure OverlapValue) [IsFiniteMeasure m], Integrable f m := by
    intro m _
    exact Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  rw [ggKernel_apply, integral_smul_measure, integral_add_measure (hb ν) (hb _),
    integral_finsetSum_measure fun l _ => hb (Measure.dirac (x 0 l))]
  simp only [integral_dirac' _ _ hf.stronglyMeasurable, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul]

/-- The integral of a continuous function against the Ghirlanda–Guerra kernel. -/
lemma integral_ggKernel [NeZero n] (ν : Measure OverlapValue) [IsProbabilityMeasure ν]
    (φ : C(OverlapValue, ℝ)) (x : Fin n → Fin n → OverlapValue) :
    (∫ y, φ y ∂(ggKernel n ν x))
      = (n : ℝ)⁻¹ *
          ((∫ y, φ y ∂ν) + ∑ l ∈ (Finset.univ : Finset (Fin n)).erase 0, φ (x 0 l)) :=
  integral_ggKernel_of_bounded ν φ.continuous.measurable
    (fun y => by simpa [Real.norm_eq_abs] using φ.norm_coe_le_norm y) x

/-- Evaluation of an `n × n` overlap block at the entry `(l, l')`, as a continuous map. -/
def blockEval (n : ℕ) (l l' : Fin n) : C(Fin n → Fin n → OverlapValue, OverlapValue) :=
  ⟨fun x => x l l', (continuous_apply l').comp (continuous_apply l)⟩

@[simp] lemma blockEval_apply (n : ℕ) (l l' : Fin n) (x : Fin n → Fin n → OverlapValue) :
    blockEval n l l' x = x l l' := rfl

/-! ### The disintegration -/

variable {μ : Measure (ℕ → ℕ → OverlapValue)} {ν : Measure OverlapValue}

/-- **The Ghirlanda–Guerra identities in disintegrated form.** If the identities hold at level `n`
with reference one-overlap law `ν` — for every continuous `φ` and every continuous function of the
`n × n` overlap block — then the joint law of `(R^n, R_{0,n})` is the composition-product of the
law of `R^n` with the Ghirlanda–Guerra kernel.

This is a strict strengthening of the hypothesis: the conclusion is an equality of measures, so it
applies to arbitrary bounded measurable test functions, and to test functions of the new overlap
and the block jointly. Talagrand Vol. II (15.40); Panchenko, Ann. of Math. **177** (2013), (1.1). -/
theorem map_prod_blockRestrict_eq_compProd [IsProbabilityMeasure μ] [NeZero n]
    [IsProbabilityMeasure ν]
    (h : ∀ (φ : C(OverlapValue, ℝ)) (g : C(Fin n → Fin n → OverlapValue, ℝ)),
      (∫ R, φ (R 0 n) * g (blockRestrict n R) ∂μ)
        = (1 / (n : ℝ)) * ((∫ y, φ y ∂ν) * ∫ R, g (blockRestrict n R) ∂μ)
          + (1 / (n : ℝ)) * ∑ l ∈ Finset.Ico 1 n, ∫ R, φ (R 0 l) * g (blockRestrict n R) ∂μ) :
    μ.map (fun R => (blockRestrict n R, R 0 n))
      = (μ.map (blockRestrict n)) ⊗ₘ ggKernel n ν := by
  classical
  have hB : Measurable (blockRestrict n) := (blockRestrict n).continuous.measurable
  have hEnt : Measurable fun R : ℕ → ℕ → OverlapValue => R 0 n :=
    (measurable_pi_apply n).comp (measurable_pi_apply 0)
  have hBE : Measurable fun R : ℕ → ℕ → OverlapValue => (blockRestrict n R, R 0 n) :=
    hB.prodMk hEnt
  have hρ : IsProbabilityMeasure (μ.map (blockRestrict n)) :=
    Measure.isProbabilityMeasure_map hB.aemeasurable
  have hjoint : IsProbabilityMeasure (μ.map fun R => (blockRestrict n R, R 0 n)) :=
    Measure.isProbabilityMeasure_map hBE.aemeasurable
  refine Measure.ext_of_integral_mul_boundedContinuousFunction fun g φ => ?_
  -- The left-hand side is an integral against `μ`.
  have hLHS : (∫ p, g p.1 * φ p.2 ∂(μ.map fun R => (blockRestrict n R, R 0 n)))
      = ∫ R, g (blockRestrict n R) * φ (R 0 n) ∂μ := by
    exact integral_map (μ := μ) (φ := fun R : ℕ → ℕ → OverlapValue => (blockRestrict n R, R 0 n))
      (f := fun p : (Fin n → Fin n → OverlapValue) × OverlapValue => g p.1 * φ p.2)
      hBE.aemeasurable
      (((g.continuous.comp continuous_fst).mul
        (φ.continuous.comp continuous_snd)).aestronglyMeasurable)
  -- The right-hand side unfolds by Fubini for the composition-product.
  have hint : Integrable
      (fun p : (Fin n → Fin n → OverlapValue) × OverlapValue => g p.1 * φ p.2)
      (μ.map (blockRestrict n) ⊗ₘ ggKernel n ν) :=
    integrable_of_continuous
      ((g.continuous.comp continuous_fst).mul (φ.continuous.comp continuous_snd))
  have hRHS : (∫ p, g p.1 * φ p.2 ∂(μ.map (blockRestrict n) ⊗ₘ ggKernel n ν))
      = ∫ x, (n : ℝ)⁻¹ * ((∫ y, φ y ∂ν) * g x)
          + (n : ℝ)⁻¹ * ∑ l ∈ (Finset.univ : Finset (Fin n)).erase 0, φ (x 0 l) * g x
          ∂(μ.map (blockRestrict n)) := by
    rw [Measure.integral_compProd hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    change (∫ y, g x * φ y ∂(ggKernel n ν x)) = _
    have hg := integral_ggKernel (n := n) ν φ.toContinuousMap x
    simp only [BoundedContinuousFunction.coe_toContinuousMap] at hg
    have key : ∀ A : ℝ,
        g x * ((n : ℝ)⁻¹ * (A + ∑ l ∈ (Finset.univ : Finset (Fin n)).erase 0, φ (x 0 l)))
          = (n : ℝ)⁻¹ * (A * g x)
            + (n : ℝ)⁻¹ * ∑ l ∈ (Finset.univ : Finset (Fin n)).erase 0, φ (x 0 l) * g x := by
      intro A
      rw [← Finset.sum_mul]
      ring
    rw [integral_const_mul, hg, key]
  -- Both remaining integrals are integrals against `μ`.
  have hmap : ∀ f : C(Fin n → Fin n → OverlapValue, ℝ),
      (∫ x, f x ∂(μ.map (blockRestrict n))) = ∫ R, f (blockRestrict n R) ∂μ := fun f => by
    exact integral_map (μ := μ) (φ := (blockRestrict n : _ → _)) (f := fun x => f x)
      hB.aemeasurable f.continuous.aestronglyMeasurable
  have hsplit : (∫ x, (n : ℝ)⁻¹ * ((∫ y, φ y ∂ν) * g x)
        + (n : ℝ)⁻¹ * ∑ l ∈ (Finset.univ : Finset (Fin n)).erase 0, φ (x 0 l) * g x
        ∂(μ.map (blockRestrict n)))
      = (n : ℝ)⁻¹ * ((∫ y, φ y ∂ν) * ∫ x, g x ∂(μ.map (blockRestrict n)))
        + (n : ℝ)⁻¹ * ∑ l ∈ (Finset.univ : Finset (Fin n)).erase 0,
            ∫ x, φ (x 0 l) * g x ∂(μ.map (blockRestrict n)) := by
    rw [integral_add (integrable_of_continuous (by fun_prop))
      (integrable_of_continuous (by fun_prop)), integral_const_mul, integral_const_mul,
      integral_const_mul, integral_finsetSum _ fun l _ => integrable_of_continuous (by fun_prop)]
  rw [hLHS, hRHS, hsplit]
  -- Push the two remaining integrals back to `μ` and apply the hypothesis.
  have h1 : (∫ x, g x ∂(μ.map (blockRestrict n))) = ∫ R, g (blockRestrict n R) ∂μ :=
    hmap g.toContinuousMap
  have h2 : ∀ l ∈ (Finset.univ : Finset (Fin n)).erase 0,
      (∫ x, φ (x 0 l) * g x ∂(μ.map (blockRestrict n)))
      = ∫ R, φ (R 0 (l : ℕ)) * g (blockRestrict n R) ∂μ := fun l _ => by
    have := hmap ((φ.toContinuousMap.comp (blockEval n 0 l)) * g.toContinuousMap)
    simpa using this
  rw [h1, Finset.sum_congr rfl h2, sum_finErase_zero
    (f := fun l : ℕ => ∫ R, φ (R 0 l) * g (blockRestrict n R) ∂μ)]
  have := h φ.toContinuousMap g.toContinuousMap
  simp only [BoundedContinuousFunction.coe_toContinuousMap] at this
  rw [show (∫ R, g (blockRestrict n R) * φ (R 0 n) ∂μ)
      = ∫ R, φ (R 0 n) * g (blockRestrict n R) ∂μ from
    integral_congr_ae (Filter.Eventually.of_forall fun R => mul_comm _ _), this]
  rw [one_div]

/-! ### Consequences: the conditional law, and measurable test functions -/

/-- **The conditional law of the new overlap.** Under the Ghirlanda–Guerra identities the
conditional distribution of `R_{0,n}` given the `n × n` overlap block of the first `n` replicas is
the Ghirlanda–Guerra kernel. This is the form of the identities used by Talagrand (Vol. II,
Theorem 15.3.6) and by Panchenko (Ann. of Math. **177** (2013), eq. (1.2)). -/
theorem condDistrib_entry_eq_ggKernel [IsProbabilityMeasure μ] [NeZero n]
    [IsProbabilityMeasure ν]
    (hgg : μ.map (fun R => (blockRestrict n R, R 0 n))
      = (μ.map (blockRestrict n)) ⊗ₘ ggKernel n ν) :
    condDistrib (fun R => R 0 n) (blockRestrict n) μ
      =ᵐ[μ.map (blockRestrict n)] ggKernel n ν :=
  condDistrib_ae_eq_of_measure_eq_compProd _
    ((measurable_pi_apply n).comp (measurable_pi_apply 0)).aemeasurable hgg

/-- **The Ghirlanda–Guerra identities for bounded measurable test functions.** The test function
may depend jointly on the `n × n` overlap block and on the new overlap — a strictly larger class
than the continuous, block-only test functions of Talagrand's (15.40). -/
theorem integral_ghirlandaGuerra [IsProbabilityMeasure μ] [NeZero n] [IsProbabilityMeasure ν]
    (hgg : μ.map (fun R => (blockRestrict n R, R 0 n))
      = (μ.map (blockRestrict n)) ⊗ₘ ggKernel n ν)
    {F : (Fin n → Fin n → OverlapValue) × OverlapValue → ℝ} (hF : Measurable F)
    {C : ℝ} (hC : ∀ p, ‖F p‖ ≤ C) :
    (∫ R, F (blockRestrict n R, R 0 n) ∂μ)
      = (1 / (n : ℝ)) * (∫ R, ∫ y, F (blockRestrict n R, y) ∂ν ∂μ)
        + (1 / (n : ℝ)) * ∑ l ∈ Finset.Ico 1 n, ∫ R, F (blockRestrict n R, R 0 l) ∂μ := by
  classical
  have hB : Measurable (blockRestrict n) := (blockRestrict n).continuous.measurable
  have hEnt : Measurable fun R : ℕ → ℕ → OverlapValue => R 0 n :=
    (measurable_pi_apply n).comp (measurable_pi_apply 0)
  have hBE : Measurable fun R : ℕ → ℕ → OverlapValue => (blockRestrict n R, R 0 n) :=
    hB.prodMk hEnt
  have hρ : IsProbabilityMeasure (μ.map (blockRestrict n)) :=
    Measure.isProbabilityMeasure_map hB.aemeasurable
  have hint : Integrable F (μ.map (blockRestrict n) ⊗ₘ ggKernel n ν) :=
    Integrable.of_bound hF.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  -- Fubini for the composition-product.
  have step1 : (∫ R, F (blockRestrict n R, R 0 n) ∂μ)
      = ∫ x, ∫ y, F (x, y) ∂(ggKernel n ν x) ∂(μ.map (blockRestrict n)) := by
    rw [← Measure.integral_compProd hint, ← hgg,
      integral_map hBE.aemeasurable hF.aestronglyMeasurable]
  -- Evaluate the inner integral against the Ghirlanda–Guerra kernel.
  have step2 : ∀ x : Fin n → Fin n → OverlapValue,
      (∫ y, F (x, y) ∂(ggKernel n ν x))
        = (n : ℝ)⁻¹ * ((∫ y, F (x, y) ∂ν)
            + ∑ l ∈ (Finset.univ : Finset (Fin n)).erase 0, F (x, x 0 l)) := fun x =>
    integral_ggKernel_of_bounded ν (hF.comp (measurable_const.prodMk measurable_id))
      (fun _ => hC _) x
  rw [step1]
  simp only [step2]
  -- Split the outer integral.
  have hG : StronglyMeasurable fun x : Fin n → Fin n → OverlapValue => ∫ y, F (x, y) ∂ν :=
    hF.stronglyMeasurable.integral_prod_right'
  have hGb : ∀ x : Fin n → Fin n → OverlapValue, ‖∫ y, F (x, y) ∂ν‖ ≤ C := fun x => by
    simpa using norm_integral_le_of_norm_le_const (μ := ν) (C := C)
      (Filter.Eventually.of_forall fun _ => hC _)
  have hGint : Integrable (fun x : Fin n → Fin n → OverlapValue => ∫ y, F (x, y) ∂ν)
      (μ.map (blockRestrict n)) :=
    Integrable.of_bound hG.aestronglyMeasurable C (Filter.Eventually.of_forall hGb)
  have hlint : ∀ l : Fin n, Integrable
      (fun x : Fin n → Fin n → OverlapValue => F (x, x 0 l)) (μ.map (blockRestrict n)) := fun l =>
    Integrable.of_bound
      ((hF.comp (measurable_id.prodMk
        ((measurable_pi_apply l).comp (measurable_pi_apply 0)))).aestronglyMeasurable) C
      (Filter.Eventually.of_forall fun _ => hC _)
  rw [integral_const_mul, integral_add hGint
      (integrable_finsetSum _ fun l _ => hlint l),
    integral_finsetSum _ fun l _ => hlint l]
  -- Push both integrals back to `μ`.
  have hmapG : (∫ x, (∫ y, F (x, y) ∂ν) ∂(μ.map (blockRestrict n)))
      = ∫ R, ∫ y, F (blockRestrict n R, y) ∂ν ∂μ :=
    integral_map hB.aemeasurable hG.aestronglyMeasurable
  have hmapl : ∀ l ∈ (Finset.univ : Finset (Fin n)).erase 0,
      (∫ x, F (x, x 0 l) ∂(μ.map (blockRestrict n)))
        = ∫ R, F (blockRestrict n R, R 0 (l : ℕ)) ∂μ := fun l _ => by
    have := integral_map (μ := μ) (φ := (blockRestrict n : _ → _))
      (f := fun x : Fin n → Fin n → OverlapValue => F (x, x 0 l)) hB.aemeasurable
      ((hF.comp (measurable_id.prodMk
        ((measurable_pi_apply l).comp (measurable_pi_apply 0)))).aestronglyMeasurable)
    simpa using this
  rw [hmapG, Finset.sum_congr rfl hmapl,
    sum_finErase_zero (f := fun l : ℕ => ∫ R, F (blockRestrict n R, R 0 l) ∂μ), one_div]
  ring

/-! ### The identities as verified: from `SatisfiesGhirlandaGuerra` -/

/-- The law of a single overlap is a probability measure. -/
instance isProbabilityMeasure_oneOverlapLaw [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (oneOverlapLaw μ) :=
  Measure.isProbabilityMeasure_map
    (((measurable_pi_apply 1).comp (measurable_pi_apply 0)).aemeasurable)

lemma integral_oneOverlapLaw [IsProbabilityMeasure μ] (φ : C(OverlapValue, ℝ)) :
    (∫ y, φ y ∂(oneOverlapLaw μ)) = ∫ R, φ (R 0 1) ∂μ :=
  integral_map ((measurable_pi_apply 1).comp (measurable_pi_apply 0)).aemeasurable
    φ.continuous.aestronglyMeasurable

/-- **Panchenko's form of the identities disintegrates.** -/
theorem SatisfiesGhirlandaGuerra'.map_prod_blockRestrict_eq_compProd
    [IsProbabilityMeasure μ] (hgg : SatisfiesGhirlandaGuerra' μ) [NeZero n] :
    μ.map (fun R => (blockRestrict n R, R 0 n))
      = (μ.map (blockRestrict n)) ⊗ₘ ggKernel n (oneOverlapLaw μ) := by
  refine _root_.SpinGlass.map_prod_blockRestrict_eq_compProd fun φ g => ?_
  rw [integral_oneOverlapLaw]
  exact hgg n (Nat.pos_of_ne_zero (NeZero.ne n)) (g.comp (blockRestrict n))
    (dependsOnFirst_comp_blockRestrict n g) φ

/-- **Talagrand's form of the identities disintegrates**, for a weakly exchangeable law. -/
theorem SatisfiesGhirlandaGuerra.map_prod_blockRestrict_eq_compProd
    [IsProbabilityMeasure μ] (hex : MeasureTheory.GibbsMeasure.IsJointlyExchangeable μ)
    (hgg : SatisfiesGhirlandaGuerra μ) [NeZero n] :
    μ.map (fun R => (blockRestrict n R, R 0 n))
      = (μ.map (blockRestrict n)) ⊗ₘ ggKernel n (oneOverlapLaw μ) :=
  ((satisfiesGhirlandaGuerra_iff_of_isJointlyExchangeable hex).1
    hgg).map_prod_blockRestrict_eq_compProd

end

end SpinGlass
