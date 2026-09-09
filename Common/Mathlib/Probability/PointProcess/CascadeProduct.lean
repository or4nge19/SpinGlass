/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Common.Mathlib.Probability.PointProcess.Cascade
import Common.Mathlib.Probability.ProductMeasureProd

/-!
# Structural identities for the cascade recursion

Talagrand, *Mean Field Models for Spin Glasses*, Vol. II, §14.4, Eqs. (14.81)–(14.84). The
recursion `cascadeRec` (Talagrand's `F_p = (1/m_p) log 𝔼_p exp (m_p F_{p+1})`, in `ℝ≥0∞`) has
three structural properties used to compute `φ(0)` in Guerra's broken replica-symmetry bound:

* **homogeneity** (`cascadeRec_const_mul`): `cascadeRec (C • G) = C * cascadeRec G`, i.e. adding a
  constant to `F_{k+1}` adds it to `F₁`;
* **site factorization** (`cascadeRec_pi`, `parisiRec_sum`): when the marks are product measures
  and `F_{k+1}(z) = ∑_i F_{k+1,i}(z_i)` is a sum over independent sites, then `F₁ = ∑_i F_{1,i}`
  (Talagrand's (14.82));
* **absorption of a level with `m = 1`** (`cascadeRec_snoc_one`): if the last level has
  exponent `m_{k+1} = 1` and its mark averages `G` by a constant factor, that level contributes a
  multiplicative constant (Talagrand's "incorporation" (14.84)); together with the
  sub-multiplicative bound `cascadeRec_sum_le` (Jensen at every level) this is what turns the
  cascade representation of Theorem 14.2.1, which needs `m_p < 1`, into the Parisi recursion with
  its final level `m_{k+1} = 1`.

The Lebesgue-integral form of Fubini for products over `Measure.pi`,
`MeasureTheory.lintegral_fintype_prod_eq_prod` (in `Common/Mathlib/Probability/ProductMeasureProd`),
is the `ℝ≥0∞` companion of Mathlib's Bochner `integral_fintype_prod_eq_prod`.
-/

open MeasureTheory Set Filter Function
open scoped ENNReal Topology

universe u

namespace ProbabilityTheory

open ENNReal

noncomputable section

variable {T : Type u} [MeasurableSpace T]

/-! ### Homogeneity -/

/-- **Homogeneity of the recursion**: `cascadeRec (C • G) = C * cascadeRec G` for `m_p > 0`.
For `G = exp F` this is Talagrand's observation that adding a constant to `F_{k+1}` adds the same
constant to every `F_p`. -/
theorem cascadeRec_const_mul (k : ℕ) :
    ∀ (ms : Fin k → ℝ) (μs : Fin k → Measure T) [∀ i, IsProbabilityMeasure (μs i)]
      {G : (Fin k → T) → ℝ≥0∞}, Measurable G → (∀ i, 0 < ms i) → ∀ (C : ℝ≥0∞),
      cascadeRec k ms μs (fun zs => C * G zs) = C * cascadeRec k ms μs G := by
  induction k with
  | zero =>
    intro ms μs _ G _ _ C
    rfl
  | succ k ih =>
    intro ms μs _ G hG hms C
    have hm : 0 < ms 0 := hms 0
    rw [cascadeRec_succ, cascadeRec_succ]
    have hR : Measurable fun z => cascadeRec k (Fin.tail ms) (Fin.tail μs)
        (fun zs => G (Fin.cons z zs)) := measurable_cascadeRec_cons k _ _ hG
    have hstep : ∀ z, cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => C * G (Fin.cons z zs))
        = C * cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs)) := fun z =>
      ih (Fin.tail ms) (Fin.tail μs) (G := fun zs => G (Fin.cons z zs))
        (hG.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
        (fun i => hms i.succ) C
    simp_rw [hstep, ENNReal.mul_rpow_of_nonneg _ _ hm.le]
    rw [lintegral_const_mul _ (hR.pow_const (ms 0)),
      ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ 1 / ms 0), ← ENNReal.rpow_mul,
      mul_one_div_cancel hm.ne', ENNReal.rpow_one]

/-! ### Site factorization -/

/-- `Fin.cons` of tuples of functions, evaluated at a site, is `Fin.cons` of the values. -/
lemma fin_cons_apply_pi {n : ℕ} {ι : Type*} {S : Type*} (z : ι → S) (zs : Fin n → ι → S)
    (i : ι) : (fun p => (Fin.cons z zs : Fin (n + 1) → ι → S) p i)
      = (Fin.cons (z i) (fun p => zs p i) : Fin (n + 1) → S) := by
  funext p
  refine Fin.cases ?_ (fun q => ?_) p
  · rfl
  · rfl

/-- **Site factorization of the recursion** (Talagrand's (14.82), multiplicative form). When the
mark at level `p` is a product measure `⊗ᵢ ν_{p,i}` over the sites `i` and
`G(z) = ∏ᵢ Gᵢ(z_{·,i})` factorizes over the sites, the recursion factorizes:
`cascadeRec k ms (⊗ᵢ ν_{·,i}) (∏ᵢ Gᵢ) = ∏ᵢ cascadeRec k ms ν_{·,i} Gᵢ`. -/
theorem cascadeRec_pi {ι : Type*} [Fintype ι] {S : Type u} [MeasurableSpace S] (k : ℕ) :
    ∀ (ms : Fin k → ℝ) (νs : Fin k → ι → Measure S) [∀ p i, IsProbabilityMeasure (νs p i)]
      {Gs : ι → (Fin k → S) → ℝ≥0∞}, (∀ i, Measurable (Gs i)) → (∀ p, 0 ≤ ms p) →
      cascadeRec (T := ι → S) k ms (fun p => Measure.pi (νs p))
          (fun zs => ∏ i, Gs i (fun p => zs p i))
        = ∏ i, cascadeRec k ms (fun p => νs p i) (Gs i) := by
  induction k with
  | zero =>
    intro ms νs _ Gs _ _
    simp only [cascadeRec_zero]
    refine Finset.prod_congr rfl fun i _ => ?_
    congr 1
    funext p
    exact Fin.elim0 p
  | succ k ih =>
    intro ms νs _ Gs hGs hms
    have hm : 0 ≤ ms 0 := hms 0
    simp_rw [cascadeRec_succ, fin_cons_apply_pi]
    have hstep : ∀ z : ι → S, cascadeRec k (Fin.tail ms)
        (Fin.tail fun p => Measure.pi (νs p))
        (fun zs => ∏ i, Gs i (Fin.cons (z i) fun p => zs p i))
        = ∏ i, cascadeRec k (Fin.tail ms) (fun p => νs p.succ i)
            (fun zs => Gs i (Fin.cons (z i) zs)) := fun z =>
      ih (Fin.tail ms) (fun p => νs p.succ) (Gs := fun i zs => Gs i (Fin.cons (z i) zs))
        (fun i => (hGs i).comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
        (fun p => hms p.succ)
    have hR : ∀ i, Measurable fun z : S => cascadeRec k (Fin.tail ms) (fun p => νs p.succ i)
        (fun zs => Gs i (Fin.cons z zs)) ^ ms 0 := fun i =>
      (measurable_cascadeRec_cons k _ _ (hGs i)).pow_const _
    have hint : ∫⁻ z : ι → S, cascadeRec k (Fin.tail ms) (Fin.tail fun p => Measure.pi (νs p))
        (fun zs => ∏ i, Gs i (Fin.cons (z i) fun p => zs p i)) ^ ms 0 ∂Measure.pi (νs 0)
        = ∫⁻ z : ι → S, ∏ i, cascadeRec k (Fin.tail ms) (fun p => νs p.succ i)
            (fun zs => Gs i (Fin.cons (z i) zs)) ^ ms 0 ∂Measure.pi (νs 0) :=
      lintegral_congr fun z => by rw [hstep z, ENNReal.prod_rpow_of_nonneg hm]
    rw [hint, lintegral_fintype_prod_eq_prod (νs 0) hR,
      ENNReal.prod_rpow_of_nonneg (by positivity)]
    rfl

/-- **Site factorization of the Parisi recursion** (Talagrand's (14.82)): if `F(z) = ∑ᵢ Fᵢ(z_{·,i})`
is a sum over independent sites, then `F₁ = ∑ᵢ F_{1,i}`. -/
theorem parisiRec_sum {ι : Type*} [Fintype ι] {S : Type u} [MeasurableSpace S] (k : ℕ)
    (ms : Fin k → ℝ) (νs : Fin k → ι → Measure S) [∀ p i, IsProbabilityMeasure (νs p i)]
    {Fs : ι → (Fin k → S) → ℝ} (hFs : ∀ i, Measurable (Fs i)) (hpos : ∀ p, 0 < ms p)
    (hfin : ∀ i, cascadeRec k ms (fun p => νs p i)
      (fun zs => ENNReal.ofReal (Real.exp (Fs i zs))) ≠ ∞) :
    parisiRec (T := ι → S) k ms (fun p => Measure.pi (νs p))
        (fun zs => ∑ i, Fs i (fun p => zs p i))
      = ∑ i, parisiRec k ms (fun p => νs p i) (Fs i) := by
  have hprod : (fun zs : Fin k → ι → S => ENNReal.ofReal (Real.exp (∑ i, Fs i fun p => zs p i)))
      = fun zs => ∏ i, ENNReal.ofReal (Real.exp (Fs i fun p => zs p i)) := by
    funext zs
    rw [Real.exp_sum, ENNReal.ofReal_prod_of_nonneg fun i _ => (Real.exp_pos _).le]
  simp only [parisiRec]
  rw [hprod, cascadeRec_pi k ms νs (Gs := fun i zs => ENNReal.ofReal (Real.exp (Fs i zs)))
    (fun i => ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hFs i)))
    (fun p => (hpos p).le), ENNReal.toReal_prod, Real.log_prod]
  intro i _
  exact (ENNReal.toReal_pos (cascadeRec_pos k _ _
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hFs i)))
    (fun _ => ENNReal.ofReal_pos.2 (Real.exp_pos _)) hpos).ne' (hfin i)).ne'

/-! ### Absorbing a final level with exponent `m = 1` -/

/-- `Fin.snoc` commutes with `Fin.tail`. -/
lemma fin_tail_snoc {n : ℕ} {β : Type*} (q : Fin (n + 1) → β) (b : β) :
    Fin.tail (Fin.snoc (α := fun _ => β) q b) = Fin.snoc (α := fun _ => β) (Fin.tail q) b := by
  conv_lhs => rw [← Fin.cons_self_tail q, ← Fin.cons_snoc_eq_snoc_cons, Fin.tail_cons]

/-- Summing a `Fin.cons` tuple of reals. -/
lemma fin_sum_cons {n : ℕ} (z : ℝ) (zs : Fin n → ℝ) :
    ∑ p, (Fin.cons z zs : Fin (n + 1) → ℝ) p = z + ∑ p, zs p := by
  rw [Fin.sum_univ_succ]
  simp

/-- **Absorbing a level with `m = 1`** (Talagrand's (14.84)). Consider the recursion on the
levels `m₁, …, m_k, m_{k+1} = 1` with real marks `μ₁, …, μ_k, ν`, applied to the function
`G(z₁ + ⋯ + z_{k+1})` of the sum of the marks. If the last mark averages `G` by a constant factor,
`∫ G(a + z) dν(z) = C · G(a)` for all `a`, then that level contributes exactly the factor `C`:
`cascadeRec (k+1) (m, 1) (μ, ν) (G ∘ sum) = C * cascadeRec k m μ (G ∘ sum)`. -/
theorem cascadeRec_snoc_one (k : ℕ) :
    ∀ (ms : Fin k → ℝ) (μs : Fin k → Measure ℝ) [∀ i, IsProbabilityMeasure (μs i)]
      {G : ℝ → ℝ≥0∞}, Measurable G → (∀ i, 0 < ms i) →
      ∀ {ν : Measure ℝ} [IsProbabilityMeasure ν] {C : ℝ≥0∞},
      (∀ a, ∫⁻ z, G (a + z) ∂ν = C * G a) →
      cascadeRec (k + 1) (Fin.snoc ms 1) (Fin.snoc μs ν) (fun zs => G (∑ p, zs p))
        = C * cascadeRec k ms μs (fun zs => G (∑ p, zs p)) := by
  induction k with
  | zero =>
    intro ms μs _ G hG _ ν _ C hC
    rw [cascadeRec_succ, cascadeRec_zero]
    simp only [cascadeRec_zero, fin_sum_cons, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    have := hC 0
    simpa [Fin.snoc] using this
  | succ k ih =>
    intro ms μs _ G hG hms ν _ C hC
    have hm : 0 < ms 0 := hms 0
    rw [cascadeRec_succ, cascadeRec_succ, fin_tail_snoc, fin_tail_snoc]
    have h0m : (Fin.snoc ms (1 : ℝ) : Fin (k + 2) → ℝ) 0 = ms 0 := by
      rw [show (0 : Fin (k + 2)) = Fin.castSucc 0 from rfl, Fin.snoc_castSucc]
    have h0μ : (Fin.snoc μs ν : Fin (k + 2) → Measure ℝ) 0 = μs 0 := by
      rw [show (0 : Fin (k + 2)) = Fin.castSucc 0 from rfl, Fin.snoc_castSucc]
    rw [h0m, h0μ]
    simp_rw [fin_sum_cons]
    have hstep : ∀ z : ℝ, cascadeRec (k + 1) (Fin.snoc (Fin.tail ms) 1)
        (Fin.snoc (Fin.tail μs) ν) (fun zs => G (z + ∑ p, zs p))
        = C * cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G (z + ∑ p, zs p)) := by
      intro z
      have hC' : ∀ a, ∫⁻ w, G (z + (a + w)) ∂ν = C * G (z + a) := by
        intro a
        simpa [add_assoc] using hC (z + a)
      exact ih (Fin.tail ms) (Fin.tail μs) (G := fun a => G (z + a))
        (hG.comp (measurable_const_add z)) (fun i => hms i.succ) hC'
    simp_rw [hstep, ENNReal.mul_rpow_of_nonneg _ _ hm.le]
    have hsum : Measurable fun zs : Fin k → ℝ => ∑ p, zs p :=
      Finset.measurable_sum _ fun p _ => measurable_pi_apply p
    have hR : Measurable fun z : ℝ => cascadeRec k (Fin.tail ms) (Fin.tail μs)
        (fun zs => G (z + ∑ p, zs p)) ^ ms 0 := by
      refine (measurable_cascadeRec_prod k _ _ (α := ℝ)
        (G := fun z zs => G (z + ∑ p, zs p)) ?_).pow_const _
      exact hG.comp (measurable_fst.add (hsum.comp measurable_snd))
    rw [lintegral_const_mul _ hR, ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ 1 / ms 0),
      ← ENNReal.rpow_mul, mul_one_div_cancel hm.ne', ENNReal.rpow_one]

/-- **A sub-multiplicative bound** (Jensen at every level): if `0 < m_p ≤ 1` and each mark
averages `G` by at most a constant factor, `∫ G(a + z) dμ_p(z) ≤ C_p · G(a)`, then
`cascadeRec k m μ (G ∘ sum) ≤ (∏ₚ C_p) · G(0)`. In particular the recursion is finite as soon as
`G(0) < ∞` and the constants are finite. -/
theorem cascadeRec_sum_le (k : ℕ) :
    ∀ (ms : Fin k → ℝ) (μs : Fin k → Measure ℝ) [∀ i, IsProbabilityMeasure (μs i)]
      {G : ℝ → ℝ≥0∞}, Measurable G → (∀ i, 0 < ms i) → (∀ i, ms i ≤ 1) →
      ∀ {C : Fin k → ℝ≥0∞}, (∀ p a, ∫⁻ z, G (a + z) ∂μs p ≤ C p * G a) →
      cascadeRec k ms μs (fun zs => G (∑ p, zs p)) ≤ (∏ p, C p) * G 0 := by
  induction k with
  | zero =>
    intro ms μs _ G _ _ _ C _
    simp
  | succ k ih =>
    intro ms μs _ G hG hpos hle C hC
    have hm : 0 < ms 0 := hpos 0
    rw [cascadeRec_succ]
    simp_rw [fin_sum_cons]
    have hsum : Measurable fun zs : Fin k → ℝ => ∑ p, zs p :=
      Finset.measurable_sum _ fun p _ => measurable_pi_apply p
    have hR : Measurable fun z : ℝ => cascadeRec k (Fin.tail ms) (Fin.tail μs)
        (fun zs => G (z + ∑ p, zs p)) := by
      refine measurable_cascadeRec_prod k _ _ (α := ℝ) (G := fun z zs => G (z + ∑ p, zs p)) ?_
      exact hG.comp (measurable_fst.add (hsum.comp measurable_snd))
    have hstep : ∀ z : ℝ, cascadeRec k (Fin.tail ms) (Fin.tail μs)
        (fun zs => G (z + ∑ p, zs p)) ≤ (∏ p : Fin k, C p.succ) * G z := by
      intro z
      have := ih (Fin.tail ms) (Fin.tail μs) (G := fun a => G (z + a))
        (hG.comp (measurable_const_add z)) (fun i => hpos i.succ) (fun i => hle i.succ)
        (C := fun p => C p.succ) (fun p a => by
          show ∫⁻ w, G (z + (a + w)) ∂μs p.succ ≤ C p.succ * G (z + a)
          simpa [add_assoc] using hC p.succ (z + a))
      simpa using this
    calc (∫⁻ z, cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G (z + ∑ p, zs p)) ^ ms 0
            ∂μs 0) ^ (1 / ms 0)
        ≤ ((∫⁻ z, cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G (z + ∑ p, zs p))
            ∂μs 0) ^ ms 0) ^ (1 / ms 0) :=
          ENNReal.rpow_le_rpow (lintegral_rpow_le_rpow_lintegral _ hR.aemeasurable hm (hle 0))
            (by positivity)
      _ = ∫⁻ z, cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G (z + ∑ p, zs p)) ∂μs 0 := by
          rw [← ENNReal.rpow_mul, mul_one_div_cancel hm.ne', ENNReal.rpow_one]
      _ ≤ ∫⁻ z, (∏ p : Fin k, C p.succ) * G z ∂μs 0 := lintegral_mono hstep
      _ = (∏ p : Fin k, C p.succ) * ∫⁻ z, G (0 + z) ∂μs 0 := by
          rw [lintegral_const_mul _ hG]
          simp
      _ ≤ (∏ p : Fin k, C p.succ) * (C 0 * G 0) := mul_le_mul' le_rfl (hC 0 0)
      _ = (∏ p, C p) * G 0 := by rw [Fin.prod_univ_succ]; ring

end

end ProbabilityTheory
