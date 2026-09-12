/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Common.Mathlib.Probability.PointProcess.CascadeDeriv
import Common.Mathlib.Probability.Distributions.Gaussian.ColeHopf
import Common.Mathlib.Probability.Distributions.Gaussian.PiGaussian

/-!
# The Parisi recursion as an iterated Cole-Hopf transform

Talagrand's functional form of the recursion (Vol. II, (14.189)-(14.191)): with Gaussian marks
`z_p ~ N(0, v_p)` and a terminal one-site function `G`, setting `A_{k+1} = G` and
`A_p = T_{m_p, v_p}(A_{p+1})`, the recursion applied to `z -> G (x + sum z)` is `A_1 (x)`.

* `coleHopfIterate`: the iterate `T_{m_1,v_1} (... (T_{m_k,v_k} G))`;
* `abs_coleHopfIterate_sub_le`: the iterate preserves Lipschitz constants (Talagrand's
  `|A_p'| <= 1` of (14.271) when `|G'| <= 1`), by monotonicity of exponential averages, with no
  differentiability assumption;
* `cascadeRec_gaussian_comp_add_sum`, `parisiRec_gaussian_comp_add_sum`: the identification
  `parisiRec = A_1`, in the `ENNReal` and the real form of the recursion;
* `hasDerivAt_coleHopfIterate_ball`, `hasDerivAt_coleHopfIterate`: Talagrand's (14.215)/(14.217),
  the derivative of `A_1` in a parameter of the terminal function as the tilted average
  `E(W_1 ... W_k d/dl G_l)`, the parameter ranging over a ball (as it does in his applications);
* `hasDerivAt_coleHopfIterate_split`: his (14.219)-(14.220), the derivative of `A_1` in the split
  point `v` of an innermost pair of levels `T_{m', a-v} o T_{m, v}`;
* `hasDerivAt_integral_coleHopfIterate_split`: the same after the outermost plain average over
  `z_0` (the level with exponent `m_0 = 0`), i.e. Talagrand's `d/dv S(v, m)` of (14.235).

This is the bridge between the cascade side of the theory (`ProbabilityTheory.parisiRec`, its
tilted derivative `hasDerivAt_parisiRec`) and the operator side (`ProbabilityTheory.coleHopf`,
Talagrand's `T_{m,v}`).
-/

open MeasureTheory Filter Topology Function
open scoped ENNReal NNReal BigOperators

namespace ProbabilityTheory

/-- **Talagrand's (14.190)**: the iterated Cole–Hopf transform `A_1 = T_{m_1,v_1} ∘ ⋯ ∘
T_{m_k,v_k} (G)`, the functional form of the Parisi recursion. -/
noncomputable def coleHopfIterate : (k : ℕ) → (Fin k → ℝ) → (Fin k → ℝ≥0) → (ℝ → ℝ) → ℝ → ℝ
  | 0, _, _, G => G
  | k + 1, ms, vs, G =>
      coleHopf (ms 0) (vs 0) (coleHopfIterate k (Fin.tail ms) (Fin.tail vs) G)

@[simp] lemma coleHopfIterate_zero (ms : Fin 0 → ℝ) (vs : Fin 0 → ℝ≥0) (G : ℝ → ℝ) :
    coleHopfIterate 0 ms vs G = G := rfl

lemma coleHopfIterate_succ (k : ℕ) (ms : Fin (k + 1) → ℝ) (vs : Fin (k + 1) → ℝ≥0) (G : ℝ → ℝ) :
    coleHopfIterate (k + 1) ms vs G
      = coleHopf (ms 0) (vs 0) (coleHopfIterate k (Fin.tail ms) (Fin.tail vs) G) := rfl

/-- **The iterated Cole–Hopf transform along a list of levels** `[(m₁, v₁), …, (m_k, v_k)]`:
`T_{m₁,v₁} ∘ ⋯ ∘ T_{m_k,v_k}`. The list form makes the level structure associative on the nose. -/
noncomputable def coleHopfIterateList : List (ℝ × ℝ≥0) → (ℝ → ℝ) → ℝ → ℝ
  | [], G => G
  | p :: l, G => coleHopf p.1 p.2 (coleHopfIterateList l G)

@[simp] lemma coleHopfIterateList_nil (G : ℝ → ℝ) : coleHopfIterateList [] G = G := rfl

@[simp] lemma coleHopfIterateList_cons (p : ℝ × ℝ≥0) (l : List (ℝ × ℝ≥0)) (G : ℝ → ℝ) :
    coleHopfIterateList (p :: l) G = coleHopf p.1 p.2 (coleHopfIterateList l G) := rfl

/-- **Concatenation of level lists is composition of the iterates** — the structural form of
Talagrand's (14.190): the levels split anywhere. -/
theorem coleHopfIterateList_append (l₁ l₂ : List (ℝ × ℝ≥0)) (G : ℝ → ℝ) :
    coleHopfIterateList (l₁ ++ l₂) G
      = coleHopfIterateList l₁ (coleHopfIterateList l₂ G) := by
  induction l₁ with
  | nil => rfl
  | cons p l ih => rw [List.cons_append, coleHopfIterateList_cons, ih, coleHopfIterateList_cons]

/-- The `Fin`-indexed iterate is the list iterate along `List.ofFn`. -/
theorem coleHopfIterate_eq_list (k : ℕ) : ∀ (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) (G : ℝ → ℝ),
    coleHopfIterate k ms vs G = coleHopfIterateList (List.ofFn fun i => (ms i, vs i)) G := by
  induction k with
  | zero => intro ms vs G; rfl
  | succ k ih =>
    intro ms vs G
    rw [coleHopfIterate_succ, ih, List.ofFn_succ, coleHopfIterateList_cons]
    rfl

/-- **Splitting the levels at any depth**: the first `j` levels applied to the rest. -/
theorem coleHopfIterateList_split (j : ℕ) (l : List (ℝ × ℝ≥0)) (G : ℝ → ℝ) :
    coleHopfIterateList l G
      = coleHopfIterateList (l.take j) (coleHopfIterateList (l.drop j) G) := by
  conv_lhs => rw [← List.take_append_drop j l]
  exact coleHopfIterateList_append _ _ _

/-- The Lipschitz bound passes to the list iterate. -/
lemma abs_coleHopfIterateList_sub_le (l : List (ℝ × ℝ≥0)) {G : ℝ → ℝ} {L : ℝ}
    (hG : ∀ x y, |G y - G x| ≤ L * |y - x|) (x y : ℝ) :
    |coleHopfIterateList l G y - coleHopfIterateList l G x| ≤ L * |y - x| := by
  induction l generalizing x y with
  | nil => exact hG x y
  | cons p l ih =>
    have hinm : Measurable (coleHopfIterateList l G) :=
      (lipschitzWith_toNNReal_of_abs_sub_le (fun x y => ih x y)).continuous.measurable
    exact abs_coleHopf_sub_le_of_lipschitz p.1 hinm (fun x y => ih x y) p.2 x y


/-- A level with zero variance drops out of the iterate. -/
lemma coleHopfIterateList_zero_var (m : ℝ) (l : List (ℝ × ℝ≥0)) (G : ℝ → ℝ) :
    coleHopfIterateList ((m, 0) :: l) G = coleHopfIterateList l G := by
  funext x
  rw [coleHopfIterateList_cons]
  exact coleHopf_zero_var _ _ _

/-- **Merging two adjacent levels with the same exponent** (Talagrand's (14.195) in the iterate,
the mechanism behind his (14.233) and (14.237)): `T_{m,a} ∘ T_{m,b} = T_{m,a+b}`. -/
lemma coleHopfIterateList_merge {A : ℝ → ℝ} {L : ℝ}
    (hA : ∀ x y, |A y - A x| ≤ L * |y - x|) (m : ℝ) (a b : ℝ≥0)
    (l₁ l₂ : List (ℝ × ℝ≥0)) :
    coleHopfIterateList (l₁ ++ (m, a) :: (m, b) :: l₂) A
      = coleHopfIterateList (l₁ ++ (m, a + b) :: l₂) A := by
  have hin : ∀ x y, |coleHopfIterateList l₂ A y - coleHopfIterateList l₂ A x| ≤ L * |y - x| :=
    abs_coleHopfIterateList_sub_le l₂ hA
  have hinm : Measurable (coleHopfIterateList l₂ A) :=
    (lipschitzWith_toNNReal_of_abs_sub_le hin).continuous.measurable
  rw [coleHopfIterateList_append, coleHopfIterateList_append]
  congr 1
  rw [coleHopfIterateList_cons, coleHopfIterateList_cons, coleHopfIterateList_cons]
  exact funext fun x =>
    coleHopf_coleHopf (HasLinearGrowth.of_lipschitz hin) hinm m a b x

/-- **The iterate preserves Lipschitz bounds**: Talagrand's `|A_p'| ≤ 1` of (14.271) when
`|G'| ≤ 1`. -/
lemma abs_coleHopfIterate_sub_le (k : ℕ) : ∀ (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) {G : ℝ → ℝ}
    {L : ℝ}, Measurable G → (∀ x y, |G y - G x| ≤ L * |y - x|) → ∀ x y,
    |coleHopfIterate k ms vs G y - coleHopfIterate k ms vs G x| ≤ L * |y - x| := by
  induction k with
  | zero => intro ms vs G L _ hG x y; exact hG x y
  | succ k ih =>
    intro ms vs G L hGm hG x y
    have hin := ih (Fin.tail ms) (Fin.tail vs) hGm hG
    have hinm : Measurable (coleHopfIterate k (Fin.tail ms) (Fin.tail vs) G) :=
      (lipschitzWith_toNNReal_of_abs_sub_le hin).continuous.measurable
    exact abs_coleHopf_sub_le_of_lipschitz (ms 0) hinm hin (vs 0) x y

/-- Consequently the iterate has linear growth. -/
lemma hasLinearGrowth_coleHopfIterate {k : ℕ} (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) {G : ℝ → ℝ}
    {L : ℝ} (hGm : Measurable G) (hG : ∀ x y, |G y - G x| ≤ L * |y - x|) :
    HasLinearGrowth (coleHopfIterate k ms vs G) :=
  HasLinearGrowth.of_lipschitz (abs_coleHopfIterate_sub_le k ms vs hGm hG)

lemma measurable_coleHopfIterate {k : ℕ} (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) {G : ℝ → ℝ} {L : ℝ}
    (hGm : Measurable G) (hG : ∀ x y, |G y - G x| ≤ L * |y - x|) :
    Measurable (coleHopfIterate k ms vs G) :=
  (lipschitzWith_toNNReal_of_abs_sub_le
    (abs_coleHopfIterate_sub_le k ms vs hGm hG)).continuous.measurable

/-- **The cascade recursion of `exp G` is `exp` of the iterated Cole–Hopf transform**
(Talagrand's (14.190)–(14.191) in the `ℝ≥0∞`-form of the recursion). -/
theorem cascadeRec_gaussian_comp_add_sum (k : ℕ) : ∀ (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0)
    {G : ℝ → ℝ} {L : ℝ}, (∀ i, 0 < ms i) → Measurable G → (∀ x y, |G y - G x| ≤ L * |y - x|) →
    ∀ x : ℝ, cascadeRec k ms (fun p => gaussianReal 0 (vs p))
        (fun zs => ENNReal.ofReal (Real.exp (G (x + ∑ p, zs p))))
      = ENNReal.ofReal (Real.exp (coleHopfIterate k ms vs G x)) := by
  induction k with
  | zero =>
    intro ms vs G L _ _ _ x
    simp [cascadeRec_zero]
  | succ k ih =>
    intro ms vs G L hpos hGm hG x
    have hm : 0 < ms 0 := hpos 0
    have hA₂ : ∀ y, cascadeRec k (Fin.tail ms) (fun p => gaussianReal 0 (Fin.tail vs p))
        (fun zs => ENNReal.ofReal (Real.exp (G (y + ∑ p, zs p))))
        = ENNReal.ofReal (Real.exp (coleHopfIterate k (Fin.tail ms) (Fin.tail vs) G y)) :=
      fun y => ih (Fin.tail ms) (Fin.tail vs) (fun i => hpos i.succ) hGm hG y
    set A₂ : ℝ → ℝ := coleHopfIterate k (Fin.tail ms) (Fin.tail vs) G with hA₂def
    have hA₂lip : ∀ x y, |A₂ y - A₂ x| ≤ L * |y - x| :=
      abs_coleHopfIterate_sub_le k (Fin.tail ms) (Fin.tail vs) hGm hG
    have hA₂m : Measurable A₂ :=
      measurable_coleHopfIterate (Fin.tail ms) (Fin.tail vs) hGm hG
    have hA₂g : HasLinearGrowth A₂ := HasLinearGrowth.of_lipschitz hA₂lip
    rw [cascadeRec_succ]
    have hinner : ∀ z : ℝ, cascadeRec k (Fin.tail ms) (Fin.tail fun p => gaussianReal 0 (vs p))
        (fun zs => ENNReal.ofReal (Real.exp (G (x + ∑ p, (Fin.cons z zs : Fin (k + 1) → ℝ) p))))
        = ENNReal.ofReal (Real.exp (A₂ (x + z))) := by
      intro z
      have hsum : ∀ zs : Fin k → ℝ, (∑ p, (Fin.cons z zs : Fin (k + 1) → ℝ) p)
          = z + ∑ p, zs p := fun zs => Fin.sum_cons z zs
      simp only [hsum]
      have : ∀ zs : Fin k → ℝ, x + (z + ∑ p, zs p) = (x + z) + ∑ p, zs p := fun zs => by ring
      simp only [this]
      exact hA₂ (x + z)
    simp only [hinner]
    -- the outer level: an `ℝ≥0∞` integral of `exp (m A₂)`
    have hexp : ∀ z : ℝ, ENNReal.ofReal (Real.exp (A₂ (x + z))) ^ ms 0
        = ENNReal.ofReal (Real.exp (ms 0 * A₂ (x + z))) := by
      intro z
      rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul, mul_comm]
    simp only [hexp]
    have hint : Integrable (fun z => Real.exp (ms 0 * A₂ (x + z))) (gaussianReal 0 (vs 0)) :=
      integrable_exp_mul_comp_add hA₂g hA₂m (ms 0) (vs 0) x
    have hpos' : 0 < ∫ z, Real.exp (ms 0 * A₂ (x + z)) ∂gaussianReal 0 (vs 0) :=
      integral_exp_mul_comp_add_pos hA₂g hA₂m (ms 0) (vs 0) x
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun z => (Real.exp_pos _).le),
      ENNReal.ofReal_rpow_of_pos hpos', Real.rpow_def_of_pos hpos']
    congr 1
    rw [coleHopfIterate_succ, coleHopf_of_ne hm.ne']
    congr 1
    ring

/-- **Talagrand's (14.190)–(14.191)**: the Parisi recursion with Gaussian marks is the iterated
Cole–Hopf transform, `parisiRec = A₁`. -/
theorem parisiRec_gaussian_comp_add_sum {k : ℕ} (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) {G : ℝ → ℝ}
    {L : ℝ} (hpos : ∀ i, 0 < ms i) (hGm : Measurable G)
    (hG : ∀ x y, |G y - G x| ≤ L * |y - x|) (x : ℝ) :
    parisiRec k ms (fun p => gaussianReal 0 (vs p)) (fun zs => G (x + ∑ p, zs p))
      = coleHopfIterate k ms vs G x := by
  rw [parisiRec, cascadeRec_gaussian_comp_add_sum k ms vs hpos hGm hG x,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, Real.log_exp]

/-- Talagrand's (14.4) for a Lipschitz terminal function: the exponential moment of
`G (x + ∑ z_p)` under the product of the Gaussian marks is finite. -/
lemma lintegral_ofReal_exp_comp_add_sum_pi_gaussianReal_ne_top {k : ℕ} (vs : Fin k → ℝ≥0)
    {G : ℝ → ℝ} {L : ℝ} (hG : ∀ x y, |G y - G x| ≤ L * |y - x|) (x : ℝ) :
    ∫⁻ zs, ENNReal.ofReal (Real.exp (G (x + ∑ p, zs p)))
      ∂Measure.pi (fun p => gaussianReal 0 (vs p)) ≠ ∞ := by
  have hL : 0 ≤ L := by
    have h := hG 0 1
    have h1 : |(1 : ℝ) - 0| = 1 := by norm_num
    rw [h1, mul_one] at h
    exact (abs_nonneg _).trans h
  have hbound : ∀ zs : Fin k → ℝ, ENNReal.ofReal (Real.exp (G (x + ∑ p, zs p)))
      ≤ ENNReal.ofReal (Real.exp (G x)) * (ENNReal.ofReal (Real.exp (∑ p, L * zs p))
        + ENNReal.ofReal (Real.exp (∑ p, (-L) * zs p))) := by
    intro zs
    set s : ℝ := ∑ p, zs p with hs
    have h1 : G (x + s) ≤ G x + L * |s| := by
      have h0 := hG x (x + s)
      have h2 : |x + s - x| = |s| := by ring_nf
      rw [h2] at h0
      linarith [le_abs_self (G (x + s) - G x)]
    have h3 : Real.exp (L * |s|) ≤ Real.exp (L * s) + Real.exp (-(L * s)) := by
      rcases le_total 0 s with hs' | hs'
      · rw [abs_of_nonneg hs']
        linarith [Real.exp_pos (-(L * s))]
      · rw [abs_of_nonpos hs', mul_neg, ← neg_mul]
        linarith [Real.exp_pos (L * s)]
    have hsum1 : ∑ p, L * zs p = L * s := by rw [hs, Finset.mul_sum]
    have hsum2 : ∑ p, (-L) * zs p = -(L * s) := by
      rw [hs, Finset.mul_sum]
      simp [neg_mul]
    rw [hsum1, hsum2, ← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    calc Real.exp (G (x + s)) ≤ Real.exp (G x + L * |s|) := Real.exp_le_exp.2 h1
      _ = Real.exp (G x) * Real.exp (L * |s|) := Real.exp_add _ _
      _ ≤ Real.exp (G x) * (Real.exp (L * s) + Real.exp (-(L * s))) :=
          mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hbound)
  have hmeas1 : Measurable fun zs : Fin k → ℝ => ENNReal.ofReal (Real.exp (∑ p, L * zs p)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (Finset.measurable_sum _ fun p _ => measurable_const.mul (measurable_pi_apply p)))
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left hmeas1,
    lintegral_ofReal_exp_sum_mul_pi_gaussianReal, lintegral_ofReal_exp_sum_mul_pi_gaussianReal]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)

/-- The tilt of the iterate is a probability measure, for a Lipschitz terminal function. -/
lemma isProbabilityMeasure_cascadeTiltMeasure_comp_add_sum {k : ℕ} (ms : Fin k → ℝ)
    (vs : Fin k → ℝ≥0) {G : ℝ → ℝ} {L : ℝ} (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    (hGm : Measurable G) (hG : ∀ x y, |G y - G x| ≤ L * |y - x|) (x : ℝ) :
    IsProbabilityMeasure (cascadeTiltMeasure k ms (fun p => gaussianReal 0 (vs p))
      (fun zs => ENNReal.ofReal (Real.exp (G (x + ∑ p, zs p))))) := by
  have hsum : Measurable fun zs : Fin k → ℝ => x + ∑ p, zs p :=
    measurable_const.add (Finset.measurable_sum _ fun p _ => measurable_pi_apply p)
  exact isProbabilityMeasure_cascadeTiltMeasure k ms _
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hGm.comp hsum)))
    (fun zs => ENNReal.ofReal_pos.2 (Real.exp_pos _)) hpos hle
    (lintegral_ofReal_exp_comp_add_sum_pi_gaussianReal_ne_top vs hG x)

/-- A tilted average of the iterate is bounded by the sup of the integrand. -/
lemma abs_integral_cascadeTiltMeasure_le {k : ℕ} (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0)
    {G : ℝ → ℝ} {L : ℝ} (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1) (hGm : Measurable G)
    (hG : ∀ x y, |G y - G x| ≤ L * |y - x|) (x : ℝ) {f : ℝ → ℝ} {C : ℝ} (hf : ∀ y, |f y| ≤ C) :
    |∫ zs, f (x + ∑ p, zs p) ∂cascadeTiltMeasure k ms (fun p => gaussianReal 0 (vs p))
      (fun zs => ENNReal.ofReal (Real.exp (G (x + ∑ p, zs p))))| ≤ C := by
  have := isProbabilityMeasure_cascadeTiltMeasure_comp_add_sum ms vs hpos hle hGm hG x
  have h := norm_integral_le_of_norm_le_const
    (μ := cascadeTiltMeasure k ms (fun p => gaussianReal 0 (vs p))
      (fun zs => ENNReal.ofReal (Real.exp (G (x + ∑ p, zs p)))))
    (f := fun zs => f (x + ∑ p, zs p)) (C := C)
    (Eventually.of_forall fun zs => by rw [Real.norm_eq_abs]; exact hf _)
  rwa [probReal_univ, mul_one, Real.norm_eq_abs] at h
/-- **Talagrand's (14.215)/(14.217)**, local form: the parameter need only range over a ball. -/
theorem hasDerivAt_coleHopfIterate_ball {k : ℕ} (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0)
    {G G' : ℝ → ℝ → ℝ} {L C l₀ δ : ℝ} (hδ : 0 < δ) (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    (hG'm : ∀ l, Measurable (G' l))
    (hd : ∀ l ∈ Metric.ball l₀ δ, ∀ y, HasDerivAt (fun l => G l y) (G' l y) l)
    (hC : ∀ l ∈ Metric.ball l₀ δ, ∀ y, |G' l y| ≤ C)
    (hLip : ∀ l x y, |G l y - G l x| ≤ L * |y - x|) (x : ℝ) :
    HasDerivAt (fun l => coleHopfIterate k ms vs (G l) x)
      (∫ zs, G' l₀ (x + ∑ p, zs p)
        ∂cascadeTiltMeasure k ms (fun p => gaussianReal 0 (vs p))
          (fun zs => ENNReal.ofReal (Real.exp (G l₀ (x + ∑ p, zs p))))) l₀ := by
  have hGmeas : ∀ l, Measurable (G l) := fun l =>
    (lipschitzWith_toNNReal_of_abs_sub_le (hLip l)).continuous.measurable
  have hsum : Measurable fun zs : Fin k → ℝ => x + ∑ p, zs p :=
    measurable_const.add (Finset.measurable_sum _ fun p _ => measurable_pi_apply p)
  have hfun : (fun l => coleHopfIterate k ms vs (G l) x)
      = fun l => parisiRec k ms (fun p => gaussianReal 0 (vs p))
          (fun zs => G l (x + ∑ p, zs p)) :=
    funext fun l => (parisiRec_gaussian_comp_add_sum ms vs hpos (hGmeas l) (hLip l) x).symm
  rw [hfun]
  exact hasDerivAt_parisiRec_ball k ms _ hδ (fun l => (hGmeas l).comp hsum)
    (fun l => (hG'm l).comp hsum) (fun l hl zs => hd l hl _) (fun l hl zs => hC l hl _)
    hpos hle (lintegral_ofReal_exp_comp_add_sum_pi_gaussianReal_ne_top vs (hLip l₀) x)

/-- **Talagrand's (14.215)/(14.217) in operator form**: the derivative of the iterated Cole-Hopf
transform in a parameter of the terminal function is the tilted average of the derivative, the
average against the cascade tilt `W_1 ⋯ W_k`. -/
theorem hasDerivAt_coleHopfIterate {k : ℕ} (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0)
    {G G' : ℝ → ℝ → ℝ} {L C : ℝ} (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    (hG'm : ∀ l, Measurable (G' l))
    (hd : ∀ l y, HasDerivAt (fun l => G l y) (G' l y) l) (hC : ∀ l y, |G' l y| ≤ C)
    (hLip : ∀ l x y, |G l y - G l x| ≤ L * |y - x|) (l₀ x : ℝ) :
    HasDerivAt (fun l => coleHopfIterate k ms vs (G l) x)
      (∫ zs, G' l₀ (x + ∑ p, zs p)
        ∂cascadeTiltMeasure k ms (fun p => gaussianReal 0 (vs p))
          (fun zs => ENNReal.ofReal (Real.exp (G l₀ (x + ∑ p, zs p))))) l₀ :=
  hasDerivAt_coleHopfIterate_ball ms vs one_pos hpos hle hG'm (fun l _ y => hd l y)
    (fun l _ y => hC l y) hLip x

/-- **Talagrand's (14.219)–(14.220) in operator form**: for a terminal function `A` with two
bounded derivatives, the derivative in the split point `v` of the iterate whose innermost two
levels are `T_{m', a−v} ∘ T_{m, v}` is the tilted average, against the cascade weights
`W_1 ⋯ W_j`, of Talagrand's `((m − m')/2) 𝔼(B'(Z, v)² R)` of (14.207). -/
theorem hasDerivAt_coleHopfIterate_split {j : ℕ} (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    {m m' a : ℝ} {A A' A'' : ℝ → ℝ} (hA : ∀ y, HasDerivAt A (A' y) y)
    (hA' : ∀ y, HasDerivAt A' (A'' y) y) (hA''c : Continuous A'') {L L₂ : ℝ}
    (hL : ∀ y, |A' y| ≤ L) (hL₂ : ∀ y, |A'' y| ≤ L₂) (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    (hm : m ≠ 0) {v₀ : ℝ} (hv₀ : 0 < v₀) (hva : v₀ < a) (x : ℝ) :
    HasDerivAt (fun v => coleHopfIterate j ms vs
        (fun y => coleHopf m' (Real.toNNReal (a - v)) (coleHopf m (Real.toNNReal v) A) y) x)
      (∫ zs, ((m - m') / 2) * ∫ z, (∫ w, A' (x + ∑ p, zs p + z + w)
              * coleHopfQ m (Real.toNNReal v₀) A (x + ∑ p, zs p + z) w
                ∂gaussianReal 0 (Real.toNNReal v₀)) ^ 2
            * coleHopfQ m' (Real.toNNReal (a - v₀)) (coleHopf m (Real.toNNReal v₀) A)
                (x + ∑ p, zs p) z ∂gaussianReal 0 (Real.toNNReal (a - v₀))
        ∂cascadeTiltMeasure j ms (fun p => gaussianReal 0 (vs p))
          (fun zs => ENNReal.ofReal (Real.exp (coleHopf m' (Real.toNNReal (a - v₀))
            (coleHopf m (Real.toNNReal v₀) A) (x + ∑ p, zs p))))) v₀ := by
  have hAm : Measurable A := measurable_of_hasDerivAt hA
  have hA'm : Measurable A' := measurable_of_hasDerivAt hA'
  have hAc : Continuous A := continuous_iff_continuousAt.2 fun y => (hA y).continuousAt
  have hA'c : Continuous A' := continuous_iff_continuousAt.2 fun y => (hA' y).continuousAt
  have hAg : HasLinearGrowth A := HasLinearGrowth.of_bounded_deriv hA hL
  have hA'g : HasExpGrowth A' := HasExpGrowth.of_bounded hL
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL 0)
  have hAlip : ∀ y z : ℝ, |A z - A y| ≤ L * |z - y| := fun y z =>
    abs_sub_le_mul_abs_sub_of_hasDerivAt hA hL y z
  -- the inner operator, its Lipschitz bound and its `x`-derivative
  have hBlip : ∀ v : ℝ, ∀ y z : ℝ,
      |coleHopf m (Real.toNNReal v) A z - coleHopf m (Real.toNNReal v) A y| ≤ L * |z - y| :=
    fun v => abs_coleHopf_sub_le_of_lipschitz m hAm hAlip (Real.toNNReal v)
  have hBm : ∀ v : ℝ, Measurable (coleHopf m (Real.toNNReal v) A) := fun v =>
    (lipschitzWith_toNNReal_of_abs_sub_le (hBlip v)).continuous.measurable
  have hBc : ∀ v : ℝ, Continuous (coleHopf m (Real.toNNReal v) A) := fun v =>
    (lipschitzWith_toNNReal_of_abs_sub_le (hBlip v)).continuous
  have hBg : ∀ v : ℝ, HasLinearGrowth (coleHopf m (Real.toNNReal v) A) := fun v =>
    HasLinearGrowth.of_lipschitz (hBlip v)
  have hB1b : ∀ (v : ℝ) (y : ℝ), |∫ w, A' (y + w) * coleHopfQ m (Real.toNNReal v) A y w
      ∂gaussianReal 0 (Real.toNNReal v)| ≤ L := fun v y =>
    abs_integral_mul_coleHopfQ_le' hAg hAm m hA'm hL (Real.toNNReal v) y
  have hB1c : ∀ v : ℝ, Continuous fun y => ∫ w, A' (y + w) * coleHopfQ m (Real.toNNReal v) A y w
      ∂gaussianReal 0 (Real.toNNReal v) := fun v =>
    continuous_integral_mul_coleHopfQ' hAc hAg m hA'c hA'g (Real.toNNReal v)
  have hB1sq : ∀ v : ℝ, Continuous fun y => (∫ w, A' (y + w)
      * coleHopfQ m (Real.toNNReal v) A y w ∂gaussianReal 0 (Real.toNNReal v)) ^ 2 := fun v =>
    (hB1c v).pow 2
  have hB1sqb : ∀ (v : ℝ) (y : ℝ), |(∫ w, A' (y + w) * coleHopfQ m (Real.toNNReal v) A y w
      ∂gaussianReal 0 (Real.toNNReal v)) ^ 2| ≤ L ^ 2 := by
    intro v y
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hB1b v y) 2
  have hB1sqg : ∀ v : ℝ, HasExpGrowth fun y => (∫ w, A' (y + w)
      * coleHopfQ m (Real.toNNReal v) A y w ∂gaussianReal 0 (Real.toNNReal v)) ^ 2 := fun v =>
    HasExpGrowth.of_bounded (C := L ^ 2) (hB1sqb v)
  -- the ball on which the split point stays in `(0, a)`
  set δ : ℝ := min v₀ (a - v₀) with hδdef
  have hδ : 0 < δ := lt_min hv₀ (by linarith)
  have hball : ∀ v ∈ Metric.ball v₀ δ, 0 < v ∧ v < a := by
    intro v hv
    have h1 : |v - v₀| < δ := by simpa [Real.dist_eq] using hv
    have h2 : δ ≤ v₀ := min_le_left _ _
    have h3 : δ ≤ a - v₀ := min_le_right _ _
    constructor
    · linarith [neg_abs_le (v - v₀)]
    · linarith [le_abs_self (v - v₀)]
  refine hasDerivAt_coleHopfIterate_ball ms vs (L := L) (C := |m - m'| / 2 * L ^ 2) hδ hpos hle
    (G' := fun v y => ((m - m') / 2) * ∫ z, (∫ w, A' (y + z + w)
        * coleHopfQ m (Real.toNNReal v) A (y + z) w ∂gaussianReal 0 (Real.toNNReal v)) ^ 2
      * coleHopfQ m' (Real.toNNReal (a - v)) (coleHopf m (Real.toNNReal v) A) y z
      ∂gaussianReal 0 (Real.toNNReal (a - v))) ?_ ?_ ?_ ?_ x
  · -- measurability of the derivative at each `v`
    intro v
    refine (continuous_const.mul ?_).measurable
    exact continuous_integral_mul_coleHopfQ' (hBc v) (hBg v) m' (hB1sq v) (hB1sqg v)
      (Real.toNNReal (a - v))
  · -- the derivative: Lemma 14.7.3
    intro v hv y
    exact hasDerivAt_coleHopf_coleHopf_var hA hA' hA''c hL hL₂ hm (hball v hv).1 (hball v hv).2 y
  · -- the uniform bound on the derivative
    intro v _ y
    rw [abs_mul, abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact abs_integral_mul_coleHopfQ_le' (hBg v) (hBm v) m' (hB1sq v).measurable (hB1sqb v)
      (Real.toNNReal (a - v)) y
  · -- the Lipschitz bound, uniform in `v`
    intro v y z
    exact abs_coleHopf_sub_le_of_lipschitz m' (hBm v) (hBlip v) (Real.toNNReal (a - v)) y z

/-- **Talagrand's `∂_v S(v, m)` of (14.235)**: the `z₀`-average of (14.219)–(14.220). `S(v, m)`
is the `X₀` of the configuration whose innermost pair of levels has been split as
`T_{m', a−v} ∘ T_{m, v}`, and its derivative in the split point is the average, over the
outermost Gaussian `z₀` and the cascade tilt, of `((m − m')/2) 𝔼(B'(Z, v)² R)`. -/
theorem hasDerivAt_integral_coleHopfIterate_split {j : ℕ} (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    {m m' a : ℝ} {A A' A'' : ℝ → ℝ} (hA : ∀ y, HasDerivAt A (A' y) y)
    (hA' : ∀ y, HasDerivAt A' (A'' y) y) (hA''c : Continuous A'') {L L₂ : ℝ}
    (hL : ∀ y, |A' y| ≤ L) (hL₂ : ∀ y, |A'' y| ≤ L₂) (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    (hm : m ≠ 0) {v₀ : ℝ} (hv₀ : 0 < v₀) (hva : v₀ < a) (w₀ : ℝ≥0) (h : ℝ) :
    HasDerivAt (fun v => ∫ z₀, coleHopfIterate j ms vs
        (fun y => coleHopf m' (Real.toNNReal (a - v)) (coleHopf m (Real.toNNReal v) A) y)
        (h + z₀) ∂gaussianReal 0 w₀)
      (∫ z₀, ∫ zs, ((m - m') / 2) * ∫ z, (∫ w, A' (h + z₀ + ∑ p, zs p + z + w)
              * coleHopfQ m (Real.toNNReal v₀) A (h + z₀ + ∑ p, zs p + z) w
                ∂gaussianReal 0 (Real.toNNReal v₀)) ^ 2
            * coleHopfQ m' (Real.toNNReal (a - v₀)) (coleHopf m (Real.toNNReal v₀) A)
                (h + z₀ + ∑ p, zs p) z ∂gaussianReal 0 (Real.toNNReal (a - v₀))
          ∂cascadeTiltMeasure j ms (fun p => gaussianReal 0 (vs p))
            (fun zs => ENNReal.ofReal (Real.exp (coleHopf m' (Real.toNNReal (a - v₀))
              (coleHopf m (Real.toNNReal v₀) A) (h + z₀ + ∑ p, zs p))))
        ∂gaussianReal 0 w₀) v₀ := by
  have hAm : Measurable A := measurable_of_hasDerivAt hA
  have hA'm : Measurable A' := measurable_of_hasDerivAt hA'
  have hAc : Continuous A := continuous_iff_continuousAt.2 fun y => (hA y).continuousAt
  have hA'c : Continuous A' := continuous_iff_continuousAt.2 fun y => (hA' y).continuousAt
  have hAg : HasLinearGrowth A := HasLinearGrowth.of_bounded_deriv hA hL
  have hA'g : HasExpGrowth A' := HasExpGrowth.of_bounded hL
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL 0)
  have hAlip : ∀ y z : ℝ, |A z - A y| ≤ L * |z - y| := fun y z =>
    abs_sub_le_mul_abs_sub_of_hasDerivAt hA hL y z
  -- the inner operator and the split terminal function
  have hBlip : ∀ v : ℝ, ∀ y z : ℝ,
      |coleHopf m (Real.toNNReal v) A z - coleHopf m (Real.toNNReal v) A y| ≤ L * |z - y| :=
    fun v => abs_coleHopf_sub_le_of_lipschitz m hAm hAlip (Real.toNNReal v)
  have hBm : ∀ v : ℝ, Measurable (coleHopf m (Real.toNNReal v) A) := fun v =>
    (lipschitzWith_toNNReal_of_abs_sub_le (hBlip v)).continuous.measurable
  have hBg : ∀ v : ℝ, HasLinearGrowth (coleHopf m (Real.toNNReal v) A) := fun v =>
    HasLinearGrowth.of_lipschitz (hBlip v)
  have hGlip : ∀ v : ℝ, ∀ y z : ℝ,
      |coleHopf m' (Real.toNNReal (a - v)) (coleHopf m (Real.toNNReal v) A) z
        - coleHopf m' (Real.toNNReal (a - v)) (coleHopf m (Real.toNNReal v) A) y|
      ≤ L * |z - y| := fun v =>
    abs_coleHopf_sub_le_of_lipschitz m' (hBm v) (hBlip v) (Real.toNNReal (a - v))
  have hGm : ∀ v : ℝ, Measurable (coleHopf m' (Real.toNNReal (a - v))
      (coleHopf m (Real.toNNReal v) A)) := fun v =>
    (lipschitzWith_toNNReal_of_abs_sub_le (hGlip v)).continuous.measurable
  -- the bounds on the inner tilted averages
  have hB1b : ∀ (v : ℝ) (y : ℝ), |∫ w, A' (y + w) * coleHopfQ m (Real.toNNReal v) A y w
      ∂gaussianReal 0 (Real.toNNReal v)| ≤ L := fun v y =>
    abs_integral_mul_coleHopfQ_le' hAg hAm m hA'm hL (Real.toNNReal v) y
  have hB1c : ∀ v : ℝ, Continuous fun y => ∫ w, A' (y + w) * coleHopfQ m (Real.toNNReal v) A y w
      ∂gaussianReal 0 (Real.toNNReal v) := fun v =>
    continuous_integral_mul_coleHopfQ' hAc hAg m hA'c hA'g (Real.toNNReal v)
  have hB1sq : ∀ v : ℝ, Continuous fun y => (∫ w, A' (y + w)
      * coleHopfQ m (Real.toNNReal v) A y w ∂gaussianReal 0 (Real.toNNReal v)) ^ 2 := fun v =>
    (hB1c v).pow 2
  have hB1sqb : ∀ (v : ℝ) (y : ℝ), |(∫ w, A' (y + w) * coleHopfQ m (Real.toNNReal v) A y w
      ∂gaussianReal 0 (Real.toNNReal v)) ^ 2| ≤ L ^ 2 := by
    intro v y
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hB1b v y) 2
  set δ : ℝ := min v₀ (a - v₀) with hδdef
  have hδ : 0 < δ := lt_min hv₀ (by linarith)
  have hball : ∀ v ∈ Metric.ball v₀ δ, 0 < v ∧ v < a := by
    intro v hv
    have h1 : |v - v₀| < δ := by simpa [Real.dist_eq] using hv
    have h2 : δ ≤ v₀ := min_le_left _ _
    have h3 : δ ≤ a - v₀ := min_le_right _ _
    exact ⟨by linarith [neg_abs_le (v - v₀)], by linarith [le_abs_self (v - v₀)]⟩
  refine hasDerivAt_integral_gaussianReal_param (L := L) (C := |m - m'| / 2 * L ^ 2)
    (D := fun v y => ∫ zs, ((m - m') / 2) * ∫ z, (∫ w, A' (y + ∑ p, zs p + z + w)
          * coleHopfQ m (Real.toNNReal v) A (y + ∑ p, zs p + z) w
            ∂gaussianReal 0 (Real.toNNReal v)) ^ 2
        * coleHopfQ m' (Real.toNNReal (a - v)) (coleHopf m (Real.toNNReal v) A)
            (y + ∑ p, zs p) z ∂gaussianReal 0 (Real.toNNReal (a - v))
      ∂cascadeTiltMeasure j ms (fun p => gaussianReal 0 (vs p))
        (fun zs => ENNReal.ofReal (Real.exp (coleHopf m' (Real.toNNReal (a - v))
          (coleHopf m (Real.toNNReal v) A) (y + ∑ p, zs p))))) hδ
    (fun v => abs_coleHopfIterate_sub_le j ms vs (hGm v) (hGlip v)) (fun v hv x => ?_)
    (fun v hv x => ?_) w₀ h
  · have hb := hball v hv
    exact hasDerivAt_coleHopfIterate_split ms vs hA hA' hA''c hL hL₂ hpos hle hm hb.1 hb.2 x
  · refine abs_integral_cascadeTiltMeasure_le ms vs hpos hle (hGm v) (hGlip v) x
      (f := fun y => ((m - m') / 2) * ∫ z, (∫ w, A' (y + z + w)
          * coleHopfQ m (Real.toNNReal v) A (y + z) w ∂gaussianReal 0 (Real.toNNReal v)) ^ 2
        * coleHopfQ m' (Real.toNNReal (a - v)) (coleHopf m (Real.toNNReal v) A) y z
        ∂gaussianReal 0 (Real.toNNReal (a - v))) (fun y => ?_)
    rw [abs_mul, abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact abs_integral_mul_coleHopfQ_le' (hBg v) (hBm v) m' (hB1sq v).measurable (hB1sqb v)
      (Real.toNNReal (a - v)) y

end ProbabilityTheory
