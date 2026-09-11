/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.Parisi.CoupledParisi
import GibbsMeasure.Mathlib.MeasureTheory.Constructions.PiBlocks
import Common.Mathlib.Data.ENNReal.ProdNeTop

/-!
# The one-site recursion `Y₀` of the coupled scheme (Talagrand Vol. II, (14.144)–(14.145))

The endpoint of the coupled interpolation is a sum over the sites of the one-site function
`Y_{κ+1} = log (ch A ch B ch λ + sh A sh B sh λ)`, `A = h¹ + y¹`, `B = h² + y²` (`pairSiteY`,
`pairSiteF`), and the marks are independent across the sites. By the site factorization
`parisiRec_sum` of the recursion (14.82), transported along the currying
`(Fin N × J → ℝ) ≃ (Fin N → J → ℝ)` of the marks (`MeasureTheory.map_curry_pi`), the recursion
`Y₁` of the site-tree function is the sum of the one-site recursions (`parisiRec_pairCoshF`), and
with the same field at every site `𝔼_{z₀} Y₁ = N · Y₀` (`integral_parisiRec_pairCoshF`), for
Talagrand's `Y₀ = 𝔼 Y₁` (`pairSiteY₀`).
-/

open MeasureTheory ProbabilityTheory Finset Set Filter Topology
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable section

/-! ### The one-site function `Y_{κ+1}` -/

/-- Talagrand's (14.144) at one site: `Y_{κ+1} = log (ch A ch B ch λ + sh A sh B sh λ)`. -/
def pairSiteY (lam A B : ℝ) : ℝ :=
  Real.log (Real.cosh A * Real.cosh B * Real.cosh lam + Real.sinh A * Real.sinh B * Real.sinh lam)

lemma pairSiteY_arg_eq (lam A B : ℝ) :
    Real.cosh A * Real.cosh B * Real.cosh lam + Real.sinh A * Real.sinh B * Real.sinh lam
      = (Real.cosh (A + B) * Real.exp lam + Real.cosh (A - B) * Real.exp (-lam)) / 2 := by
  rw [Real.cosh_add, Real.cosh_sub, ← Real.cosh_add_sinh, ← Real.cosh_sub_sinh]
  ring

lemma cosh_le_pairSiteY_arg (lam A B : ℝ) :
    Real.cosh lam
      ≤ Real.cosh A * Real.cosh B * Real.cosh lam + Real.sinh A * Real.sinh B * Real.sinh lam := by
  rw [pairSiteY_arg_eq, Real.cosh_eq]
  have h1 := mul_le_mul_of_nonneg_right (Real.one_le_cosh (A + B)) (Real.exp_pos lam).le
  have h2 := mul_le_mul_of_nonneg_right (Real.one_le_cosh (A - B)) (Real.exp_pos (-lam)).le
  linarith

lemma exp_pairSiteY (lam A B : ℝ) :
    Real.exp (pairSiteY lam A B)
      = Real.cosh A * Real.cosh B * Real.cosh lam + Real.sinh A * Real.sinh B * Real.sinh lam :=
  Real.exp_log (cosh_mul_cosh_mul_cosh_add_sinh_mul_sinh_mul_sinh_pos A B lam)

/-- `Y_{κ+1} ≥ log ch λ`. -/
lemma log_cosh_le_pairSiteY (lam A B : ℝ) : Real.log (Real.cosh lam) ≤ pairSiteY lam A B :=
  Real.log_le_log (Real.cosh_pos lam) (cosh_le_pairSiteY_arg lam A B)

lemma pairSiteY_nonneg (lam A B : ℝ) : 0 ≤ pairSiteY lam A B :=
  (Real.log_nonneg (Real.one_le_cosh lam)).trans (log_cosh_le_pairSiteY lam A B)

lemma continuous_pairSiteY (lam : ℝ) : Continuous fun q : ℝ × ℝ => pairSiteY lam q.1 q.2 := by
  unfold pairSiteY
  refine Continuous.log ?_ fun q =>
    (cosh_mul_cosh_mul_cosh_add_sinh_mul_sinh_mul_sinh_pos _ _ _).ne'
  fun_prop

/-! ### The one-site function of the marks -/

variable {κ : ℕ} {J : Type*} [Fintype J]

/-- The one-site field of copy `ℓ`: `∑_j K₀ ℓ j y₀ j + ∑_p ∑_j K p ℓ j y p j`. -/
def pairSiteMark (K₀ : Fin 2 → J → ℝ) (K : Fin κ → Fin 2 → J → ℝ) (y₀ : J → ℝ)
    (y : Fin κ → J → ℝ) (l : Fin 2) : ℝ :=
  ∑ j, K₀ l j * y₀ j + ∑ p, ∑ j, K p l j * y p j

/-- Talagrand's (14.144) at a site with field `h`:
`Y_{κ+1}(y₀, y) = pairSiteY λ (h¹ + y¹) (h² + y²)`, `y^ℓ` the one-site field of copy `ℓ`. -/
def pairSiteF (lam : ℝ) (h : Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ) (K : Fin κ → Fin 2 → J → ℝ)
    (y₀ : J → ℝ) (y : Fin κ → J → ℝ) : ℝ :=
  pairSiteY lam (h 0 + pairSiteMark K₀ K y₀ y 0) (h 1 + pairSiteMark K₀ K y₀ y 1)

lemma pairSiteF_nonneg (lam : ℝ) (h : Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ)
    (K : Fin κ → Fin 2 → J → ℝ) (y₀ : J → ℝ) (y : Fin κ → J → ℝ) :
    0 ≤ pairSiteF lam h K₀ K y₀ y :=
  pairSiteY_nonneg _ _ _

lemma continuous_pairSiteF (lam : ℝ) (h : Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ)
    (K : Fin κ → Fin 2 → J → ℝ) :
    Continuous fun q : (J → ℝ) × (Fin κ → J → ℝ) => pairSiteF lam h K₀ K q.1 q.2 := by
  have hf : Continuous fun q : (J → ℝ) × (Fin κ → J → ℝ) =>
      (h 0 + pairSiteMark K₀ K q.1 q.2 0, h 1 + pairSiteMark K₀ K q.1 q.2 1) := by
    unfold pairSiteMark
    fun_prop
  have hc := (continuous_pairSiteY lam).comp hf
  exact hc

lemma measurable_pairSiteF' (lam : ℝ) (h : Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ)
    (K : Fin κ → Fin 2 → J → ℝ) (y₀ : J → ℝ) : Measurable (pairSiteF lam h K₀ K y₀) := by
  have hc := (continuous_pairSiteF lam h K₀ K).comp
    (continuous_const.prodMk continuous_id : Continuous fun y : Fin κ → J → ℝ => (y₀, y))
  exact hc.measurable

variable (N : ℕ)

/-- The site-tree function is the sum of the one-site functions. -/
lemma pairCoshF_eq_sum_pairSiteF (lam : ℝ) (a : Fin N × Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ)
    (K : Fin κ → Fin 2 → J → ℝ) (z₀ : Fin N × J → ℝ) (x : Fin κ → Fin N × J → ℝ) :
    pairCoshF N κ lam a K₀ K z₀ x
      = ∑ i, pairSiteF lam (fun l => a (i, l)) K₀ K (fun j => z₀ (i, j)) (fun p j => x p (i, j)) :=
  rfl

/-! ### Site factorization of `Y₁` -/

/-- **Site factorization of `Y₁`** (Talagrand's (14.82) for the coupled scheme):
`Y₁(z₀) = ∑ᵢ Y₁^{(i)}(z₀(i,·))`, the one-site recursion at site `i` having field `a(i,·)` and
root mark `z₀(i,·)`. -/
theorem parisiRec_pairCoshF (ns : Fin κ → ℝ) (hpos : ∀ i, 0 < ns i) (hle : ∀ i, ns i ≤ 1)
    (vs : Fin κ → ℝ≥0) (lam : ℝ) (a : Fin N × Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ)
    (K : Fin κ → Fin 2 → J → ℝ) (z₀ : Fin N × J → ℝ) :
    parisiRec κ ns (siteGaussianMarks (Fin N × J) κ vs) (pairCoshF N κ lam a K₀ K z₀)
      = ∑ i, parisiRec κ ns (siteGaussianMarks J κ vs)
          (pairSiteF lam (fun l => a (i, l)) K₀ K (fun j => z₀ (i, j))) := by
  classical
  set Fs : Fin N → (Fin κ → J → ℝ) → ℝ :=
    fun i => pairSiteF lam (fun l => a (i, l)) K₀ K (fun j => z₀ (i, j)) with hFs
  have hFsm : ∀ i, Measurable (Fs i) := fun i => measurable_pairSiteF' lam _ K₀ K _
  -- the currying of the marks
  set φ : (Fin N × J → ℝ) → (Fin N → J → ℝ) := fun x i j => x (i, j) with hφ
  have hφm : Measurable φ :=
    measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => measurable_pi_apply (i, j)
  have hmap : ∀ p : Fin κ, (siteGaussianMarks (Fin N × J) κ vs p).map φ
      = Measure.pi fun _ : Fin N => siteGaussianMarks J κ vs p := fun p =>
    map_curry_pi (Fin N) J (gaussianReal 0 (vs p))
  have hmap' : (fun p => (siteGaussianMarks (Fin N × J) κ vs p).map φ)
      = fun p => Measure.pi fun _ : Fin N => siteGaussianMarks J κ vs p := funext hmap
  -- the summed function on the curried marks
  set F' : (Fin κ → Fin N → J → ℝ) → ℝ := fun ys => ∑ i, Fs i (fun p => ys p i) with hF'
  have hcoord : ∀ i : Fin N, Measurable fun ys : Fin κ → Fin N → J → ℝ => fun p => ys p i :=
    fun i => measurable_pi_lambda _ fun p => (measurable_pi_apply i).comp (measurable_pi_apply p)
  have hF'm : Measurable F' := Finset.measurable_sum _ fun i _ => (hFsm i).comp (hcoord i)
  -- finiteness of each site factor, from the finiteness of the site-tree recursion
  have hfin : ∀ i, cascadeRec κ ns (siteGaussianMarks J κ vs)
      (fun y => ENNReal.ofReal (Real.exp (Fs i y))) ≠ ∞ := by
    have hGs : ∀ i, Measurable fun y : Fin κ → J → ℝ => ENNReal.ofReal (Real.exp (Fs i y)) :=
      fun i => ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hFsm i))
    have hprod := cascadeRec_pi κ ns (fun p _ => siteGaussianMarks J κ vs p)
      (Gs := fun i y => ENNReal.ofReal (Real.exp (Fs i y))) hGs (fun p => (hpos p).le)
    have hGm : Measurable fun ys : Fin κ → Fin N → J → ℝ =>
        ∏ i, ENNReal.ofReal (Real.exp (Fs i (fun p => ys p i))) :=
      Finset.measurable_prod _ fun i _ => (hGs i).comp (hcoord i)
    have htot : cascadeRec κ ns (fun p => Measure.pi fun _ : Fin N => siteGaussianMarks J κ vs p)
        (fun ys => ∏ i, ENNReal.ofReal (Real.exp (Fs i (fun p => ys p i)))) ≠ ∞ := by
      rw [← hmap', cascadeRec_map κ ns _ (fun _ => φ) (fun _ => hφm) hGm]
      have hfun : (fun zs : Fin κ → Fin N × J → ℝ =>
          ∏ i, ENNReal.ofReal (Real.exp (Fs i (fun p => φ (zs p) i))))
          = fun zs => ENNReal.ofReal (Real.exp (pairCoshF N κ lam a K₀ K z₀ zs)) := by
        funext zs
        rw [pairCoshF_eq_sum_pairSiteF, Real.exp_sum,
          ENNReal.ofReal_prod_of_nonneg fun i _ => (Real.exp_pos _).le]
      rw [hfun]
      exact cascadeRec_ofReal_exp_pairCoshF_ne_top N κ ns vs hpos hle lam a K₀ K z₀
    rw [hprod] at htot
    exact ENNReal.ne_top_of_prod_ne_top (fun j => (cascadeRec_pos κ ns _ (hGs j)
      (fun _ => ENNReal.ofReal_pos.2 (Real.exp_pos _)) hpos).ne') htot
  -- transport the recursion along the currying and factorize
  have h1 : parisiRec κ ns (siteGaussianMarks (Fin N × J) κ vs) (pairCoshF N κ lam a K₀ K z₀)
      = parisiRec κ ns (fun p => (siteGaussianMarks (Fin N × J) κ vs p).map φ) F' := by
    rw [parisiRec_map κ ns _ (fun _ => φ) (fun _ => hφm) hF'm]
    rfl
  rw [h1, hmap']
  exact parisiRec_sum κ ns (fun p _ => siteGaussianMarks J κ vs p) hFsm hpos hfin

/-! ### Talagrand's `Y₀` -/

/-- **Talagrand's `Y₀`** ((14.145), `Y₀ = 𝔼 Y₁`): the one-site recursion, with field `h`, root
mark `y₀ ∼ N(0, v₀)^J` and marks `y_p ∼ N(0, v_p)^J` along the branch, averaged over `y₀`. -/
def pairSiteY₀ (ns : Fin κ → ℝ) (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) (lam : ℝ) (h : Fin 2 → ℝ)
    (K₀ : Fin 2 → J → ℝ) (K : Fin κ → Fin 2 → J → ℝ) : ℝ :=
  ∫ y₀, parisiRec κ ns (siteGaussianMarks J κ vs) (pairSiteF lam h K₀ K y₀)
    ∂Measure.pi fun _ : J => gaussianReal 0 v₀

universe u

variable {J' : Type u} [Fintype J']

/-- `Y₁` is integrable in the root marks. -/
theorem integrable_parisiRec_pairCoshF_rootMarksLaw (ns : Fin κ → ℝ) (hsm : StrictMono ns)
    (hpos : ∀ i, 0 < ns i) (hlt : ∀ i, ns i < 1) (lam : ℝ) (a : Fin N × Fin 2 → ℝ)
    (K₀ : Fin 2 → J' → ℝ) (K : Fin κ → Fin 2 → J' → ℝ) (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) :
    Integrable (fun z₀ => parisiRec κ ns (siteGaussianMarks (Fin N × J') κ vs)
      (pairCoshF N κ lam a K₀ K z₀)) (rootMarksLaw N v₀) := by
  have hI := integrable_parisiRec_pairCoshF N ns hsm hpos hlt lam a K₀ K v₀ vs
    (Pm := (Measure.dirac PUnit.unit : Measure PUnit.{u + 1}))
  have hmeas : AEStronglyMeasurable (fun z₀ => parisiRec κ ns (siteGaussianMarks (Fin N × J') κ vs)
      (pairCoshF N κ lam a K₀ K z₀)) (rootMarksLaw N v₀) := by
    have hc := (continuous_pairCoshF N κ (J := J') lam a).comp
      ((continuous_const.prodMk (continuous_fst.prodMk continuous_snd)) :
        Continuous fun p : (Fin N × J' → ℝ) × (Fin κ → Fin N × J' → ℝ) =>
          (((0 : EnergySpace N), K₀, K), (p.1, p.2)))
    have hG : Measurable (Function.uncurry fun (z₀ : Fin N × J' → ℝ)
        (x : Fin κ → Fin N × J' → ℝ) => ENNReal.ofReal (Real.exp
          (pairCoshF N κ lam a K₀ K z₀ x))) := by
      have h := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hc.measurable)
      exact h
    have hR : Measurable fun z₀ : Fin N × J' → ℝ => cascadeRec κ ns
        (siteGaussianMarks (Fin N × J') κ vs) (fun x => ENNReal.ofReal (Real.exp
          (pairCoshF N κ lam a K₀ K z₀ x))) :=
      measurable_cascadeRec_prod κ ns (siteGaussianMarks (Fin N × J') κ vs) hG
    exact hR.ennreal_toReal.log.aestronglyMeasurable
  exact ((measurePreserving_snd (μ := (Measure.dirac PUnit.unit : Measure PUnit.{u + 1}))
    (ν := rootMarksLaw N v₀)).integrable_comp hmeas).1 hI

/-- **`𝔼_{z₀} Y₁(z₀) = N · Y₀`** when the field is the same `h` at every site (Talagrand's
(14.143)–(14.145)): the sites are independent and identically distributed. -/
theorem integral_parisiRec_pairCoshF (ns : Fin κ → ℝ) (hsm : StrictMono ns)
    (hpos : ∀ i, 0 < ns i) (hlt : ∀ i, ns i < 1) (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) (lam : ℝ)
    (h : Fin 2 → ℝ) (K₀ : Fin 2 → J' → ℝ) (K : Fin κ → Fin 2 → J' → ℝ) :
    ∫ z₀, parisiRec κ ns (siteGaussianMarks (Fin N × J') κ vs)
        (pairCoshF N κ lam (fun s => h s.2) K₀ K z₀) ∂rootMarksLaw N v₀
      = N * pairSiteY₀ ns v₀ vs lam h K₀ K := by
  classical
  have hle : ∀ i, ns i ≤ 1 := fun i => (hlt i).le
  -- the one-site recursion at site `i`, as a function of the root marks
  set f : (J' → ℝ) → ℝ := fun y₀ => parisiRec κ ns (siteGaussianMarks J' κ vs)
    (pairSiteF lam h K₀ K y₀) with hf
  have hfm : Measurable f := by
    have hc := (continuous_pairSiteF lam h K₀ K)
    have hG : Measurable (Function.uncurry fun (y₀ : J' → ℝ) (y : Fin κ → J' → ℝ) =>
        ENNReal.ofReal (Real.exp (pairSiteF lam h K₀ K y₀ y))) := by
      have h := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hc.measurable)
      exact h
    have hR : Measurable fun y₀ : J' → ℝ => cascadeRec κ ns (siteGaussianMarks J' κ vs)
        (fun y => ENNReal.ofReal (Real.exp (pairSiteF lam h K₀ K y₀ y))) :=
      measurable_cascadeRec_prod κ ns (siteGaussianMarks J' κ vs) hG
    exact hR.ennreal_toReal.log
  have hf0 : ∀ y₀, 0 ≤ f y₀ := fun y₀ =>
    parisiRec_nonneg κ ns _ (fun y => pairSiteF_nonneg lam h K₀ K y₀ y) hpos
  -- the site factorization, pointwise
  have hsum : ∀ z₀ : Fin N × J' → ℝ, parisiRec κ ns (siteGaussianMarks (Fin N × J') κ vs)
      (pairCoshF N κ lam (fun s => h s.2) K₀ K z₀) = ∑ i, f (fun j => z₀ (i, j)) := fun z₀ =>
    parisiRec_pairCoshF N ns hpos hle vs lam (fun s => h s.2) K₀ K z₀
  -- each site term is dominated by the (integrable) sum
  have hY := integrable_parisiRec_pairCoshF_rootMarksLaw N ns hsm hpos hlt lam (fun s => h s.2)
    K₀ K v₀ vs
  have hcoord : ∀ i : Fin N, Measurable fun z₀ : Fin N × J' → ℝ => fun j => z₀ (i, j) :=
    fun i => measurable_pi_lambda _ fun j => measurable_pi_apply (i, j)
  have hterm : ∀ i : Fin N, Integrable (fun z₀ : Fin N × J' → ℝ => f (fun j => z₀ (i, j)))
      (rootMarksLaw N v₀) := by
    intro i
    refine hY.mono' (hfm.comp (hcoord i)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z₀ => ?_)
    rw [hsum z₀, Real.norm_eq_abs, abs_of_nonneg (hf0 _)]
    exact Finset.single_le_sum (f := fun i => f (fun j => z₀ (i, j)))
      (fun i _ => hf0 _) (Finset.mem_univ i)
  -- the law of the root marks at one site
  have hsite : ∀ i : Fin N, ∫ z₀, f (fun j => z₀ (i, j)) ∂rootMarksLaw N v₀
      = ∫ y₀, f y₀ ∂Measure.pi fun _ : J' => gaussianReal 0 v₀ := by
    intro i
    have hg : Function.Injective fun j : J' => ((i, j) : Fin N × J') :=
      fun j j' hjj' => (Prod.mk.inj hjj').2
    have hmap := map_comp_pi_of_injective (gaussianReal 0 v₀) hg
    rw [← hmap, integral_map (measurable_comp_right (E := ℝ) _).aemeasurable
      hfm.aestronglyMeasurable]
    rfl
  rw [integral_congr_ae (Filter.Eventually.of_forall hsum), integral_finsetSum _ fun i _ => hterm i,
    Finset.sum_congr rfl fun i _ => hsite i, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rfl

end

end SpinGlass
