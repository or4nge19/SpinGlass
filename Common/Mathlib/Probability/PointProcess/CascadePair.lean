/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Common.Mathlib.Data.ENNReal.DivPow
import Common.Mathlib.Probability.PointProcess.CascadeSecondMoment

/-!
# Pairs of branches of a cascade

Talagrand, *Mean Field Models for Spin Glasses*, Vol. II, §14.3, (14.40)–(14.47). The identities
of §14.3 culminate in a statement about a general function `Ũ(α, γ)` of the *pair* of mark
sequences along two branches, rather than a product `U(α) U'(γ)`. This file builds the two objects
that statement is about.

* `cascadePairSum k Ũ ω₁ ω₂ = ∑_{α, γ} u*_α u*_γ Ũ(z_α, z_γ)`, the double sum over one branch of
  each of two cascades, and `cascadeSqPair k r Ũ ω`, its restriction to pairs of branches of the
  *same* cascade agreeing up to level `r`. For a product `Ũ = A ⊗ A'` they factor into
  `cascadeSum` and reduce to `cascadeSq` (`cascadePairSum_prod`, `cascadeSqPair_prod`).

* `cascadeTiltProd k ms μs G₁ G₂ Ũ = 𝔼(W₁¹ W₁² ⋯ W_k¹ W_k² Ũ)`, the tilted average over **two
  independent copies** of the marks — note the two functions `G₁`, `G₂`, since at the next level
  copy `ℓ` is tilted by `G_ℓ(z_ℓ, ·)` — and `cascadeTiltPair k r ms μs G Ũ`, which uses a single
  `W_p` at the levels `p ≤ r` and the two independent copies from level `r + 1` on. This is
  Talagrand's coupling (14.40)–(14.41).

The bridge between the two tilted objects is **Talagrand's (14.42)**,
`𝔼(W₁ ⋯ W_r (𝔼_{r+1} W_{r+1} ⋯ W_k A)²) = 𝔼(W₁ ⋯ W_r W_{r+1}¹ W_{r+1}² ⋯ W_k¹ W_k² A¹ A²)`
(`cascadeTiltPair_prod`): the square of a conditional expectation is the expectation over two
independent copies. Here it is a consequence of the definitions rather than an argument, because
the two copies are built into `cascadeTiltProd`.

On top of these, **Theorem 14.3.5** (`lintegral_cascadeSqPair_succ_add`, and its cumulative form
`lintegral_cascadeSqPair_mul_inv_sq`), proved with a free exponent
(`lintegral_cascadeSqPair_mul_rpow`) by induction on the number of levels, directly for a general
`Ũ`: Talagrand polarizes from the product case and then approximates, and neither step is needed
here. The check that the identity specializes to (14.33) at `Ũ = A ⊗ A` — two separate
inductions agreeing — is `lintegral_cascadeSqPair_mul_inv_sq_prod`.

Finally **Lemma 14.3.6 and Corollary 14.3.7**. The coupled construction (14.40) is an *ordinary*
cascade on the mark space `T × T`, whose mark law at level `p` is the diagonal image of `μ_p` for
`p < r` and the product `μ_p ⊗ μ_p` for `p ≥ r` (`pairMarkLaw`), and whose parameters are the
halved sequence (14.48) (`halveBelow`). Lemma 14.3.6(a), `J_p = F_p¹ + F_p²`, becomes
`cascadeRec_pairMarkLaw`: the recursion of `Ĝ = G ⊗ G` is the *square* of the recursion of `G` —
its independent half is the factorization `cascadeRec_prod`. Lemma 14.3.6(b) becomes
`cascadeW_prod` (`V_p = W_p¹ W_p²` for `p ≥ r`) and `cascadeW_pairMarkLaw_diag`
(`V_p = W_p` for `p < r`). Corollary 14.3.7 is then `cascadeTiltPair_eq_cascadeTilt`: the coupled
tilted average *is* the tilted average of that ordinary cascade, so that (14.27) applies to it
and turns it into a cascade Gibbs average (`cascadeTiltPair_eq_lintegral_cascadeSum_div`,
Talagrand's (14.54)) — the entry point of §14.5.
-/

open MeasureTheory Set Filter Function
open scoped ENNReal Topology BigOperators

namespace ProbabilityTheory

open ENNReal

universe u

variable {T : Type u} [MeasurableSpace T]

noncomputable section

/-! ### The double sum over a branch of each of two cascades -/

/-- `∑_{α, γ} u*_α u*_γ Ũ(z_α, z_γ)`, the sum over one branch `α` of the first cascade and one
branch `γ` of the second. -/
def cascadePairSum : (k : ℕ) → ((Fin k → T × T) → ℝ≥0∞) → CascadeSpace T k → CascadeSpace T k →
    ℝ≥0∞
  | 0, U, _, _ => U Fin.elim0
  | k + 1, U, ω₁, ω₂ =>
    ∫⁻ p : ℝ × (T × CascadeSpace T k), ∫⁻ q : ℝ × (T × CascadeSpace T k),
      ENNReal.ofReal p.1 * ENNReal.ofReal q.1
        * cascadePairSum k (fun zs => U (Fin.cons (p.2.1, q.2.1) zs)) p.2.2 q.2.2
      ∂superCounting ω₂ ∂superCounting ω₁

@[simp] lemma cascadePairSum_zero (U : (Fin 0 → T × T) → ℝ≥0∞) (ω₁ ω₂ : CascadeSpace T 0) :
    cascadePairSum 0 U ω₁ ω₂ = U Fin.elim0 := rfl

lemma cascadePairSum_succ (k : ℕ) (U : (Fin (k + 1) → T × T) → ℝ≥0∞)
    (ω₁ ω₂ : CascadeSpace T (k + 1)) :
    cascadePairSum (k + 1) U ω₁ ω₂
      = ∫⁻ p : ℝ × (T × CascadeSpace T k), ∫⁻ q : ℝ × (T × CascadeSpace T k),
          ENNReal.ofReal p.1 * ENNReal.ofReal q.1
            * cascadePairSum k (fun zs => U (Fin.cons (p.2.1, q.2.1) zs)) p.2.2 q.2.2
          ∂superCounting ω₂ ∂superCounting ω₁ := rfl

/-- Taking the first coordinate of a sequence of pairs is measurable. -/
lemma measurable_pairFst {n : ℕ} :
    Measurable fun zs : Fin n → T × T => (fun i => (zs i).1) :=
  measurable_pi_lambda _ fun i => measurable_fst.comp (measurable_pi_apply i)

/-- Taking the second coordinate of a sequence of pairs is measurable. -/
lemma measurable_pairSnd {n : ℕ} :
    Measurable fun zs : Fin n → T × T => (fun i => (zs i).2) :=
  measurable_pi_lambda _ fun i => measurable_snd.comp (measurable_pi_apply i)

omit [MeasurableSpace T] in
/-- The first coordinates of `Fin.cons` on pairs. -/
lemma fin_cons_fst {n : ℕ} (a : T × T) (zs : Fin n → T × T) :
    (fun i => ((Fin.cons a zs : Fin (n + 1) → T × T) i).1)
      = (Fin.cons a.1 (fun j => (zs j).1) : Fin (n + 1) → T) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [Fin.cons_zero, Fin.cons_zero]
  · rw [Fin.cons_succ, Fin.cons_succ]

omit [MeasurableSpace T] in
/-- The second coordinates of `Fin.cons` on pairs. -/
lemma fin_cons_snd {n : ℕ} (a : T × T) (zs : Fin n → T × T) :
    (fun i => ((Fin.cons a zs : Fin (n + 1) → T × T) i).2)
      = (Fin.cons a.2 (fun j => (zs j).2) : Fin (n + 1) → T) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [Fin.cons_zero, Fin.cons_zero]
  · rw [Fin.cons_succ, Fin.cons_succ]

/-- Joint measurability of the double sum in a parameter and the two samples. -/
lemma measurable_cascadePairSum_prod (k : ℕ) :
    ∀ {α : Type u} [MeasurableSpace α] {U : α → (Fin k → T × T) → ℝ≥0∞},
      Measurable (uncurry U) →
        Measurable fun q : α × (CascadeSpace T k × CascadeSpace T k) =>
          cascadePairSum k (U q.1) q.2.1 q.2.2 := by
  induction k with
  | zero =>
    intro α _ U hU
    simp only [cascadePairSum_zero]
    exact hU.comp (measurable_fst.prodMk measurable_const)
  | succ k ih =>
    intro α _ U hU
    simp only [cascadePairSum_succ]
    have hU' : Measurable (uncurry fun q : α × (T × T) => fun zs : Fin k → T × T =>
        U q.1 (Fin.cons q.2 zs)) :=
      hU.comp ((measurable_fst.comp measurable_fst).prodMk
        (measurable_fin_cons.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
    have h1 := ih (α := α × (T × T)) (U := fun q zs => U q.1 (Fin.cons q.2 zs)) hU'
    -- the integrand, in (parameter, first point, second point)
    have hF : Measurable fun z : (α × (ℝ × (T × CascadeSpace T k)))
          × (ℝ × (T × CascadeSpace T k)) =>
        ENNReal.ofReal z.1.2.1 * ENNReal.ofReal z.2.1
          * cascadePairSum k (fun zs => U z.1.1 (Fin.cons (z.1.2.2.1, z.2.2.1) zs))
              z.1.2.2.2 z.2.2.2 := by
      refine ((ENNReal.measurable_ofReal.comp (measurable_fst.comp
        (measurable_snd.comp measurable_fst))).mul
        (ENNReal.measurable_ofReal.comp (measurable_fst.comp measurable_snd))).mul ?_
      exact h1.comp ((((measurable_fst.comp measurable_fst).prodMk
        ((measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))).prodMk
          (measurable_fst.comp (measurable_snd.comp measurable_snd))))).prodMk
        ((measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))).prodMk
          (measurable_snd.comp (measurable_snd.comp measurable_snd))))
    have h2 : Measurable fun w : (α × (ℝ × (T × CascadeSpace T k)))
          × CascadeSpace T (k + 1) =>
        ∫⁻ q : ℝ × (T × CascadeSpace T k), ENNReal.ofReal w.1.2.1 * ENNReal.ofReal q.1
          * cascadePairSum k (fun zs => U w.1.1 (Fin.cons (w.1.2.2.1, q.2.1) zs))
              w.1.2.2.2 q.2.2 ∂superCounting w.2 :=
      measurable_lintegral_superCounting_prod hF
    have hmap3 : Measurable fun w : (α × CascadeSpace T (k + 1))
          × (ℝ × (T × CascadeSpace T k)) => ((w.1.1, w.2), w.1.2) :=
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
        (measurable_snd.comp measurable_fst)
    have h3 : Measurable fun w : (α × CascadeSpace T (k + 1))
          × (ℝ × (T × CascadeSpace T k)) =>
        ∫⁻ q : ℝ × (T × CascadeSpace T k), ENNReal.ofReal w.2.1 * ENNReal.ofReal q.1
          * cascadePairSum k (fun zs => U w.1.1 (Fin.cons (w.2.2.1, q.2.1) zs))
              w.2.2.2 q.2.2 ∂superCounting w.1.2 := by
      have h := h2.comp hmap3
      simp only [Function.comp_def] at h
      exact h
    have h4 : Measurable fun w : (α × CascadeSpace T (k + 1)) × CascadeSpace T (k + 1) =>
        ∫⁻ p : ℝ × (T × CascadeSpace T k), ∫⁻ q : ℝ × (T × CascadeSpace T k),
          ENNReal.ofReal p.1 * ENNReal.ofReal q.1
            * cascadePairSum k (fun zs => U w.1.1 (Fin.cons (p.2.1, q.2.1) zs)) p.2.2 q.2.2
          ∂superCounting w.1.2 ∂superCounting w.2 :=
      measurable_lintegral_superCounting_prod h3
    have hmap : Measurable fun q : α × (CascadeSpace T (k + 1) × CascadeSpace T (k + 1)) =>
        ((q.1, q.2.2), q.2.1) :=
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd)).prodMk
        (measurable_fst.comp measurable_snd)
    have h5 := h4.comp hmap
    simp only [Function.comp_def] at h5
    exact h5

lemma measurable_cascadePairSum {k : ℕ} {U : (Fin k → T × T) → ℝ≥0∞} (hU : Measurable U) :
    Measurable fun q : CascadeSpace T k × CascadeSpace T k => cascadePairSum k U q.1 q.2 := by
  have h := measurable_cascadePairSum_prod k (α := PUnit.{u + 1}) (U := fun _ => U)
    (hU.comp measurable_snd)
  exact h.comp (measurable_const.prodMk measurable_id :
    Measurable fun q : CascadeSpace T k × CascadeSpace T k => (PUnit.unit, q))

/-- **The double sum factors for a product**: `∑_{α,γ} u*_α u*_γ A(z_α) A'(z_γ)
= (∑_α u*_α A(z_α))(∑_γ u*_γ A'(z_γ))`. -/
theorem cascadePairSum_prod : ∀ (k : ℕ) {A A' : (Fin k → T) → ℝ≥0∞}, Measurable A →
    Measurable A' → ∀ ω₁ ω₂ : CascadeSpace T k,
    cascadePairSum k (fun zs => A (fun i => (zs i).1) * A' (fun i => (zs i).2)) ω₁ ω₂
      = cascadeSum k A ω₁ * cascadeSum k A' ω₂
  | 0, A, A', _, _, ω₁, ω₂ => by
      simp only [cascadePairSum_zero, cascadeSum_zero]
      congr 1 <;> exact congrArg _ (Subsingleton.elim _ _)
  | k + 1, A, A', hA, hA', ω₁, ω₂ => by
      rw [cascadePairSum_succ, cascadeSum_succ, cascadeSum_succ, pdSum, pdSum]
      have hvA : Measurable fun p : ℝ × (T × CascadeSpace T k) =>
          ENNReal.ofReal p.1 * cascadeSum k (fun zs => A (Fin.cons p.2.1 zs)) p.2.2 :=
        (ENNReal.measurable_ofReal.comp measurable_fst).mul
          ((measurable_cascadeSum_prod k (α := T) (G := fun z zs => A (Fin.cons z zs))
            (hA.comp measurable_fin_cons)).comp measurable_snd)
      have hvA' : Measurable fun q : ℝ × (T × CascadeSpace T k) =>
          ENNReal.ofReal q.1 * cascadeSum k (fun zs => A' (Fin.cons q.2.1 zs)) q.2.2 :=
        (ENNReal.measurable_ofReal.comp measurable_fst).mul
          ((measurable_cascadeSum_prod k (α := T) (G := fun z zs => A' (Fin.cons z zs))
            (hA'.comp measurable_fin_cons)).comp measurable_snd)
      rw [← lintegral_mul_const _ hvA]
      refine lintegral_congr fun p => ?_
      have hcons : ∀ (p q : ℝ × (T × CascadeSpace T k)) (zs : Fin k → T × T),
          (fun zs : Fin (k + 1) → T × T => A (fun i => (zs i).1) * A' (fun i => (zs i).2))
              (Fin.cons (p.2.1, q.2.1) zs)
            = A (Fin.cons p.2.1 (fun i => (zs i).1))
              * A' (Fin.cons q.2.1 (fun i => (zs i).2)) := by
        intro p q zs
        simp only
        rw [fin_cons_fst (p.2.1, q.2.1) zs, fin_cons_snd (p.2.1, q.2.1) zs]
      have hin : ∀ q : ℝ × (T × CascadeSpace T k),
          ENNReal.ofReal p.1 * ENNReal.ofReal q.1
              * cascadePairSum k (fun zs => A (Fin.cons p.2.1 (fun i => (zs i).1))
                  * A' (Fin.cons q.2.1 (fun i => (zs i).2))) p.2.2 q.2.2
            = (ENNReal.ofReal p.1 * cascadeSum k (fun zs => A (Fin.cons p.2.1 zs)) p.2.2)
              * (ENNReal.ofReal q.1
                * cascadeSum k (fun zs => A' (Fin.cons q.2.1 zs)) q.2.2) := by
        intro q
        rw [cascadePairSum_prod k (A := fun zs => A (Fin.cons p.2.1 zs))
          (A' := fun zs => A' (Fin.cons q.2.1 zs))
          (hA.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
          (hA'.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))]
        ring
      simp_rw [hcons, hin]
      exact lintegral_const_mul _ hvA'

/-! ### The restricted double sum over pairs of branches of one cascade -/

/-- `∑_{α|r = γ|r} u*_α u*_γ Ũ(z_α, z_γ)`: the pairs of branches of a single cascade that agree
up to level `r`. At `r = 0` there is no restriction; for `r > k` there are no such pairs of
distinct-prefix type and the sum is `0`. -/
def cascadeSqPair : (k : ℕ) → ℕ → ((Fin k → T × T) → ℝ≥0∞) → CascadeSpace T k → ℝ≥0∞
  | k, 0, U, ω => cascadePairSum k U ω ω
  | 0, _ + 1, _, _ => 0
  | k + 1, r + 1, U, ω =>
    ∫⁻ p : ℝ × (T × CascadeSpace T k), ENNReal.ofReal p.1 * ENNReal.ofReal p.1
      * cascadeSqPair k r (fun zs => U (Fin.cons (p.2.1, p.2.1) zs)) p.2.2 ∂superCounting ω

@[simp] lemma cascadeSqPair_zero (k : ℕ) (U : (Fin k → T × T) → ℝ≥0∞) (ω : CascadeSpace T k) :
    cascadeSqPair k 0 U ω = cascadePairSum k U ω ω := by cases k <;> rfl

lemma cascadeSqPair_zero_succ (r : ℕ) (U : (Fin 0 → T × T) → ℝ≥0∞) (ω : CascadeSpace T 0) :
    cascadeSqPair 0 (r + 1) U ω = 0 := rfl

lemma cascadeSqPair_succ (k r : ℕ) (U : (Fin (k + 1) → T × T) → ℝ≥0∞)
    (ω : CascadeSpace T (k + 1)) :
    cascadeSqPair (k + 1) (r + 1) U ω
      = ∫⁻ p : ℝ × (T × CascadeSpace T k), ENNReal.ofReal p.1 * ENNReal.ofReal p.1
          * cascadeSqPair k r (fun zs => U (Fin.cons (p.2.1, p.2.1) zs)) p.2.2
          ∂superCounting ω := rfl

/-- Joint measurability of the restricted double sum in a parameter and the sample. -/
lemma measurable_cascadeSqPair_prod (k : ℕ) :
    ∀ (r : ℕ) {α : Type u} [MeasurableSpace α] {U : α → (Fin k → T × T) → ℝ≥0∞},
      Measurable (uncurry U) →
        Measurable fun q : α × CascadeSpace T k => cascadeSqPair k r (U q.1) q.2 := by
  induction k with
  | zero =>
    intro r α _ U hU
    cases r with
    | zero =>
      simp only [cascadeSqPair_zero]
      have h := measurable_cascadePairSum_prod 0 (α := α) hU
      have hmap : Measurable fun q : α × CascadeSpace T 0 => (q.1, (q.2, q.2)) :=
        measurable_fst.prodMk (measurable_snd.prodMk measurable_snd)
      have h2 := h.comp hmap
      simp only [Function.comp_def] at h2
      exact h2
    | succ r =>
      simp only [cascadeSqPair_zero_succ]
      exact measurable_const
  | succ k ih =>
    intro r α _ U hU
    cases r with
    | zero =>
      simp only [cascadeSqPair_zero]
      have h := measurable_cascadePairSum_prod (k + 1) (α := α) hU
      have hmap : Measurable fun q : α × CascadeSpace T (k + 1) => (q.1, (q.2, q.2)) :=
        measurable_fst.prodMk (measurable_snd.prodMk measurable_snd)
      have h2 := h.comp hmap
      simp only [Function.comp_def] at h2
      exact h2
    | succ r =>
      simp only [cascadeSqPair_succ]
      have hU' : Measurable (uncurry fun q : α × T => fun zs : Fin k → T × T =>
          U q.1 (Fin.cons (q.2, q.2) zs)) :=
        hU.comp ((measurable_fst.comp measurable_fst).prodMk
          (measurable_fin_cons.comp (((measurable_snd.comp measurable_fst).prodMk
            (measurable_snd.comp measurable_fst)).prodMk measurable_snd)))
      have h1 := ih r (α := α × T) (U := fun q zs => U q.1 (Fin.cons (q.2, q.2) zs)) hU'
      have hf : Measurable fun z : α × (ℝ × (T × CascadeSpace T k)) =>
          ENNReal.ofReal z.2.1 * ENNReal.ofReal z.2.1
            * cascadeSqPair k r (fun zs => U z.1 (Fin.cons (z.2.2.1, z.2.2.1) zs)) z.2.2.2 := by
        refine ((ENNReal.measurable_ofReal.comp (measurable_fst.comp measurable_snd)).mul
          (ENNReal.measurable_ofReal.comp (measurable_fst.comp measurable_snd))).mul ?_
        exact h1.comp ((measurable_fst.prodMk (measurable_fst.comp
          (measurable_snd.comp measurable_snd))).prodMk
          (measurable_snd.comp (measurable_snd.comp measurable_snd)))
      exact measurable_lintegral_superCounting_prod hf

/-- **The restricted double sum of a product is the prefix square**:
`cascadeSqPair k r (A ⊗ A) = cascadeSq k r A`. -/
theorem cascadeSqPair_prod : ∀ (k r : ℕ) {A : (Fin k → T) → ℝ≥0∞}, Measurable A →
    ∀ ω : CascadeSpace T k,
    cascadeSqPair k r (fun zs => A (fun i => (zs i).1) * A (fun i => (zs i).2)) ω
      = cascadeSq k r A ω
  | k, 0, A, hA, ω => by
      rw [cascadeSqPair_zero, cascadeSq_zero, cascadePairSum_prod k hA hA]
  | 0, r + 1, A, _, ω => by
      rw [cascadeSqPair_zero_succ, cascadeSq_zero_succ]
  | k + 1, r + 1, A, hA, ω => by
      rw [cascadeSqPair_succ, cascadeSq_succ]
      refine lintegral_congr fun p => ?_
      have hcons : (fun zs : Fin k → T × T =>
            (fun zs : Fin (k + 1) → T × T => A (fun i => (zs i).1) * A (fun i => (zs i).2))
              (Fin.cons (p.2.1, p.2.1) zs))
          = fun zs : Fin k → T × T => A (Fin.cons p.2.1 (fun i => (zs i).1))
              * A (Fin.cons p.2.1 (fun i => (zs i).2)) := by
        funext zs
        simp only
        rw [fin_cons_fst (p.2.1, p.2.1) zs, fin_cons_snd (p.2.1, p.2.1) zs]
      rw [hcons, cascadeSqPair_prod k r (A := fun zs => A (Fin.cons p.2.1 zs))
        (hA.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))]

/-! ### The tilted average over two independent copies -/

/-- **Talagrand's (14.41)**: `𝔼(W₁¹ W₁² ⋯ W_k¹ W_k² Ũ)`, the tilted average over two independent
copies of the marks. The two copies are tilted by different functions, since at the next level
copy `ℓ` carries `G_ℓ(z_ℓ, ·)`. -/
def cascadeTiltProd : (k : ℕ) → (ms : Fin k → ℝ) → (μs : Fin k → Measure T) →
    [∀ i, IsProbabilityMeasure (μs i)] → ((Fin k → T) → ℝ≥0∞) → ((Fin k → T) → ℝ≥0∞) →
    ((Fin k → T × T) → ℝ≥0∞) → ℝ≥0∞
  | 0, _, _, _, _, _, U => U Fin.elim0
  | k + 1, ms, μs, _, G₁, G₂, U =>
      ∫⁻ z₁, ∫⁻ z₂, cascadeW k ms μs G₁ z₁ * cascadeW k ms μs G₂ z₂
        * cascadeTiltProd k (Fin.tail ms) (Fin.tail μs)
            (fun zs => G₁ (Fin.cons z₁ zs)) (fun zs => G₂ (Fin.cons z₂ zs))
            (fun zs => U (Fin.cons (z₁, z₂) zs)) ∂μs 0 ∂μs 0

@[simp] lemma cascadeTiltProd_zero (ms : Fin 0 → ℝ) (μs : Fin 0 → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] (G₁ G₂ : (Fin 0 → T) → ℝ≥0∞)
    (U : (Fin 0 → T × T) → ℝ≥0∞) : cascadeTiltProd 0 ms μs G₁ G₂ U = U Fin.elim0 := rfl

lemma cascadeTiltProd_succ (k : ℕ) (ms : Fin (k + 1) → ℝ) (μs : Fin (k + 1) → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] (G₁ G₂ : (Fin (k + 1) → T) → ℝ≥0∞)
    (U : (Fin (k + 1) → T × T) → ℝ≥0∞) :
    cascadeTiltProd (k + 1) ms μs G₁ G₂ U
      = ∫⁻ z₁, ∫⁻ z₂, cascadeW k ms μs G₁ z₁ * cascadeW k ms μs G₂ z₂
          * cascadeTiltProd k (Fin.tail ms) (Fin.tail μs)
              (fun zs => G₁ (Fin.cons z₁ zs)) (fun zs => G₂ (Fin.cons z₂ zs))
              (fun zs => U (Fin.cons (z₁, z₂) zs)) ∂μs 0 ∂μs 0 := rfl

/-- **Joint measurability of the two-copy tilted average** in a parameter. -/
theorem measurable_cascadeTiltProd_prod : ∀ (k : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {α : Type u} [MeasurableSpace α]
    {G₁s G₂s : α → (Fin k → T) → ℝ≥0∞} {Us : α → (Fin k → T × T) → ℝ≥0∞},
    Measurable (uncurry G₁s) → Measurable (uncurry G₂s) → Measurable (uncurry Us) →
    Measurable fun a => cascadeTiltProd k ms μs (G₁s a) (G₂s a) (Us a) := by
  intro k
  induction k with
  | zero =>
    intro ms μs _ α _ G₁s G₂s Us _ _ hUs
    exact hUs.comp (measurable_id.prodMk measurable_const)
  | succ k ih =>
    intro ms μs _ α _ G₁s G₂s Us hG₁ hG₂ hUs
    have hc₁ : Measurable (uncurry fun q : (α × T) × T => fun zs : Fin k → T =>
        G₁s q.1.1 (Fin.cons q.1.2 zs)) :=
      hG₁.comp ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
        (measurable_fin_cons.comp ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
          measurable_snd)))
    have hc₂ : Measurable (uncurry fun q : (α × T) × T => fun zs : Fin k → T =>
        G₂s q.1.1 (Fin.cons q.2 zs)) :=
      hG₂.comp ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
        (measurable_fin_cons.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
    have hcU : Measurable (uncurry fun q : (α × T) × T => fun zs : Fin k → T × T =>
        Us q.1.1 (Fin.cons (q.1.2, q.2) zs)) :=
      hUs.comp ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
        (measurable_fin_cons.comp
          (((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
            (measurable_snd.comp measurable_fst)).prodMk measurable_snd)))
    have hW₁ : Measurable fun q : (α × T) × T => cascadeW k ms μs (G₁s q.1.1) q.1.2 :=
      (measurable_cascadeW_prod k ms μs hG₁).comp
        ((measurable_fst.comp measurable_fst).prodMk (measurable_snd.comp measurable_fst))
    have hW₂ : Measurable fun q : (α × T) × T => cascadeW k ms μs (G₂s q.1.1) q.2 :=
      (measurable_cascadeW_prod k ms μs hG₂).comp
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    have hprod : Measurable fun q : (α × T) × T =>
        cascadeW k ms μs (G₁s q.1.1) q.1.2 * cascadeW k ms μs (G₂s q.1.1) q.2
          * cascadeTiltProd k (Fin.tail ms) (Fin.tail μs)
              (fun zs => G₁s q.1.1 (Fin.cons q.1.2 zs)) (fun zs => G₂s q.1.1 (Fin.cons q.2 zs))
              (fun zs => Us q.1.1 (Fin.cons (q.1.2, q.2) zs)) :=
      (hW₁.mul hW₂).mul (ih (Fin.tail ms) (Fin.tail μs) hc₁ hc₂ hcU)
    have h1 : Measurable fun q : α × T =>
        ∫⁻ z₂, cascadeW k ms μs (G₁s q.1) q.2 * cascadeW k ms μs (G₂s q.1) z₂
          * cascadeTiltProd k (Fin.tail ms) (Fin.tail μs)
              (fun zs => G₁s q.1 (Fin.cons q.2 zs)) (fun zs => G₂s q.1 (Fin.cons z₂ zs))
              (fun zs => Us q.1 (Fin.cons (q.2, z₂) zs)) ∂μs 0 :=
      Measurable.lintegral_prod_right' (ν := μs 0) hprod
    exact Measurable.lintegral_prod_right' (ν := μs 0) h1

/-- **The two-copy tilted average of a product factors**:
`𝔼(W₁¹W₁²⋯W_k¹W_k² (A ⊗ A')) = 𝔼(W₁⋯W_k A) · 𝔼(W₁⋯W_k A')`. -/
theorem cascadeTiltProd_prod : ∀ (k : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {G₁ G₂ A A' : (Fin k → T) → ℝ≥0∞},
    Measurable G₁ → Measurable G₂ → Measurable A → Measurable A' →
    cascadeTiltProd k ms μs G₁ G₂ (fun zs => A (fun i => (zs i).1) * A' (fun i => (zs i).2))
      = cascadeTilt k ms μs G₁ A * cascadeTilt k ms μs G₂ A' := by
  intro k
  induction k with
  | zero =>
    intro ms μs _ G₁ G₂ A A' _ _ _ _
    rw [cascadeTiltProd_zero, cascadeTilt_zero, cascadeTilt_zero]
    congr 1 <;> exact congrArg _ (Subsingleton.elim _ _)
  | succ k ih =>
    intro ms μs _ G₁ G₂ A A' hG₁ hG₂ hA hA'
    rw [cascadeTiltProd_succ, cascadeTilt_succ, cascadeTilt_succ]
    have hT₂ : Measurable fun z₂ : T => cascadeW k ms μs G₂ z₂
        * cascadeTilt k (Fin.tail ms) (Fin.tail μs) (fun zs => G₂ (Fin.cons z₂ zs))
            (fun zs => A' (Fin.cons z₂ zs)) :=
      (measurable_cascadeW k ms μs hG₂).mul
        (measurable_cascadeTilt_prod k (Fin.tail ms) (Fin.tail μs)
          (Gs := fun z zs => G₂ (Fin.cons z zs)) (As := fun z zs => A' (Fin.cons z zs))
          (hG₂.comp measurable_fin_cons) (hA'.comp measurable_fin_cons))
    have hT₁ : Measurable fun z₁ : T => cascadeW k ms μs G₁ z₁
        * cascadeTilt k (Fin.tail ms) (Fin.tail μs) (fun zs => G₁ (Fin.cons z₁ zs))
            (fun zs => A (Fin.cons z₁ zs)) :=
      (measurable_cascadeW k ms μs hG₁).mul
        (measurable_cascadeTilt_prod k (Fin.tail ms) (Fin.tail μs)
          (Gs := fun z zs => G₁ (Fin.cons z zs)) (As := fun z zs => A (Fin.cons z zs))
          (hG₁.comp measurable_fin_cons) (hA.comp measurable_fin_cons))
    have hz : ∀ z₁ : T, ∫⁻ z₂, cascadeW k ms μs G₁ z₁ * cascadeW k ms μs G₂ z₂
          * cascadeTiltProd k (Fin.tail ms) (Fin.tail μs)
              (fun zs => G₁ (Fin.cons z₁ zs)) (fun zs => G₂ (Fin.cons z₂ zs))
              (fun zs => (fun zs : Fin (k + 1) → T × T =>
                A (fun i => (zs i).1) * A' (fun i => (zs i).2)) (Fin.cons (z₁, z₂) zs)) ∂μs 0
        = (cascadeW k ms μs G₁ z₁
            * cascadeTilt k (Fin.tail ms) (Fin.tail μs) (fun zs => G₁ (Fin.cons z₁ zs))
                (fun zs => A (Fin.cons z₁ zs)))
          * ∫⁻ z₂, cascadeW k ms μs G₂ z₂
              * cascadeTilt k (Fin.tail ms) (Fin.tail μs) (fun zs => G₂ (Fin.cons z₂ zs))
                  (fun zs => A' (Fin.cons z₂ zs)) ∂μs 0 := by
      intro z₁
      rw [← lintegral_const_mul _ hT₂]
      refine lintegral_congr fun z₂ => ?_
      have hcons : (fun zs : Fin k → T × T => (fun zs : Fin (k + 1) → T × T =>
              A (fun i => (zs i).1) * A' (fun i => (zs i).2)) (Fin.cons (z₁, z₂) zs))
          = fun zs : Fin k → T × T => A (Fin.cons z₁ (fun i => (zs i).1))
              * A' (Fin.cons z₂ (fun i => (zs i).2)) := by
        funext zs
        simp only
        rw [fin_cons_fst (z₁, z₂) zs, fin_cons_snd (z₁, z₂) zs]
      rw [hcons, ih (Fin.tail ms) (Fin.tail μs)
        (G₁ := fun zs => G₁ (Fin.cons z₁ zs)) (G₂ := fun zs => G₂ (Fin.cons z₂ zs))
        (A := fun zs => A (Fin.cons z₁ zs)) (A' := fun zs => A' (Fin.cons z₂ zs))
        (hG₁.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
        (hG₂.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
        (hA.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
        (hA'.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))]
      ring
    simp_rw [hz]
    exact lintegral_mul_const _ hT₁

/-! ### The coupled tilted average -/

/-- **Talagrand's coupling (14.40)–(14.41)**: `𝔼(W₁ ⋯ W_r W_{r+1}¹ W_{r+1}² ⋯ W_k¹ W_k² Ũ)`, a
single copy of the marks at the first `r` levels and two independent copies from level `r + 1`
on. -/
def cascadeTiltPair : (k : ℕ) → ℕ → (ms : Fin k → ℝ) → (μs : Fin k → Measure T) →
    [∀ i, IsProbabilityMeasure (μs i)] → ((Fin k → T) → ℝ≥0∞) →
    ((Fin k → T × T) → ℝ≥0∞) → ℝ≥0∞
  | k, 0, ms, μs, _, G, U => cascadeTiltProd k ms μs G G U
  | 0, _ + 1, _, _, _, _, U => U Fin.elim0
  | k + 1, r + 1, ms, μs, _, G, U =>
      ∫⁻ z, cascadeW k ms μs G z
        * cascadeTiltPair k r (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs))
            (fun zs => U (Fin.cons (z, z) zs)) ∂μs 0

@[simp] lemma cascadeTiltPair_zero (k : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] (G : (Fin k → T) → ℝ≥0∞)
    (U : (Fin k → T × T) → ℝ≥0∞) :
    cascadeTiltPair k 0 ms μs G U = cascadeTiltProd k ms μs G G U := by cases k <;> rfl

lemma cascadeTiltPair_zero_levels (r : ℕ) (ms : Fin 0 → ℝ) (μs : Fin 0 → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] (G : (Fin 0 → T) → ℝ≥0∞)
    (U : (Fin 0 → T × T) → ℝ≥0∞) : cascadeTiltPair 0 r ms μs G U = U Fin.elim0 := by
  cases r <;> rfl

lemma cascadeTiltPair_succ (k r : ℕ) (ms : Fin (k + 1) → ℝ) (μs : Fin (k + 1) → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] (G : (Fin (k + 1) → T) → ℝ≥0∞)
    (U : (Fin (k + 1) → T × T) → ℝ≥0∞) :
    cascadeTiltPair (k + 1) (r + 1) ms μs G U
      = ∫⁻ z, cascadeW k ms μs G z
          * cascadeTiltPair k r (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs))
              (fun zs => U (Fin.cons (z, z) zs)) ∂μs 0 := rfl

/-- **Talagrand's (14.42)**: the square of a conditional tilted average is the coupled tilted
average of the product over two independent copies,

`𝔼(W₁ ⋯ W_r (𝔼_{r+1} W_{r+1} ⋯ W_k A)²)
  = 𝔼(W₁ ⋯ W_r W_{r+1}¹ W_{r+1}² ⋯ W_k¹ W_k² A¹ A²)`.

Talagrand obtains it from the independence of the two copies above level `r`; here it is a
consequence of the two definitions, the independence being built into `cascadeTiltProd`. -/
theorem cascadeTiltPair_prod : ∀ (k r : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {G A : (Fin k → T) → ℝ≥0∞},
    Measurable G → Measurable A →
    cascadeTiltPair k r ms μs G (fun zs => A (fun i => (zs i).1) * A (fun i => (zs i).2))
      = cascadeTiltSq k r ms μs G A := by
  intro k
  induction k with
  | zero =>
    intro r ms μs _ G A _ _
    rw [cascadeTiltPair_zero_levels, cascadeTiltSq_zero_levels, pow_two]
    congr 1 <;> exact congrArg _ (Subsingleton.elim _ _)
  | succ k ih =>
    intro r ms μs _ G A hG hA
    cases r with
    | zero =>
      rw [cascadeTiltPair_zero, cascadeTiltSq_zero,
        cascadeTiltProd_prod (k + 1) ms μs hG hG hA hA, pow_two]
    | succ r =>
      rw [cascadeTiltPair_succ, cascadeTiltSq_succ]
      refine lintegral_congr fun z => ?_
      have hcons : (fun zs : Fin k → T × T => (fun zs : Fin (k + 1) → T × T =>
              A (fun i => (zs i).1) * A (fun i => (zs i).2)) (Fin.cons (z, z) zs))
          = fun zs : Fin k → T × T => A (Fin.cons z (fun i => (zs i).1))
              * A (Fin.cons z (fun i => (zs i).2)) := by
        funext zs
        simp only
        rw [fin_cons_fst (z, z) zs, fin_cons_snd (z, z) zs]
      rw [hcons, ih r (Fin.tail ms) (Fin.tail μs) (G := fun zs => G (Fin.cons z zs))
        (A := fun zs => A (Fin.cons z zs))
        (hG.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
        (hA.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))]

/-- **Joint measurability of the coupled tilted average** in a parameter. -/
theorem measurable_cascadeTiltPair_prod : ∀ (k r : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {α : Type u} [MeasurableSpace α]
    {Gs : α → (Fin k → T) → ℝ≥0∞} {Us : α → (Fin k → T × T) → ℝ≥0∞},
    Measurable (uncurry Gs) → Measurable (uncurry Us) →
    Measurable fun a => cascadeTiltPair k r ms μs (Gs a) (Us a) := by
  intro k
  induction k with
  | zero =>
    intro r ms μs _ α _ Gs Us _ hUs
    simp_rw [cascadeTiltPair_zero_levels]
    exact hUs.comp (measurable_id.prodMk measurable_const)
  | succ k ih =>
    intro r ms μs _ α _ Gs Us hGs hUs
    cases r with
    | zero =>
      simp_rw [cascadeTiltPair_zero]
      exact measurable_cascadeTiltProd_prod (k + 1) ms μs hGs hGs hUs
    | succ r =>
      simp_rw [cascadeTiltPair_succ]
      have hcG : Measurable (uncurry fun q : α × T => fun zs : Fin k → T =>
          Gs q.1 (Fin.cons q.2 zs)) :=
        hGs.comp ((measurable_fst.comp measurable_fst).prodMk
          (measurable_fin_cons.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
      have hcU : Measurable (uncurry fun q : α × T => fun zs : Fin k → T × T =>
          Us q.1 (Fin.cons (q.2, q.2) zs)) :=
        hUs.comp ((measurable_fst.comp measurable_fst).prodMk
          (measurable_fin_cons.comp (((measurable_snd.comp measurable_fst).prodMk
            (measurable_snd.comp measurable_fst)).prodMk measurable_snd)))
      exact Measurable.lintegral_prod_right' (ν := μs 0)
        ((measurable_cascadeW_prod k ms μs hGs).mul
          (ih r (Fin.tail ms) (Fin.tail μs) hcG hcU))

variable [Nonempty T]

/-- `cascadeLaw` is a probability measure, as a *lemma*: at a literal successor `k + 1` the term
`cascadeLaw (k + 1) ms μs` reduces during instance search, so the instance is not found by
`inferInstance` and has to be applied through a statement whose index is a variable. -/
lemma isProbabilityMeasure_cascadeLaw (k : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] : IsProbabilityMeasure (cascadeLaw k ms μs) :=
  inferInstance

/-! ### The one-insertion moment for a pair of independent cascades -/

set_option maxHeartbeats 4000000 in
-- the induction unfolds nested cascade integrals with large measurability terms
set_option synthInstance.maxHeartbeats 1000000 in
set_option synthInstance.maxSize 400 in
/-- **The one-insertion moment for a pair of independent cascades**: for `0 < a < m₁`,

`𝔼 (∑_{α, γ} u*_α u*_γ Ũ(z_α, z_γ)) S_{G₁}^{a-1} S_{G₂}^{a-1}
  = 𝔼(W₁¹ W₁² ⋯ W_k¹ W_k² (Ũ / (G₁ ⊗ G₂))) · 𝔼 S_{G₁}^a · 𝔼 S_{G₂}^a`,

the two cascades being independent. It is the pair analogue of `lintegral_cascadeSum_mul_rpow`,
and is what the off-diagonal term of the second-order identity reduces to: the two inserted
points lie in independent sub-cascades, so each contributes its own first-order factor. -/
theorem lintegral_cascadePairSum_mul_rpow (k : ℕ) :
    ∀ (ms : Fin k → ℝ) (μs : Fin k → Measure T) [∀ i, IsProbabilityMeasure (μs i)]
      {U : (Fin k → T × T) → ℝ≥0∞} {G₁ G₂ : (Fin k → T) → ℝ≥0∞}, Measurable U →
      Measurable G₁ → Measurable G₂ → (∀ zs, 0 < G₁ zs) → (∀ zs, 0 < G₂ zs) →
      ∫⁻ zs, G₁ zs ∂Measure.pi μs ≠ ∞ → ∫⁻ zs, G₂ zs ∂Measure.pi μs ≠ ∞ →
      ∀ {a : ℝ}, 0 < a → StrictMono (Fin.cons a ms : Fin (k + 1) → ℝ) → (∀ i, ms i < 1) →
      ∫⁻ ω₁, ∫⁻ ω₂, cascadePairSum k U ω₁ ω₂ * cascadeSum k G₁ ω₁ ^ (a - 1)
            * cascadeSum k G₂ ω₂ ^ (a - 1) ∂cascadeLaw k ms μs ∂cascadeLaw k ms μs
        = cascadeTiltProd k ms μs G₁ G₂
            (fun zs => U zs / (G₁ (fun i => (zs i).1) * G₂ (fun i => (zs i).2)))
          * ((∫⁻ ω, cascadeSum k G₁ ω ^ a ∂cascadeLaw k ms μs)
            * ∫⁻ ω, cascadeSum k G₂ ω ^ a ∂cascadeLaw k ms μs) := by
  induction k with
  | zero =>
    intro ms μs hμs U G₁ G₂ hU hG₁ hG₂ hG₁pos hG₂pos hfin₁ hfin₂ a _ _ _
    have (i : Fin 0) : IsProbabilityMeasure (μs i) := hμs i
    have hG₁0 : G₁ Fin.elim0 ≠ 0 := (hG₁pos _).ne'
    have hG₂0 : G₂ Fin.elim0 ≠ 0 := (hG₂pos _).ne'
    have hG₁top : G₁ Fin.elim0 ≠ ∞ := by
      rw [Measure.pi_of_empty, lintegral_dirac' _ hG₁] at hfin₁
      exact fun h => hfin₁ (by rw [← h]; exact congrArg G₁ (Subsingleton.elim _ _))
    have hG₂top : G₂ Fin.elim0 ≠ ∞ := by
      rw [Measure.pi_of_empty, lintegral_dirac' _ hG₂] at hfin₂
      exact fun h => hfin₂ (by rw [← h]; exact congrArg G₂ (Subsingleton.elim _ _))
    simp only [cascadeLaw_zero, lintegral_dirac, cascadePairSum_zero, cascadeSum_zero,
      cascadeTiltProd_zero]
    have hU' : U (fun i => ((Fin.elim0 : Fin 0 → T × T) i)) = U Fin.elim0 :=
      congrArg U (Subsingleton.elim _ _)
    have he₁ : G₁ (fun i => ((Fin.elim0 : Fin 0 → T × T) i).1) = G₁ Fin.elim0 :=
      congrArg G₁ (Subsingleton.elim _ _)
    have he₂ : G₂ (fun i => ((Fin.elim0 : Fin 0 → T × T) i).2) = G₂ Fin.elim0 :=
      congrArg G₂ (Subsingleton.elim _ _)
    rw [he₁, he₂]
    rw [ENNReal.rpow_sub _ _ hG₁0 hG₁top, ENNReal.rpow_sub _ _ hG₂0 hG₂top,
      ENNReal.rpow_one, ENNReal.rpow_one, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
      ENNReal.mul_inv (Or.inl hG₁0) (Or.inl hG₁top)]
    ring
  | succ k ih =>
    intro ms μs hμs U G₁ G₂ hU hG₁ hG₂ hG₁pos hG₂pos hfin₁ hfin₂ a ha0 hsm hlt
    have (i : Fin (k + 1)) : IsProbabilityMeasure (μs i) := hμs i
    have := isProbabilityMeasure_cascadeLaw (k + 1) ms μs
    have hm : 0 < ms 0 := pos_of_strictMono_cons ha0 hsm 0
    have ham : a < ms 0 := lt_zero_of_strictMono_cons hsm
    have hm1 : ms 0 < 1 := hlt 0
    have hsm' : StrictMono (Fin.cons (ms 0) (Fin.tail ms) : Fin (k + 1) → ℝ) := by
      rw [Fin.cons_self_tail]
      exact strictMono_of_strictMono_cons hsm
    have hposAll : ∀ i, 0 < ms i := fun i => pos_of_strictMono_cons ha0 hsm i
    have hposTail : ∀ i, 0 < Fin.tail ms i := fun i => pos_of_strictMono_cons hm hsm' i
    have hfinTail₁ : ∀ᵐ z ∂μs 0,
        ∫⁻ zs, G₁ (Fin.cons z zs) ∂Measure.pi (Fin.tail μs) ≠ ∞ :=
      ae_lintegral_pi_cons_ne_top k μs hG₁ hfin₁
    have hfinTail₂ : ∀ᵐ z ∂μs 0,
        ∫⁻ zs, G₂ (Fin.cons z zs) ∂Measure.pi (Fin.tail μs) ≠ ∞ :=
      ae_lintegral_pi_cons_ne_top k μs hG₂ hfin₂
    set η := (μs 0).prod (cascadeLaw k (Fin.tail ms) (Fin.tail μs)) with hη
    set vG₁ : T × CascadeSpace T k → ℝ≥0∞ :=
      fun p => cascadeSum k (fun zs => G₁ (Fin.cons p.1 zs)) p.2 with hvG₁_def
    set vG₂ : T × CascadeSpace T k → ℝ≥0∞ :=
      fun p => cascadeSum k (fun zs => G₂ (Fin.cons p.1 zs)) p.2 with hvG₂_def
    have hvG₁ : Measurable vG₁ :=
      measurable_cascadeSum_prod k (α := T) (G := fun z zs => G₁ (Fin.cons z zs))
        (hG₁.comp measurable_fin_cons)
    have hvG₂ : Measurable vG₂ :=
      measurable_cascadeSum_prod k (α := T) (G := fun z zs => G₂ (Fin.cons z zs))
        (hG₂.comp measurable_fin_cons)
    set vB : (T × CascadeSpace T k) × (T × CascadeSpace T k) → ℝ≥0∞ :=
      fun r => cascadePairSum k (fun zs => U (Fin.cons (r.1.1, r.2.1) zs)) r.1.2 r.2.2
      with hvB_def
    have hUcons : Measurable (uncurry fun q : T × T => fun zs : Fin k → T × T =>
        U (Fin.cons q zs)) := hU.comp measurable_fin_cons
    have hvB : Measurable vB := by
      have h := measurable_cascadePairSum_prod k (α := T × T)
        (U := fun q zs => U (Fin.cons q zs)) hUcons
      have hmap : Measurable fun r : (T × CascadeSpace T k) × (T × CascadeSpace T k) =>
          ((r.1.1, r.2.1), (r.1.2, r.2.2)) :=
        ((measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)).prodMk
          ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd))
      have h2 := h.comp hmap
      simp only [Function.comp_def] at h2
      exact h2
    have hlaw := hasLaw_superCounting_cascadeLaw k ms μs
    have hVpos₁ : ∀ᵐ p ∂η, 0 < vG₁ p := by
      rw [hη, Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const hvG₁)]
      refine Filter.Eventually.of_forall fun z => ?_
      exact ae_cascadeSum_pos k (Fin.tail ms) (Fin.tail μs)
        (hG₁.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
        (fun zs => hG₁pos _) hposTail
    have hVpos₂ : ∀ᵐ p ∂η, 0 < vG₂ p := by
      rw [hη, Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const hvG₂)]
      refine Filter.Eventually.of_forall fun z => ?_
      exact ae_cascadeSum_pos k (Fin.tail ms) (Fin.tail μs)
        (hG₂.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
        (fun zs => hG₂pos _) hposTail
    have hR₁ : Measurable fun z => cascadeRec k (Fin.tail ms) (Fin.tail μs)
        (fun zs => G₁ (Fin.cons z zs)) := measurable_cascadeRec_cons k _ _ hG₁
    have hR₂ : Measurable fun z => cascadeRec k (Fin.tail ms) (Fin.tail μs)
        (fun zs => G₂ (Fin.cons z zs)) := measurable_cascadeRec_cons k _ _ hG₂
    have hQ₁ : ∀ z, ∫⁻ ω', vG₁ (z, ω') ^ ms 0 ∂cascadeLaw k (Fin.tail ms) (Fin.tail μs)
        = cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G₁ (Fin.cons z zs)) ^ ms 0
          * cascadeConst k (ms 0) (Fin.tail ms) := fun z =>
      lintegral_cascadeSum_rpow k (Fin.tail ms) (Fin.tail μs)
        (hG₁.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
        hm hsm' (fun i => hlt i.succ)
    have hQ₂ : ∀ z, ∫⁻ ω', vG₂ (z, ω') ^ ms 0 ∂cascadeLaw k (Fin.tail ms) (Fin.tail μs)
        = cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G₂ (Fin.cons z zs)) ^ ms 0
          * cascadeConst k (ms 0) (Fin.tail ms) := fun z =>
      lintegral_cascadeSum_rpow k (Fin.tail ms) (Fin.tail μs)
        (hG₂.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
        hm hsm' (fun i => hlt i.succ)
    have hQ₁' : ∀ z, ∫⁻ ω, cascadeSum k (fun zs => G₁ (Fin.cons z zs)) ω ^ ms 0
        ∂cascadeLaw k (Fin.tail ms) (Fin.tail μs)
        = cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G₁ (Fin.cons z zs)) ^ ms 0
          * cascadeConst k (ms 0) (Fin.tail ms) := hQ₁
    have hQ₂' : ∀ z, ∫⁻ ω, cascadeSum k (fun zs => G₂ (Fin.cons z zs)) ω ^ ms 0
        ∂cascadeLaw k (Fin.tail ms) (Fin.tail μs)
        = cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G₂ (Fin.cons z zs)) ^ ms 0
          * cascadeConst k (ms 0) (Fin.tail ms) := hQ₂
    obtain ⟨hCk0, hCktop⟩ := cascadeConst_pos_ne_top k hm hsm' (fun i => hlt i.succ)
    set R₁ := cascadeRec (k + 1) ms μs G₁ with hR₁def
    set R₂ := cascadeRec (k + 1) ms μs G₂ with hR₂def
    have hR₁0 : R₁ ≠ 0 := (cascadeRec_pos (k + 1) ms μs hG₁ hG₁pos hposAll).ne'
    have hR₂0 : R₂ ≠ 0 := (cascadeRec_pos (k + 1) ms μs hG₂ hG₂pos hposAll).ne'
    have hR₁top : R₁ ≠ ∞ := cascadeRec_ne_top (k + 1) ms μs hG₁ hposAll (fun i => (hlt i).le) hfin₁
    have hR₂top : R₂ ≠ ∞ := cascadeRec_ne_top (k + 1) ms μs hG₂ hposAll (fun i => (hlt i).le) hfin₂
    have hR₁m0 : R₁ ^ ms 0 ≠ 0 := by
      simpa using (ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.2 hR₁0) hm.le).ne'
    have hR₂m0 : R₂ ^ ms 0 ≠ 0 := by
      simpa using (ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.2 hR₂0) hm.le).ne'
    have hR₁mtop : R₁ ^ ms 0 ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hm.le hR₁top
    have hR₂mtop : R₂ ^ ms 0 ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hm.le hR₂top
    have hκ₁ : ∫⁻ p, vG₁ p ^ ms 0 ∂η = cascadeConst k (ms 0) (Fin.tail ms) * R₁ ^ ms 0 := by
      rw [hη, lintegral_prod (fun p : T × CascadeSpace T k => vG₁ p ^ ms 0)
        (hvG₁.pow_const _).aemeasurable]
      simp_rw [hQ₁]
      rw [lintegral_mul_const _ (hR₁.pow_const _), hR₁def, cascadeRec_succ, ← ENNReal.rpow_mul,
        one_div_mul_cancel hm.ne', ENNReal.rpow_one, mul_comm]
    have hκ₂ : ∫⁻ p, vG₂ p ^ ms 0 ∂η = cascadeConst k (ms 0) (Fin.tail ms) * R₂ ^ ms 0 := by
      rw [hη, lintegral_prod (fun p : T × CascadeSpace T k => vG₂ p ^ ms 0)
        (hvG₂.pow_const _).aemeasurable]
      simp_rw [hQ₂]
      rw [lintegral_mul_const _ (hR₂.pow_const _), hR₂def, cascadeRec_succ, ← ENNReal.rpow_mul,
        one_div_mul_cancel hm.ne', ENNReal.rpow_one, mul_comm]
    have hκtop₁ : ∫⁻ p, vG₁ p ^ ms 0 ∂η ≠ ∞ := by
      rw [hκ₁]; exact ENNReal.mul_ne_top hCktop hR₁mtop
    have hκtop₂ : ∫⁻ p, vG₂ p ^ ms 0 ∂η ≠ ∞ := by
      rw [hκ₂]; exact ENNReal.mul_ne_top hCktop hR₂mtop
    -- the one-insertion identity, in transported form
    have hins : ∀ {C V : T × CascadeSpace T k → ℝ≥0∞}, Measurable C → Measurable V →
        (∀ᵐ p ∂η, 0 < V p) → (∫⁻ p, V p ^ ms 0 ∂η ≠ ∞) →
        ∫⁻ ω, pdSum C (superCounting ω) * pdSum V (superCounting ω) ^ (a - 1)
            ∂cascadeLaw (k + 1) ms μs
          = ENNReal.ofReal (pdOneConst (ms 0) a (stableConst (ms 0))
              (∫⁻ p, V p ^ ms 0 ∂η).toReal) * ∫⁻ g, C g * V g ^ (ms 0 - 1) ∂η := by
      intro C V hC hV hVpos hVκ
      have hf : Measurable fun N : Measure (ℝ × (T × CascadeSpace T k)) =>
          pdSum C N * pdSum V N ^ (a - 1) :=
        (measurable_pdSum hC).mul ((measurable_pdSum hV).pow_const _)
      rw [hlaw.lintegral_comp hf.aemeasurable]
      exact lintegral_pdSum_mul_rpow_pdSum hm hm1 η hC hV hVpos hVκ ham
    have hmom : ∀ {V : T × CascadeSpace T k → ℝ≥0∞}, Measurable V → (∀ᵐ p ∂η, 0 < V p) →
        (∫⁻ p, V p ^ ms 0 ∂η ≠ ∞) →
        ∫⁻ ω, pdSum V (superCounting ω) ^ a ∂cascadeLaw (k + 1) ms μs
          = ENNReal.ofReal (pdOneConst (ms 0) a (stableConst (ms 0))
              (∫⁻ p, V p ^ ms 0 ∂η).toReal) * ∫⁻ p, V p ^ ms 0 ∂η := by
      intro V hV hVpos hVκ
      have hf : Measurable fun N : Measure (ℝ × (T × CascadeSpace T k)) =>
          pdSum V N ^ a := (measurable_pdSum hV).pow_const _
      rw [hlaw.lintegral_comp hf.aemeasurable]
      exact lintegral_pdSum_rpow_eq_pdOneConst hm hm1 η hV hVpos hVκ ham
    -- the double sum, as a first-order sum whose numerator is itself a first-order sum
    have hvBg : ∀ g : T × CascadeSpace T k,
        Measurable fun q : ℝ × (T × CascadeSpace T k) => ENNReal.ofReal q.1 * vB (g, q.2) :=
      fun g => (ENNReal.measurable_ofReal.comp measurable_fst).mul
        (hvB.comp (measurable_const.prodMk measurable_snd))
    have hpair : ∀ ω₁ ω₂ : CascadeSpace T (k + 1),
        cascadePairSum (k + 1) U ω₁ ω₂
          = pdSum (fun g => pdSum (fun g' => vB (g, g')) (superCounting ω₂))
              (superCounting ω₁) := by
      intro ω₁ ω₂
      rw [cascadePairSum_succ, pdSum]
      refine lintegral_congr fun p => ?_
      rw [pdSum, ← lintegral_const_mul _ (hvBg p.2)]
      exact lintegral_congr fun q => by rw [mul_assoc]
    have hCm : Measurable fun q : (T × CascadeSpace T k) × CascadeSpace T (k + 1) =>
        pdSum (fun g' => vB (q.1, g')) (superCounting q.2) := by
      have hf : Measurable fun r : (T × CascadeSpace T k) × (ℝ × (T × CascadeSpace T k)) =>
          ENNReal.ofReal r.2.1 * vB (r.1, r.2.2) :=
        (ENNReal.measurable_ofReal.comp (measurable_fst.comp measurable_snd)).mul
          (hvB.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
      exact measurable_lintegral_superCounting_prod hf
    have hCfix : ∀ ω₂ : CascadeSpace T (k + 1),
        Measurable fun g : T × CascadeSpace T k =>
          pdSum (fun g' => vB (g, g')) (superCounting ω₂) := by
      intro ω₂
      have hmap : Measurable fun g : T × CascadeSpace T k => (g, ω₂) :=
        measurable_id.prodMk measurable_const
      have h := hCm.comp hmap
      simp only [Function.comp_def] at h
      exact h
    have hSC₁ : Measurable fun ω : CascadeSpace T (k + 1) => pdSum vG₁ (superCounting ω) := by
      have h : Measurable (cascadeSum (k + 1) G₁) := measurable_cascadeSum (k + 1) hG₁
      exact h
    have hSC₂ : Measurable fun ω : CascadeSpace T (k + 1) => pdSum vG₂ (superCounting ω) := by
      have h : Measurable (cascadeSum (k + 1) G₂) := measurable_cascadeSum (k + 1) hG₂
      exact h
    have hint : ∀ ω₁ ω₂ : CascadeSpace T (k + 1),
        cascadePairSum (k + 1) U ω₁ ω₂ * cascadeSum (k + 1) G₁ ω₁ ^ (a - 1)
            * cascadeSum (k + 1) G₂ ω₂ ^ (a - 1)
          = pdSum (fun g => pdSum (fun g' => vB (g, g')) (superCounting ω₂)) (superCounting ω₁)
              * pdSum vG₁ (superCounting ω₁) ^ (a - 1)
            * pdSum vG₂ (superCounting ω₂) ^ (a - 1) := by
      intro ω₁ ω₂
      rw [hpair ω₁ ω₂]
      rfl
    simp_rw [hint]
    -- swap the two samples
    have hjoint0 : Measurable fun r : CascadeSpace T (k + 1) × CascadeSpace T (k + 1) =>
        pdSum (fun g => pdSum (fun g' => vB (g, g')) (superCounting r.2))
          (superCounting r.1) := by
      have hcm2 : Measurable fun z : (CascadeSpace T (k + 1) × CascadeSpace T (k + 1))
            × (ℝ × (T × CascadeSpace T k)) =>
          pdSum (fun g' => vB (z.2.2, g')) (superCounting z.1.2) := by
        have hmap : Measurable fun z : (CascadeSpace T (k + 1) × CascadeSpace T (k + 1))
            × (ℝ × (T × CascadeSpace T k)) => (z.2.2, z.1.2) :=
          (measurable_snd.comp measurable_snd).prodMk (measurable_snd.comp measurable_fst)
        have h := hCm.comp hmap
        simp only [Function.comp_def] at h
        exact h
      have hf : Measurable fun z : (CascadeSpace T (k + 1) × CascadeSpace T (k + 1))
            × (ℝ × (T × CascadeSpace T k)) =>
          ENNReal.ofReal z.2.1 * pdSum (fun g' => vB (z.2.2, g')) (superCounting z.1.2) :=
        (ENNReal.measurable_ofReal.comp (measurable_fst.comp measurable_snd)).mul hcm2
      have h := measurable_lintegral_superCounting_prod hf
      have hmap : Measurable fun r : CascadeSpace T (k + 1) × CascadeSpace T (k + 1) =>
          (r, r.1) := measurable_id.prodMk measurable_fst
      have h2 := h.comp hmap
      simp only [Function.comp_def] at h2
      exact h2
    have hjoint : Measurable fun r : CascadeSpace T (k + 1) × CascadeSpace T (k + 1) =>
        pdSum (fun g => pdSum (fun g' => vB (g, g')) (superCounting r.2)) (superCounting r.1)
            * pdSum vG₁ (superCounting r.1) ^ (a - 1)
          * pdSum vG₂ (superCounting r.2) ^ (a - 1) :=
      (hjoint0.mul ((hSC₁.comp measurable_fst).pow_const _)).mul
        ((hSC₂.comp measurable_snd).pow_const _)
    rw [lintegral_lintegral_swap (μ := cascadeLaw (k + 1) ms μs)
      (ν := cascadeLaw (k + 1) ms μs)
      (f := fun ω₁ ω₂ : CascadeSpace T (k + 1) =>
        pdSum (fun g => pdSum (fun g' => vB (g, g')) (superCounting ω₂)) (superCounting ω₁)
            * pdSum vG₁ (superCounting ω₁) ^ (a - 1)
          * pdSum vG₂ (superCounting ω₂) ^ (a - 1)) hjoint.aemeasurable]
    -- the one-insertion identity in the first sample
    have hω₂ : ∀ ω₂ : CascadeSpace T (k + 1),
        ∫⁻ ω₁, pdSum (fun g => pdSum (fun g' => vB (g, g')) (superCounting ω₂))
              (superCounting ω₁) * pdSum vG₁ (superCounting ω₁) ^ (a - 1)
            * pdSum vG₂ (superCounting ω₂) ^ (a - 1) ∂cascadeLaw (k + 1) ms μs
          = ENNReal.ofReal (pdOneConst (ms 0) a (stableConst (ms 0))
                (∫⁻ p, vG₁ p ^ ms 0 ∂η).toReal)
              * (∫⁻ g, pdSum (fun g' => vB (g, g')) (superCounting ω₂) * vG₁ g ^ (ms 0 - 1) ∂η)
            * pdSum vG₂ (superCounting ω₂) ^ (a - 1) := by
      intro ω₂
      have hCsc : Measurable fun ω₁ : CascadeSpace T (k + 1) =>
          pdSum (fun g => pdSum (fun g' => vB (g, g')) (superCounting ω₂))
            (superCounting ω₁) := by
        have hmap : Measurable fun ω₁ : CascadeSpace T (k + 1) => (ω₁, ω₂) :=
          measurable_id.prodMk measurable_const
        have h := hjoint0.comp hmap
        simp only [Function.comp_def] at h
        exact h
      have hm₁ : Measurable fun ω₁ : CascadeSpace T (k + 1) =>
          pdSum (fun g => pdSum (fun g' => vB (g, g')) (superCounting ω₂)) (superCounting ω₁)
            * pdSum vG₁ (superCounting ω₁) ^ (a - 1) :=
        hCsc.mul (hSC₁.pow_const _)
      rw [lintegral_mul_const _ hm₁, hins (hCfix ω₂) hvG₁ hVpos₁ hκtop₁]
    simp_rw [hω₂]
    have hJ : ∫⁻ g, vG₁ g ^ (ms 0 - 1) * ∫⁻ g', vB (g, g') * vG₂ g' ^ (ms 0 - 1) ∂η ∂η
        = cascadeTiltProd (k + 1) ms μs G₁ G₂
            (fun zs => U zs / (G₁ (fun i => (zs i).1) * G₂ (fun i => (zs i).2)))
          * ((∫⁻ p, vG₁ p ^ ms 0 ∂η) * ∫⁻ p, vG₂ p ^ ms 0 ∂η) := by
      have hFm : Measurable fun r : (T × CascadeSpace T k) × (T × CascadeSpace T k) =>
          vB r * vG₁ r.1 ^ (ms 0 - 1) * vG₂ r.2 ^ (ms 0 - 1) :=
        (hvB.mul ((hvG₁.comp measurable_fst).pow_const _)).mul
          ((hvG₂.comp measurable_snd).pow_const _)
      have hLHS : ∫⁻ g, vG₁ g ^ (ms 0 - 1) * ∫⁻ g', vB (g, g') * vG₂ g' ^ (ms 0 - 1) ∂η ∂η
          = ∫⁻ g, ∫⁻ g', vB (g, g') * vG₁ g ^ (ms 0 - 1) * vG₂ g' ^ (ms 0 - 1) ∂η ∂η := by
        refine lintegral_congr fun g => ?_
        have hin : Measurable fun g' : T × CascadeSpace T k =>
            vB (g, g') * vG₂ g' ^ (ms 0 - 1) :=
          (hvB.comp (measurable_const.prodMk measurable_id)).mul (hvG₂.pow_const _)
        rw [← lintegral_const_mul _ hin]
        exact lintegral_congr fun g' => by ring
      rw [hLHS]
      have hexp : ∀ F : (T × CascadeSpace T k) → ℝ≥0∞, Measurable F →
          ∫⁻ g, F g ∂η = ∫⁻ z, ∫⁻ ω', F (z, ω')
            ∂cascadeLaw k (Fin.tail ms) (Fin.tail μs) ∂μs 0 := by
        intro F hF
        rw [hη]
        exact lintegral_prod _ hF.aemeasurable
      have hOuterM : Measurable fun g : T × CascadeSpace T k =>
          ∫⁻ g', vB (g, g') * vG₁ g ^ (ms 0 - 1) * vG₂ g' ^ (ms 0 - 1) ∂η :=
        Measurable.lintegral_prod_right' (ν := η) hFm
      rw [hexp (fun g => ∫⁻ g', vB (g, g') * vG₁ g ^ (ms 0 - 1) * vG₂ g' ^ (ms 0 - 1) ∂η)
        hOuterM]
      have hinner : ∀ (z₁ : T) (ω₁' : CascadeSpace T k),
          ∫⁻ g', vB ((z₁, ω₁'), g') * vG₁ (z₁, ω₁') ^ (ms 0 - 1) * vG₂ g' ^ (ms 0 - 1) ∂η
            = ∫⁻ z₂, ∫⁻ ω₂', vB ((z₁, ω₁'), (z₂, ω₂')) * vG₁ (z₁, ω₁') ^ (ms 0 - 1)
                * vG₂ (z₂, ω₂') ^ (ms 0 - 1) ∂cascadeLaw k (Fin.tail ms) (Fin.tail μs)
                ∂μs 0 := fun z₁ ω₁' =>
        hexp (fun g' => vB ((z₁, ω₁'), g') * vG₁ (z₁, ω₁') ^ (ms 0 - 1)
            * vG₂ g' ^ (ms 0 - 1))
          (hFm.comp ((measurable_const :
            Measurable fun _ : T × CascadeSpace T k => (z₁, ω₁')).prodMk measurable_id))
      simp_rw [hinner]
      -- exchange the first sub-cascade with the second top-level mark
      have hswapz : ∀ z₁ : T,
          ∫⁻ ω₁', ∫⁻ z₂, ∫⁻ ω₂', vB ((z₁, ω₁'), (z₂, ω₂')) * vG₁ (z₁, ω₁') ^ (ms 0 - 1)
                  * vG₂ (z₂, ω₂') ^ (ms 0 - 1)
                ∂cascadeLaw k (Fin.tail ms) (Fin.tail μs) ∂μs 0
                ∂cascadeLaw k (Fin.tail ms) (Fin.tail μs)
            = ∫⁻ z₂, ∫⁻ ω₁', ∫⁻ ω₂', vB ((z₁, ω₁'), (z₂, ω₂')) * vG₁ (z₁, ω₁') ^ (ms 0 - 1)
                  * vG₂ (z₂, ω₂') ^ (ms 0 - 1)
                ∂cascadeLaw k (Fin.tail ms) (Fin.tail μs)
                ∂cascadeLaw k (Fin.tail ms) (Fin.tail μs) ∂μs 0 := by
        intro z₁
        have hjz : Measurable fun r : CascadeSpace T k × T =>
            ∫⁻ ω₂', vB ((z₁, r.1), (r.2, ω₂')) * vG₁ (z₁, r.1) ^ (ms 0 - 1)
              * vG₂ (r.2, ω₂') ^ (ms 0 - 1) ∂cascadeLaw k (Fin.tail ms) (Fin.tail μs) := by
          refine Measurable.lintegral_prod_right'
            (ν := cascadeLaw k (Fin.tail ms) (Fin.tail μs))
            (f := fun w : (CascadeSpace T k × T) × CascadeSpace T k =>
              vB ((z₁, w.1.1), (w.1.2, w.2)) * vG₁ (z₁, w.1.1) ^ (ms 0 - 1)
                * vG₂ (w.1.2, w.2) ^ (ms 0 - 1)) ?_
          exact hFm.comp (((measurable_const : Measurable
              fun _ : (CascadeSpace T k × T) × CascadeSpace T k => z₁).prodMk
            (measurable_fst.comp measurable_fst)).prodMk
            ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
        exact lintegral_lintegral_swap
          (μ := cascadeLaw k (Fin.tail ms) (Fin.tail μs)) (ν := μs 0)
          (f := fun (ω₁' : CascadeSpace T k) (z₂ : T) =>
            ∫⁻ ω₂', vB ((z₁, ω₁'), (z₂, ω₂')) * vG₁ (z₁, ω₁') ^ (ms 0 - 1)
              * vG₂ (z₂, ω₂') ^ (ms 0 - 1) ∂cascadeLaw k (Fin.tail ms) (Fin.tail μs))
          hjz.aemeasurable
      simp_rw [hswapz]
      -- the induction hypothesis, fibrewise
      have hfib : ∀ᵐ z₁ ∂μs 0, ∀ᵐ z₂ ∂μs 0,
          ∫⁻ ω₁', ∫⁻ ω₂', vB ((z₁, ω₁'), (z₂, ω₂')) * vG₁ (z₁, ω₁') ^ (ms 0 - 1)
                * vG₂ (z₂, ω₂') ^ (ms 0 - 1)
              ∂cascadeLaw k (Fin.tail ms) (Fin.tail μs)
              ∂cascadeLaw k (Fin.tail ms) (Fin.tail μs)
            = cascadeTiltProd k (Fin.tail ms) (Fin.tail μs)
                (fun zs => G₁ (Fin.cons z₁ zs)) (fun zs => G₂ (Fin.cons z₂ zs))
                (fun zs => U (Fin.cons (z₁, z₂) zs)
                  / (G₁ (Fin.cons z₁ fun i => (zs i).1)
                    * G₂ (Fin.cons z₂ fun i => (zs i).2)))
              * ((cascadeRec k (Fin.tail ms) (Fin.tail μs)
                    (fun zs => G₁ (Fin.cons z₁ zs)) ^ ms 0
                  * cascadeConst k (ms 0) (Fin.tail ms))
                * (cascadeRec k (Fin.tail ms) (Fin.tail μs)
                    (fun zs => G₂ (Fin.cons z₂ zs)) ^ ms 0
                  * cascadeConst k (ms 0) (Fin.tail ms))) := by
        filter_upwards [hfinTail₁] with z₁ hz₁
        filter_upwards [hfinTail₂] with z₂ hz₂
        have h := ih (Fin.tail ms) (Fin.tail μs)
          (U := fun zs => U (Fin.cons (z₁, z₂) zs))
          (G₁ := fun zs => G₁ (Fin.cons z₁ zs)) (G₂ := fun zs => G₂ (Fin.cons z₂ zs))
          (hU.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
          (hG₁.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
          (hG₂.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
          (fun zs => hG₁pos _) (fun zs => hG₂pos _) hz₁ hz₂ hm hsm' (fun i => hlt i.succ)
        rw [hQ₁' z₁, hQ₂' z₂] at h
        exact h
      rw [lintegral_congr_ae (by
        filter_upwards [hfib] with z₁ hz₁
        exact lintegral_congr_ae hz₁)]
      -- the level-`(k+1)` tilted average
      have hWmul₁ : ∀ z : T, cascadeRec k (Fin.tail ms) (Fin.tail μs)
            (fun zs => G₁ (Fin.cons z zs)) ^ ms 0
          = cascadeW k ms μs G₁ z * R₁ ^ ms 0 := by
        intro z
        rw [cascadeW, ENNReal.div_rpow_of_nonneg _ _ hm.le,
          ENNReal.div_mul_cancel hR₁m0 hR₁mtop]
      have hWmul₂ : ∀ z : T, cascadeRec k (Fin.tail ms) (Fin.tail μs)
            (fun zs => G₂ (Fin.cons z zs)) ^ ms 0
          = cascadeW k ms μs G₂ z * R₂ ^ ms 0 := by
        intro z
        rw [cascadeW, ENNReal.div_rpow_of_nonneg _ _ hm.le,
          ENNReal.div_mul_cancel hR₂m0 hR₂mtop]
      have hcons : ∀ z₁ z₂ : T,
          (fun zs : Fin k → T × T => U (Fin.cons (z₁, z₂) zs)
              / (G₁ (Fin.cons z₁ fun i => (zs i).1) * G₂ (Fin.cons z₂ fun i => (zs i).2)))
            = fun zs : Fin k → T × T =>
              (fun zs : Fin (k + 1) → T × T => U zs
                / (G₁ (fun i => (zs i).1) * G₂ (fun i => (zs i).2))) (Fin.cons (z₁, z₂) zs) := by
        intro z₁ z₂
        funext zs
        simp only
        rw [fin_cons_fst (z₁, z₂) zs, fin_cons_snd (z₁, z₂) zs]
      have hUcheck : Measurable fun zs : Fin (k + 1) → T × T =>
          U zs / (G₁ (fun i => (zs i).1) * G₂ (fun i => (zs i).2)) :=
        hU.div ((hG₁.comp measurable_pairFst).mul (hG₂.comp measurable_pairSnd))
      have hTm : Measurable fun q : T × T => cascadeTiltProd k (Fin.tail ms) (Fin.tail μs)
          (fun zs => G₁ (Fin.cons q.1 zs)) (fun zs => G₂ (Fin.cons q.2 zs))
          (fun zs => (fun zs : Fin (k + 1) → T × T => U zs
            / (G₁ (fun i => (zs i).1) * G₂ (fun i => (zs i).2))) (Fin.cons q zs)) := by
        refine measurable_cascadeTiltProd_prod k (Fin.tail ms) (Fin.tail μs) ?_ ?_
          (hUcheck.comp measurable_fin_cons)
        · exact hG₁.comp (measurable_fin_cons.comp
            ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
        · exact hG₂.comp (measurable_fin_cons.comp
            ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
      have hM2 : ∀ z₁ : T, Measurable fun z₂ : T => cascadeW k ms μs G₁ z₁
          * cascadeW k ms μs G₂ z₂
          * cascadeTiltProd k (Fin.tail ms) (Fin.tail μs)
              (fun zs => G₁ (Fin.cons z₁ zs)) (fun zs => G₂ (Fin.cons z₂ zs))
              (fun zs => (fun zs : Fin (k + 1) → T × T => U zs
                / (G₁ (fun i => (zs i).1) * G₂ (fun i => (zs i).2)))
                (Fin.cons (z₁, z₂) zs)) := by
        intro z₁
        exact (measurable_const.mul (measurable_cascadeW k ms μs hG₂)).mul
          (hTm.comp (measurable_const.prodMk measurable_id))
      have hM1 : Measurable fun z₁ : T => ∫⁻ z₂, cascadeW k ms μs G₁ z₁
          * cascadeW k ms μs G₂ z₂
          * cascadeTiltProd k (Fin.tail ms) (Fin.tail μs)
              (fun zs => G₁ (Fin.cons z₁ zs)) (fun zs => G₂ (Fin.cons z₂ zs))
              (fun zs => (fun zs : Fin (k + 1) → T × T => U zs
                / (G₁ (fun i => (zs i).1) * G₂ (fun i => (zs i).2)))
                (Fin.cons (z₁, z₂) zs)) ∂μs 0 := by
        refine Measurable.lintegral_prod_right' (ν := μs 0)
          (f := fun q : T × T => cascadeW k ms μs G₁ q.1 * cascadeW k ms μs G₂ q.2
            * cascadeTiltProd k (Fin.tail ms) (Fin.tail μs)
                (fun zs => G₁ (Fin.cons q.1 zs)) (fun zs => G₂ (Fin.cons q.2 zs))
                (fun zs => (fun zs : Fin (k + 1) → T × T => U zs
                  / (G₁ (fun i => (zs i).1) * G₂ (fun i => (zs i).2)))
                  (Fin.cons q zs))) ?_
        exact (((measurable_cascadeW k ms μs hG₁).comp measurable_fst).mul
          ((measurable_cascadeW k ms μs hG₂).comp measurable_snd)).mul hTm
      rw [cascadeTiltProd_succ, hκ₁, hκ₂, ← lintegral_mul_const _ hM1]
      refine lintegral_congr fun z₁ => ?_
      rw [← lintegral_mul_const _ (hM2 z₁)]
      refine lintegral_congr fun z₂ => ?_
      rw [hWmul₁ z₁, hWmul₂ z₂, hcons z₁ z₂]
      ring
    -- pull the first constant out and exchange the mark integral with the second sample
    have hCfix' : ∀ g : T × CascadeSpace T k,
        Measurable fun g' : T × CascadeSpace T k => vB (g, g') := fun g =>
      hvB.comp (measurable_const.prodMk measurable_id)
    have hrw₁ : ∀ ω₂ : CascadeSpace T (k + 1),
        ENNReal.ofReal (pdOneConst (ms 0) a (stableConst (ms 0))
              (∫⁻ p, vG₁ p ^ ms 0 ∂η).toReal)
            * (∫⁻ g, pdSum (fun g' => vB (g, g')) (superCounting ω₂) * vG₁ g ^ (ms 0 - 1) ∂η)
          * pdSum vG₂ (superCounting ω₂) ^ (a - 1)
        = ENNReal.ofReal (pdOneConst (ms 0) a (stableConst (ms 0))
              (∫⁻ p, vG₁ p ^ ms 0 ∂η).toReal)
          * ∫⁻ g, pdSum (fun g' => vB (g, g')) (superCounting ω₂) * vG₁ g ^ (ms 0 - 1)
              * pdSum vG₂ (superCounting ω₂) ^ (a - 1) ∂η := by
      intro ω₂
      have hF : Measurable fun g : T × CascadeSpace T k =>
          pdSum (fun g' => vB (g, g')) (superCounting ω₂) * vG₁ g ^ (ms 0 - 1) :=
        (hCfix ω₂).mul (hvG₁.pow_const _)
      rw [mul_assoc, lintegral_mul_const _ hF]
    simp_rw [hrw₁]
    have hjointηP : Measurable fun r : CascadeSpace T (k + 1) × (T × CascadeSpace T k) =>
        pdSum (fun g' => vB (r.2, g')) (superCounting r.1) * vG₁ r.2 ^ (ms 0 - 1)
          * pdSum vG₂ (superCounting r.1) ^ (a - 1) := by
      have h1 : Measurable fun r : CascadeSpace T (k + 1) × (T × CascadeSpace T k) =>
          pdSum (fun g' => vB (r.2, g')) (superCounting r.1) := by
        have hmap : Measurable fun r : CascadeSpace T (k + 1) × (T × CascadeSpace T k) =>
            (r.2, r.1) := measurable_snd.prodMk measurable_fst
        have h := hCm.comp hmap
        simp only [Function.comp_def] at h
        exact h
      exact (h1.mul ((hvG₁.comp measurable_snd).pow_const _)).mul
        ((hSC₂.comp measurable_fst).pow_const _)
    rw [lintegral_const_mul _ (Measurable.lintegral_prod_right' (ν := η) hjointηP),
      lintegral_lintegral_swap (μ := cascadeLaw (k + 1) ms μs) (ν := η)
        (f := fun (ω₂ : CascadeSpace T (k + 1)) (g : T × CascadeSpace T k) =>
          pdSum (fun g' => vB (g, g')) (superCounting ω₂) * vG₁ g ^ (ms 0 - 1)
            * pdSum vG₂ (superCounting ω₂) ^ (a - 1)) hjointηP.aemeasurable]
    -- the one-insertion identity in the second sample
    have hg : ∀ g : T × CascadeSpace T k,
        ∫⁻ ω₂, pdSum (fun g' => vB (g, g')) (superCounting ω₂) * vG₁ g ^ (ms 0 - 1)
            * pdSum vG₂ (superCounting ω₂) ^ (a - 1) ∂cascadeLaw (k + 1) ms μs
          = vG₁ g ^ (ms 0 - 1) * (ENNReal.ofReal (pdOneConst (ms 0) a (stableConst (ms 0))
                (∫⁻ p, vG₂ p ^ ms 0 ∂η).toReal)
              * ∫⁻ g', vB (g, g') * vG₂ g' ^ (ms 0 - 1) ∂η) := by
      intro g
      have hre : ∀ ω₂ : CascadeSpace T (k + 1),
          pdSum (fun g' => vB (g, g')) (superCounting ω₂) * vG₁ g ^ (ms 0 - 1)
              * pdSum vG₂ (superCounting ω₂) ^ (a - 1)
            = vG₁ g ^ (ms 0 - 1) * (pdSum (fun g' => vB (g, g')) (superCounting ω₂)
                * pdSum vG₂ (superCounting ω₂) ^ (a - 1)) := fun ω₂ => by ring
      simp_rw [hre]
      have hF2 : Measurable fun ω₂ : CascadeSpace T (k + 1) =>
          pdSum (fun g' => vB (g, g')) (superCounting ω₂)
            * pdSum vG₂ (superCounting ω₂) ^ (a - 1) :=
        ((measurable_pdSum (hCfix' g)).comp measurable_superCounting).mul
          (hSC₂.pow_const _)
      rw [lintegral_const_mul _ hF2, hins (hCfix' g) hvG₂ hVpos₂ hκtop₂]
    simp_rw [hg]
    -- pull the second constant out
    have hre₂ : ∀ g : T × CascadeSpace T k,
        vG₁ g ^ (ms 0 - 1) * (ENNReal.ofReal (pdOneConst (ms 0) a (stableConst (ms 0))
              (∫⁻ p, vG₂ p ^ ms 0 ∂η).toReal)
            * ∫⁻ g', vB (g, g') * vG₂ g' ^ (ms 0 - 1) ∂η)
          = ENNReal.ofReal (pdOneConst (ms 0) a (stableConst (ms 0))
              (∫⁻ p, vG₂ p ^ ms 0 ∂η).toReal)
            * (vG₁ g ^ (ms 0 - 1) * ∫⁻ g', vB (g, g') * vG₂ g' ^ (ms 0 - 1) ∂η) :=
      fun g => by ring
    simp_rw [hre₂]
    have hmeasJ : Measurable fun g : T × CascadeSpace T k =>
        vG₁ g ^ (ms 0 - 1) * ∫⁻ g', vB (g, g') * vG₂ g' ^ (ms 0 - 1) ∂η := by
      refine (hvG₁.pow_const _).mul ?_
      exact Measurable.lintegral_prod_right' (ν := η)
        (hvB.mul ((hvG₂.comp measurable_snd).pow_const _))
    rw [lintegral_const_mul _ hmeasJ]
    -- the induction hypothesis
    have hsum₁ : ∀ ω : CascadeSpace T (k + 1),
        cascadeSum (k + 1) G₁ ω = pdSum vG₁ (superCounting ω) := fun ω => rfl
    have hsum₂ : ∀ ω : CascadeSpace T (k + 1),
        cascadeSum (k + 1) G₂ ω = pdSum vG₂ (superCounting ω) := fun ω => rfl
    simp_rw [hsum₁, hsum₂]
    rw [hmom hvG₁ hVpos₁ hκtop₁, hmom hvG₂ hVpos₂ hκtop₂, hJ]
    ring

/-- **The off-diagonal term of a two-level cascade**, `∫∫ vB vG₁^{m₁-1} vG₂^{m₁-1}`: the two
inserted points lie in independent sub-cascades, so the term is the two-copy tilted average times
the product of the two normalizers. This is the off-diagonal half of the second-order identity at
the top level of a cascade. -/
theorem lintegral_prod_cascadePairSum_mul_rpow (k : ℕ) (ms : Fin (k + 1) → ℝ)
    (μs : Fin (k + 1) → Measure T) [inst : ∀ i, IsProbabilityMeasure (μs i)]
    {U : (Fin (k + 1) → T × T) → ℝ≥0∞} {G₁ G₂ : (Fin (k + 1) → T) → ℝ≥0∞}
    (hU : Measurable U) (hG₁ : Measurable G₁) (hG₂ : Measurable G₂)
    (hG₁pos : ∀ zs, 0 < G₁ zs) (hG₂pos : ∀ zs, 0 < G₂ zs)
    (hfin₁ : ∫⁻ zs, G₁ zs ∂Measure.pi μs ≠ ∞) (hfin₂ : ∫⁻ zs, G₂ zs ∂Measure.pi μs ≠ ∞)
    (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1) :
    ∫⁻ g, (fun p : T × CascadeSpace T k =>
          cascadeSum k (fun zs => G₁ (Fin.cons p.1 zs)) p.2) g ^ (ms 0 - 1)
        * ∫⁻ g', (fun r : (T × CascadeSpace T k) × (T × CascadeSpace T k) =>
              cascadePairSum k (fun zs => U (Fin.cons (r.1.1, r.2.1) zs)) r.1.2 r.2.2) (g, g')
            * (fun p : T × CascadeSpace T k =>
              cascadeSum k (fun zs => G₂ (Fin.cons p.1 zs)) p.2) g' ^ (ms 0 - 1)
          ∂((μs 0).prod (cascadeLaw k (Fin.tail ms) (Fin.tail μs)))
        ∂((μs 0).prod (cascadeLaw k (Fin.tail ms) (Fin.tail μs)))
      = cascadeTiltProd (k + 1) ms μs G₁ G₂
          (fun zs => U zs / (G₁ (fun i => (zs i).1) * G₂ (fun i => (zs i).2)))
        * ((∫⁻ p, (fun p : T × CascadeSpace T k =>
              cascadeSum k (fun zs => G₁ (Fin.cons p.1 zs)) p.2) p ^ ms 0
              ∂((μs 0).prod (cascadeLaw k (Fin.tail ms) (Fin.tail μs))))
          * ∫⁻ p, (fun p : T × CascadeSpace T k =>
              cascadeSum k (fun zs => G₂ (Fin.cons p.1 zs)) p.2) p ^ ms 0
              ∂((μs 0).prod (cascadeLaw k (Fin.tail ms) (Fin.tail μs)))) := by
    have hm : 0 < ms 0 := hpos 0
    have hm1 : ms 0 < 1 := hlt 0
    have hsm' : StrictMono (Fin.cons (ms 0) (Fin.tail ms) : Fin (k + 1) → ℝ) := by
      rw [Fin.cons_self_tail]
      exact hsm
    have hposAll : ∀ i, 0 < ms i := hpos
    have hposTail : ∀ i, 0 < Fin.tail ms i := fun i => pos_of_strictMono_cons hm hsm' i
    have hfinTail₁ : ∀ᵐ z ∂μs 0,
        ∫⁻ zs, G₁ (Fin.cons z zs) ∂Measure.pi (Fin.tail μs) ≠ ∞ :=
      ae_lintegral_pi_cons_ne_top k μs hG₁ hfin₁
    have hfinTail₂ : ∀ᵐ z ∂μs 0,
        ∫⁻ zs, G₂ (Fin.cons z zs) ∂Measure.pi (Fin.tail μs) ≠ ∞ :=
      ae_lintegral_pi_cons_ne_top k μs hG₂ hfin₂
    set η := (μs 0).prod (cascadeLaw k (Fin.tail ms) (Fin.tail μs)) with hη
    set vG₁ : T × CascadeSpace T k → ℝ≥0∞ :=
      fun p => cascadeSum k (fun zs => G₁ (Fin.cons p.1 zs)) p.2 with hvG₁_def
    set vG₂ : T × CascadeSpace T k → ℝ≥0∞ :=
      fun p => cascadeSum k (fun zs => G₂ (Fin.cons p.1 zs)) p.2 with hvG₂_def
    have hvG₁ : Measurable vG₁ :=
      measurable_cascadeSum_prod k (α := T) (G := fun z zs => G₁ (Fin.cons z zs))
        (hG₁.comp measurable_fin_cons)
    have hvG₂ : Measurable vG₂ :=
      measurable_cascadeSum_prod k (α := T) (G := fun z zs => G₂ (Fin.cons z zs))
        (hG₂.comp measurable_fin_cons)
    set vB : (T × CascadeSpace T k) × (T × CascadeSpace T k) → ℝ≥0∞ :=
      fun r => cascadePairSum k (fun zs => U (Fin.cons (r.1.1, r.2.1) zs)) r.1.2 r.2.2
      with hvB_def
    have hUcons : Measurable (uncurry fun q : T × T => fun zs : Fin k → T × T =>
        U (Fin.cons q zs)) := hU.comp measurable_fin_cons
    have hvB : Measurable vB := by
      have h := measurable_cascadePairSum_prod k (α := T × T)
        (U := fun q zs => U (Fin.cons q zs)) hUcons
      have hmap : Measurable fun r : (T × CascadeSpace T k) × (T × CascadeSpace T k) =>
          ((r.1.1, r.2.1), (r.1.2, r.2.2)) :=
        ((measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)).prodMk
          ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd))
      have h2 := h.comp hmap
      simp only [Function.comp_def] at h2
      exact h2
    have hlaw := hasLaw_superCounting_cascadeLaw k ms μs
    have hVpos₁ : ∀ᵐ p ∂η, 0 < vG₁ p := by
      rw [hη, Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const hvG₁)]
      refine Filter.Eventually.of_forall fun z => ?_
      exact ae_cascadeSum_pos k (Fin.tail ms) (Fin.tail μs)
        (hG₁.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
        (fun zs => hG₁pos _) hposTail
    have hVpos₂ : ∀ᵐ p ∂η, 0 < vG₂ p := by
      rw [hη, Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const hvG₂)]
      refine Filter.Eventually.of_forall fun z => ?_
      exact ae_cascadeSum_pos k (Fin.tail ms) (Fin.tail μs)
        (hG₂.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
        (fun zs => hG₂pos _) hposTail
    have hR₁ : Measurable fun z => cascadeRec k (Fin.tail ms) (Fin.tail μs)
        (fun zs => G₁ (Fin.cons z zs)) := measurable_cascadeRec_cons k _ _ hG₁
    have hR₂ : Measurable fun z => cascadeRec k (Fin.tail ms) (Fin.tail μs)
        (fun zs => G₂ (Fin.cons z zs)) := measurable_cascadeRec_cons k _ _ hG₂
    have hQ₁ : ∀ z, ∫⁻ ω', vG₁ (z, ω') ^ ms 0 ∂cascadeLaw k (Fin.tail ms) (Fin.tail μs)
        = cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G₁ (Fin.cons z zs)) ^ ms 0
          * cascadeConst k (ms 0) (Fin.tail ms) := fun z =>
      lintegral_cascadeSum_rpow k (Fin.tail ms) (Fin.tail μs)
        (hG₁.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
        hm hsm' (fun i => hlt i.succ)
    have hQ₂ : ∀ z, ∫⁻ ω', vG₂ (z, ω') ^ ms 0 ∂cascadeLaw k (Fin.tail ms) (Fin.tail μs)
        = cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G₂ (Fin.cons z zs)) ^ ms 0
          * cascadeConst k (ms 0) (Fin.tail ms) := fun z =>
      lintegral_cascadeSum_rpow k (Fin.tail ms) (Fin.tail μs)
        (hG₂.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
        hm hsm' (fun i => hlt i.succ)
    have hQ₁' : ∀ z, ∫⁻ ω, cascadeSum k (fun zs => G₁ (Fin.cons z zs)) ω ^ ms 0
        ∂cascadeLaw k (Fin.tail ms) (Fin.tail μs)
        = cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G₁ (Fin.cons z zs)) ^ ms 0
          * cascadeConst k (ms 0) (Fin.tail ms) := hQ₁
    have hQ₂' : ∀ z, ∫⁻ ω, cascadeSum k (fun zs => G₂ (Fin.cons z zs)) ω ^ ms 0
        ∂cascadeLaw k (Fin.tail ms) (Fin.tail μs)
        = cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G₂ (Fin.cons z zs)) ^ ms 0
          * cascadeConst k (ms 0) (Fin.tail ms) := hQ₂
    obtain ⟨hCk0, hCktop⟩ := cascadeConst_pos_ne_top k hm hsm' (fun i => hlt i.succ)
    set R₁ := cascadeRec (k + 1) ms μs G₁ with hR₁def
    set R₂ := cascadeRec (k + 1) ms μs G₂ with hR₂def
    have hR₁0 : R₁ ≠ 0 := (cascadeRec_pos (k + 1) ms μs hG₁ hG₁pos hposAll).ne'
    have hR₂0 : R₂ ≠ 0 := (cascadeRec_pos (k + 1) ms μs hG₂ hG₂pos hposAll).ne'
    have hR₁top : R₁ ≠ ∞ := cascadeRec_ne_top (k + 1) ms μs hG₁ hposAll (fun i => (hlt i).le) hfin₁
    have hR₂top : R₂ ≠ ∞ := cascadeRec_ne_top (k + 1) ms μs hG₂ hposAll (fun i => (hlt i).le) hfin₂
    have hR₁m0 : R₁ ^ ms 0 ≠ 0 := by
      simpa using (ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.2 hR₁0) hm.le).ne'
    have hR₂m0 : R₂ ^ ms 0 ≠ 0 := by
      simpa using (ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.2 hR₂0) hm.le).ne'
    have hR₁mtop : R₁ ^ ms 0 ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hm.le hR₁top
    have hR₂mtop : R₂ ^ ms 0 ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hm.le hR₂top
    have hκ₁ : ∫⁻ p, vG₁ p ^ ms 0 ∂η = cascadeConst k (ms 0) (Fin.tail ms) * R₁ ^ ms 0 := by
      rw [hη, lintegral_prod (fun p : T × CascadeSpace T k => vG₁ p ^ ms 0)
        (hvG₁.pow_const _).aemeasurable]
      simp_rw [hQ₁]
      rw [lintegral_mul_const _ (hR₁.pow_const _), hR₁def, cascadeRec_succ, ← ENNReal.rpow_mul,
        one_div_mul_cancel hm.ne', ENNReal.rpow_one, mul_comm]
    have hκ₂ : ∫⁻ p, vG₂ p ^ ms 0 ∂η = cascadeConst k (ms 0) (Fin.tail ms) * R₂ ^ ms 0 := by
      rw [hη, lintegral_prod (fun p : T × CascadeSpace T k => vG₂ p ^ ms 0)
        (hvG₂.pow_const _).aemeasurable]
      simp_rw [hQ₂]
      rw [lintegral_mul_const _ (hR₂.pow_const _), hR₂def, cascadeRec_succ, ← ENNReal.rpow_mul,
        one_div_mul_cancel hm.ne', ENNReal.rpow_one, mul_comm]
    have hκtop₁ : ∫⁻ p, vG₁ p ^ ms 0 ∂η ≠ ∞ := by
      rw [hκ₁]; exact ENNReal.mul_ne_top hCktop hR₁mtop
    have hκtop₂ : ∫⁻ p, vG₂ p ^ ms 0 ∂η ≠ ∞ := by
      rw [hκ₂]; exact ENNReal.mul_ne_top hCktop hR₂mtop
    have hFm : Measurable fun r : (T × CascadeSpace T k) × (T × CascadeSpace T k) =>
        vB r * vG₁ r.1 ^ (ms 0 - 1) * vG₂ r.2 ^ (ms 0 - 1) :=
      (hvB.mul ((hvG₁.comp measurable_fst).pow_const _)).mul
        ((hvG₂.comp measurable_snd).pow_const _)
    have hLHS : ∫⁻ g, vG₁ g ^ (ms 0 - 1) * ∫⁻ g', vB (g, g') * vG₂ g' ^ (ms 0 - 1) ∂η ∂η
        = ∫⁻ g, ∫⁻ g', vB (g, g') * vG₁ g ^ (ms 0 - 1) * vG₂ g' ^ (ms 0 - 1) ∂η ∂η := by
      refine lintegral_congr fun g => ?_
      have hin : Measurable fun g' : T × CascadeSpace T k =>
          vB (g, g') * vG₂ g' ^ (ms 0 - 1) :=
        (hvB.comp (measurable_const.prodMk measurable_id)).mul (hvG₂.pow_const _)
      rw [← lintegral_const_mul _ hin]
      exact lintegral_congr fun g' => by ring
    rw [hLHS]
    have hexp : ∀ F : (T × CascadeSpace T k) → ℝ≥0∞, Measurable F →
        ∫⁻ g, F g ∂η = ∫⁻ z, ∫⁻ ω', F (z, ω')
          ∂cascadeLaw k (Fin.tail ms) (Fin.tail μs) ∂μs 0 := by
      intro F hF
      rw [hη]
      exact lintegral_prod _ hF.aemeasurable
    have hOuterM : Measurable fun g : T × CascadeSpace T k =>
        ∫⁻ g', vB (g, g') * vG₁ g ^ (ms 0 - 1) * vG₂ g' ^ (ms 0 - 1) ∂η :=
      Measurable.lintegral_prod_right' (ν := η) hFm
    rw [hexp (fun g => ∫⁻ g', vB (g, g') * vG₁ g ^ (ms 0 - 1) * vG₂ g' ^ (ms 0 - 1) ∂η)
      hOuterM]
    have hinner : ∀ (z₁ : T) (ω₁' : CascadeSpace T k),
        ∫⁻ g', vB ((z₁, ω₁'), g') * vG₁ (z₁, ω₁') ^ (ms 0 - 1) * vG₂ g' ^ (ms 0 - 1) ∂η
          = ∫⁻ z₂, ∫⁻ ω₂', vB ((z₁, ω₁'), (z₂, ω₂')) * vG₁ (z₁, ω₁') ^ (ms 0 - 1)
              * vG₂ (z₂, ω₂') ^ (ms 0 - 1) ∂cascadeLaw k (Fin.tail ms) (Fin.tail μs)
              ∂μs 0 := fun z₁ ω₁' =>
      hexp (fun g' => vB ((z₁, ω₁'), g') * vG₁ (z₁, ω₁') ^ (ms 0 - 1)
          * vG₂ g' ^ (ms 0 - 1))
        (hFm.comp ((measurable_const :
          Measurable fun _ : T × CascadeSpace T k => (z₁, ω₁')).prodMk measurable_id))
    simp_rw [hinner]
    -- exchange the first sub-cascade with the second top-level mark
    have hswapz : ∀ z₁ : T,
        ∫⁻ ω₁', ∫⁻ z₂, ∫⁻ ω₂', vB ((z₁, ω₁'), (z₂, ω₂')) * vG₁ (z₁, ω₁') ^ (ms 0 - 1)
                * vG₂ (z₂, ω₂') ^ (ms 0 - 1)
              ∂cascadeLaw k (Fin.tail ms) (Fin.tail μs) ∂μs 0
              ∂cascadeLaw k (Fin.tail ms) (Fin.tail μs)
          = ∫⁻ z₂, ∫⁻ ω₁', ∫⁻ ω₂', vB ((z₁, ω₁'), (z₂, ω₂')) * vG₁ (z₁, ω₁') ^ (ms 0 - 1)
                * vG₂ (z₂, ω₂') ^ (ms 0 - 1)
              ∂cascadeLaw k (Fin.tail ms) (Fin.tail μs)
              ∂cascadeLaw k (Fin.tail ms) (Fin.tail μs) ∂μs 0 := by
      intro z₁
      have hjz : Measurable fun r : CascadeSpace T k × T =>
          ∫⁻ ω₂', vB ((z₁, r.1), (r.2, ω₂')) * vG₁ (z₁, r.1) ^ (ms 0 - 1)
            * vG₂ (r.2, ω₂') ^ (ms 0 - 1) ∂cascadeLaw k (Fin.tail ms) (Fin.tail μs) := by
        refine Measurable.lintegral_prod_right'
          (ν := cascadeLaw k (Fin.tail ms) (Fin.tail μs))
          (f := fun w : (CascadeSpace T k × T) × CascadeSpace T k =>
            vB ((z₁, w.1.1), (w.1.2, w.2)) * vG₁ (z₁, w.1.1) ^ (ms 0 - 1)
              * vG₂ (w.1.2, w.2) ^ (ms 0 - 1)) ?_
        exact hFm.comp (((measurable_const : Measurable
            fun _ : (CascadeSpace T k × T) × CascadeSpace T k => z₁).prodMk
          (measurable_fst.comp measurable_fst)).prodMk
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
      exact lintegral_lintegral_swap
        (μ := cascadeLaw k (Fin.tail ms) (Fin.tail μs)) (ν := μs 0)
        (f := fun (ω₁' : CascadeSpace T k) (z₂ : T) =>
          ∫⁻ ω₂', vB ((z₁, ω₁'), (z₂, ω₂')) * vG₁ (z₁, ω₁') ^ (ms 0 - 1)
            * vG₂ (z₂, ω₂') ^ (ms 0 - 1) ∂cascadeLaw k (Fin.tail ms) (Fin.tail μs))
        hjz.aemeasurable
    simp_rw [hswapz]
    -- the induction hypothesis, fibrewise
    have hfib : ∀ᵐ z₁ ∂μs 0, ∀ᵐ z₂ ∂μs 0,
        ∫⁻ ω₁', ∫⁻ ω₂', vB ((z₁, ω₁'), (z₂, ω₂')) * vG₁ (z₁, ω₁') ^ (ms 0 - 1)
              * vG₂ (z₂, ω₂') ^ (ms 0 - 1)
            ∂cascadeLaw k (Fin.tail ms) (Fin.tail μs)
            ∂cascadeLaw k (Fin.tail ms) (Fin.tail μs)
          = cascadeTiltProd k (Fin.tail ms) (Fin.tail μs)
              (fun zs => G₁ (Fin.cons z₁ zs)) (fun zs => G₂ (Fin.cons z₂ zs))
              (fun zs => U (Fin.cons (z₁, z₂) zs)
                / (G₁ (Fin.cons z₁ fun i => (zs i).1)
                  * G₂ (Fin.cons z₂ fun i => (zs i).2)))
            * ((cascadeRec k (Fin.tail ms) (Fin.tail μs)
                  (fun zs => G₁ (Fin.cons z₁ zs)) ^ ms 0
                * cascadeConst k (ms 0) (Fin.tail ms))
              * (cascadeRec k (Fin.tail ms) (Fin.tail μs)
                  (fun zs => G₂ (Fin.cons z₂ zs)) ^ ms 0
                * cascadeConst k (ms 0) (Fin.tail ms))) := by
      filter_upwards [hfinTail₁] with z₁ hz₁
      filter_upwards [hfinTail₂] with z₂ hz₂
      have h := lintegral_cascadePairSum_mul_rpow k (Fin.tail ms) (Fin.tail μs)
        (U := fun zs => U (Fin.cons (z₁, z₂) zs))
        (G₁ := fun zs => G₁ (Fin.cons z₁ zs)) (G₂ := fun zs => G₂ (Fin.cons z₂ zs))
        (hU.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
        (hG₁.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
        (hG₂.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
        (fun zs => hG₁pos _) (fun zs => hG₂pos _) hz₁ hz₂ hm hsm' (fun i => hlt i.succ)
      rw [hQ₁' z₁, hQ₂' z₂] at h
      exact h
    rw [lintegral_congr_ae (by
      filter_upwards [hfib] with z₁ hz₁
      exact lintegral_congr_ae hz₁)]
    -- the level-`(k+1)` tilted average
    have hWmul₁ : ∀ z : T, cascadeRec k (Fin.tail ms) (Fin.tail μs)
          (fun zs => G₁ (Fin.cons z zs)) ^ ms 0
        = cascadeW k ms μs G₁ z * R₁ ^ ms 0 := by
      intro z
      rw [cascadeW, ENNReal.div_rpow_of_nonneg _ _ hm.le,
        ENNReal.div_mul_cancel hR₁m0 hR₁mtop]
    have hWmul₂ : ∀ z : T, cascadeRec k (Fin.tail ms) (Fin.tail μs)
          (fun zs => G₂ (Fin.cons z zs)) ^ ms 0
        = cascadeW k ms μs G₂ z * R₂ ^ ms 0 := by
      intro z
      rw [cascadeW, ENNReal.div_rpow_of_nonneg _ _ hm.le,
        ENNReal.div_mul_cancel hR₂m0 hR₂mtop]
    have hcons : ∀ z₁ z₂ : T,
        (fun zs : Fin k → T × T => U (Fin.cons (z₁, z₂) zs)
            / (G₁ (Fin.cons z₁ fun i => (zs i).1) * G₂ (Fin.cons z₂ fun i => (zs i).2)))
          = fun zs : Fin k → T × T =>
            (fun zs : Fin (k + 1) → T × T => U zs
              / (G₁ (fun i => (zs i).1) * G₂ (fun i => (zs i).2))) (Fin.cons (z₁, z₂) zs) := by
      intro z₁ z₂
      funext zs
      simp only
      rw [fin_cons_fst (z₁, z₂) zs, fin_cons_snd (z₁, z₂) zs]
    have hUcheck : Measurable fun zs : Fin (k + 1) → T × T =>
        U zs / (G₁ (fun i => (zs i).1) * G₂ (fun i => (zs i).2)) :=
      hU.div ((hG₁.comp measurable_pairFst).mul (hG₂.comp measurable_pairSnd))
    have hTm : Measurable fun q : T × T => cascadeTiltProd k (Fin.tail ms) (Fin.tail μs)
        (fun zs => G₁ (Fin.cons q.1 zs)) (fun zs => G₂ (Fin.cons q.2 zs))
        (fun zs => (fun zs : Fin (k + 1) → T × T => U zs
          / (G₁ (fun i => (zs i).1) * G₂ (fun i => (zs i).2))) (Fin.cons q zs)) := by
      refine measurable_cascadeTiltProd_prod k (Fin.tail ms) (Fin.tail μs) ?_ ?_
        (hUcheck.comp measurable_fin_cons)
      · exact hG₁.comp (measurable_fin_cons.comp
          ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
      · exact hG₂.comp (measurable_fin_cons.comp
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
    have hM2 : ∀ z₁ : T, Measurable fun z₂ : T => cascadeW k ms μs G₁ z₁
        * cascadeW k ms μs G₂ z₂
        * cascadeTiltProd k (Fin.tail ms) (Fin.tail μs)
            (fun zs => G₁ (Fin.cons z₁ zs)) (fun zs => G₂ (Fin.cons z₂ zs))
            (fun zs => (fun zs : Fin (k + 1) → T × T => U zs
              / (G₁ (fun i => (zs i).1) * G₂ (fun i => (zs i).2)))
              (Fin.cons (z₁, z₂) zs)) := by
      intro z₁
      exact (measurable_const.mul (measurable_cascadeW k ms μs hG₂)).mul
        (hTm.comp (measurable_const.prodMk measurable_id))
    have hM1 : Measurable fun z₁ : T => ∫⁻ z₂, cascadeW k ms μs G₁ z₁
        * cascadeW k ms μs G₂ z₂
        * cascadeTiltProd k (Fin.tail ms) (Fin.tail μs)
            (fun zs => G₁ (Fin.cons z₁ zs)) (fun zs => G₂ (Fin.cons z₂ zs))
            (fun zs => (fun zs : Fin (k + 1) → T × T => U zs
              / (G₁ (fun i => (zs i).1) * G₂ (fun i => (zs i).2)))
              (Fin.cons (z₁, z₂) zs)) ∂μs 0 := by
      refine Measurable.lintegral_prod_right' (ν := μs 0)
        (f := fun q : T × T => cascadeW k ms μs G₁ q.1 * cascadeW k ms μs G₂ q.2
          * cascadeTiltProd k (Fin.tail ms) (Fin.tail μs)
              (fun zs => G₁ (Fin.cons q.1 zs)) (fun zs => G₂ (Fin.cons q.2 zs))
              (fun zs => (fun zs : Fin (k + 1) → T × T => U zs
                / (G₁ (fun i => (zs i).1) * G₂ (fun i => (zs i).2)))
                (Fin.cons q zs))) ?_
      exact (((measurable_cascadeW k ms μs hG₁).comp measurable_fst).mul
        ((measurable_cascadeW k ms μs hG₂).comp measurable_snd)).mul hTm
    rw [cascadeTiltProd_succ, hκ₁, hκ₂, ← lintegral_mul_const _ hM1]
    refine lintegral_congr fun z₁ => ?_
    rw [← lintegral_mul_const _ (hM2 z₁)]
    refine lintegral_congr fun z₂ => ?_
    rw [hWmul₁ z₁, hWmul₂ z₂, hcons z₁ z₂]
    ring

omit [Nonempty T] in
/-- **The two-copy tilted average is an average against a probability measure**:
`𝔼(W₁¹ W₁² ⋯ W_k¹ W_k²) = 1`, under Talagrand's (14.4). -/
theorem cascadeTiltProd_one (k : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {G₁ G₂ : (Fin k → T) → ℝ≥0∞} (hG₁ : Measurable G₁)
    (hG₂ : Measurable G₂) (hG₁pos : ∀ zs, 0 < G₁ zs) (hG₂pos : ∀ zs, 0 < G₂ zs)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    (hfin₁ : ∫⁻ zs, G₁ zs ∂Measure.pi μs ≠ ∞) (hfin₂ : ∫⁻ zs, G₂ zs ∂Measure.pi μs ≠ ∞) :
    cascadeTiltProd k ms μs G₁ G₂ (fun _ => 1) = 1 := by
  have h : (fun _ : Fin k → T × T => (1 : ℝ≥0∞))
      = fun zs : Fin k → T × T => (fun _ : Fin k → T => (1 : ℝ≥0∞)) (fun i => (zs i).1)
        * (fun _ : Fin k → T => (1 : ℝ≥0∞)) (fun i => (zs i).2) := by
    funext zs
    simp
  rw [h, cascadeTiltProd_prod k ms μs hG₁ hG₂ measurable_const measurable_const,
    cascadeTilt_one k ms μs hG₁ hG₁pos hpos hle hfin₁,
    cascadeTilt_one k ms μs hG₂ hG₂pos hpos hle hfin₂, one_mul]

omit [Nonempty T] in
/-- **The coupled tilted average is an average against a probability measure**:
`𝔼(W₁ ⋯ W_r W_{r+1}¹ W_{r+1}² ⋯ W_k¹ W_k²) = 1`, under Talagrand's (14.4). Equivalently, by
Corollary 14.3.7, the coupled cascade's tilted average is normalized. -/
theorem cascadeTiltPair_one (k r : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {G : (Fin k → T) → ℝ≥0∞} (hG : Measurable G)
    (hGpos : ∀ zs, 0 < G zs) (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    (hfin : ∫⁻ zs, G zs ∂Measure.pi μs ≠ ∞) :
    cascadeTiltPair k r ms μs G (fun _ => 1) = 1 := by
  have h : (fun _ : Fin k → T × T => (1 : ℝ≥0∞))
      = fun zs : Fin k → T × T => (fun _ : Fin k → T => (1 : ℝ≥0∞)) (fun i => (zs i).1)
        * (fun _ : Fin k → T => (1 : ℝ≥0∞)) (fun i => (zs i).2) := by
    funext zs
    simp
  rw [h, cascadeTiltPair_prod k r ms μs hG measurable_const,
    cascadeTiltSq_one k r ms μs hG hGpos hpos hle hfin]

/-! ### Talagrand's Theorem 14.3.5 -/

/-- Shifting the summation index of a sum over `Finset.Ico`. -/
private lemma sum_Ico_shift (n r : ℕ) (F : ℕ → ℝ≥0∞) :
    ∑ j ∈ Finset.Ico r (n + 1), F (j + 1) = ∑ j ∈ Finset.Ico (r + 1) (n + 2), F j := by
  rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range,
    show n + 2 - (r + 1) = n + 1 - r by omega]
  exact Finset.sum_congr rfl fun i _ => by rw [show r + i + 1 = r + 1 + i by omega]

/-- The algebraic recombination of the two terms produced by the one-level pair identity. -/
private lemma combine_off_diag_pair (Koff Ksq T S κ Ma c d : ℝ≥0∞)
    (h1 : Koff * κ ^ 2 = c * Ma) (h2 : Ksq * κ = d * Ma) :
    Koff * (T * (κ * κ)) + Ksq * (S * κ) = (c * T + S * d) * Ma := by
  calc Koff * (T * (κ * κ)) + Ksq * (S * κ)
      = T * (Koff * κ ^ 2) + S * (Ksq * κ) := by ring
    _ = T * (c * Ma) + S * (d * Ma) := by rw [h1, h2]
    _ = (c * T + S * d) * Ma := by ring


set_option maxHeartbeats 4000000 in
-- the induction unfolds nested cascade integrals with large measurability terms
/-- **Talagrand's Theorem 14.3.5 with a free exponent**: for a general function `Ũ` of the *pair*
of mark sequences,

`𝔼 Q_r(Ũ) S_G^{a-2}
  = (∑_{r ≤ j ≤ k} (m_{j+1} - m_j)/(1-a) · 𝔼(W₁ ⋯ W_j W_{j+1}¹ W_{j+1}² ⋯ W_k¹ W_k² Ǔ)) · 𝔼 S_G^a`,

`m_0` being replaced by `a` and `Ǔ = Ũ / (G ⊗ G)`. Talagrand proves the corresponding identity
by polarization from the case `Ũ = U ⊗ U'` and then approximating a general `Ũ` by sums of such
products; here the induction is carried out directly for a general `Ũ`, so no approximation is
needed. At `Ũ = A ⊗ A` it is `lintegral_cascadeSq_mul_rpow_num`, by `cascadeSqPair_prod` and
`cascadeTiltPair_prod` (Talagrand's (14.42)). -/
theorem lintegral_cascadeSqPair_mul_rpow (k : ℕ) :
    ∀ (ms : Fin k → ℝ) (μs : Fin k → Measure T) [∀ i, IsProbabilityMeasure (μs i)]
      {U : (Fin k → T × T) → ℝ≥0∞} {G : (Fin k → T) → ℝ≥0∞}, Measurable U → Measurable G →
      (∀ zs, 0 < G zs) → ∫⁻ zs, G zs ∂Measure.pi μs ≠ ∞ → StrictMono ms → (∀ i, ms i < 1) →
      ∀ {a : ℝ}, 0 ≤ a → a < 1 → (∀ i, a < ms i) → ∀ r : ℕ,
      ∫⁻ ω, cascadeSqPair k r U ω * cascadeSum k G ω ^ (a - 2) ∂cascadeLaw k ms μs
        = (∑ j ∈ Finset.Ico r (k + 1),
            ENNReal.ofReal ((mExt' ms a (j + 1) - mExt' ms a j) / (1 - a))
              * cascadeTiltPair k j ms μs G
                  (fun zs => U zs / (G (fun i => (zs i).1) * G (fun i => (zs i).2))))
          * ∫⁻ ω, cascadeSum k G ω ^ a ∂cascadeLaw k ms μs := by
  induction k with
  | zero =>
    intro ms μs hμs U G hU hG hGpos hfin _ _ a ha0 ha1 _ r
    have (i : Fin 0) : IsProbabilityMeasure (μs i) := hμs i
    have hG0 : G Fin.elim0 ≠ 0 := (hGpos _).ne'
    have hGtop : G Fin.elim0 ≠ ∞ := by
      rw [Measure.pi_of_empty, lintegral_dirac' _ hG] at hfin
      exact fun h => hfin (by rw [← h]; exact congrArg G (Subsingleton.elim _ _))
    rcases r with _ | r
    · rw [← Finset.range_eq_Ico, Finset.sum_range_one]
      have hc : ENNReal.ofReal ((mExt' ms a (0 + 1) - mExt' ms a 0) / (1 - a)) = 1 := by
        rw [mExt'_zero, mExt'_succ_eq, mExt_of_zero_lt (r := 0 + 1) (by omega),
          div_self (show (1 : ℝ) - a ≠ 0 by linarith), ENNReal.ofReal_one]
      simp only [cascadeLaw_zero, lintegral_dirac, hc, one_mul, cascadeSqPair_zero,
        cascadePairSum_zero, cascadeSum_zero, cascadeTiltPair_zero, cascadeTiltProd_zero]
      have he : G (fun i => ((Fin.elim0 : Fin 0 → T × T) i).1) = G Fin.elim0 :=
        congrArg G (Subsingleton.elim _ _)
      have he' : G (fun i => ((Fin.elim0 : Fin 0 → T × T) i).2) = G Fin.elim0 :=
        congrArg G (Subsingleton.elim _ _)
      rw [he, he', ENNReal.rpow_sub _ _ hG0 hGtop, div_eq_mul_inv, div_eq_mul_inv,
        show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast, pow_two,
        ENNReal.mul_inv (Or.inl hG0) (Or.inl hGtop)]
      ring
    · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty, zero_mul]
      simp only [cascadeLaw_zero, lintegral_dirac, cascadeSqPair_zero_succ, zero_mul]
  | succ k ih =>
    intro ms μs hμs U G hU hG hGpos hfin hsm hlt a ha0 ha1 ham r
    have (i : Fin (k + 1)) : IsProbabilityMeasure (μs i) := hμs i
    have := isProbabilityMeasure_cascadeLaw (k + 1) ms μs
    have hm : 0 < ms 0 := lt_of_le_of_lt ha0 (ham 0)
    have ham0 : a < ms 0 := ham 0
    have hm1 : ms 0 < 1 := hlt 0
    have h1m : (1 : ℝ) - ms 0 ≠ 0 := by linarith
    have h1a : (1 : ℝ) - a ≠ 0 := by linarith
    have hposAll : ∀ i, 0 < ms i := fun i => lt_of_le_of_lt ha0 (ham i)
    have hsm' : StrictMono (Fin.cons (ms 0) (Fin.tail ms) : Fin (k + 1) → ℝ) := by
      rw [Fin.cons_self_tail]
      exact hsm
    have hposTail : ∀ i, 0 < Fin.tail ms i := fun i => hposAll i.succ
    have hfinTail : ∀ᵐ z ∂μs 0,
        ∫⁻ zs, G (Fin.cons z zs) ∂Measure.pi (Fin.tail μs) ≠ ∞ :=
      ae_lintegral_pi_cons_ne_top k μs hG hfin
    have hconsG : Measurable (uncurry fun z : T => fun zs : Fin k → T => G (Fin.cons z zs)) :=
      hG.comp measurable_fin_cons
    have hconsU : Measurable (uncurry fun z : T => fun zs : Fin k → T × T =>
        U (Fin.cons (z, z) zs)) :=
      hU.comp (measurable_fin_cons.comp
        ((measurable_fst.prodMk measurable_fst).prodMk measurable_snd))
    have hUcheck : Measurable fun zs : Fin (k + 1) → T × T =>
        U zs / (G (fun i => (zs i).1) * G (fun i => (zs i).2)) :=
      hU.div ((hG.comp measurable_pairFst).mul (hG.comp measurable_pairSnd))
    set η := (μs 0).prod (cascadeLaw k (Fin.tail ms) (Fin.tail μs)) with hη
    set vG : T × CascadeSpace T k → ℝ≥0∞ :=
      fun p => cascadeSum k (fun zs => G (Fin.cons p.1 zs)) p.2 with hvG_def
    have hvG : Measurable vG :=
      measurable_cascadeSum_prod k (α := T) (G := fun z zs => G (Fin.cons z zs)) hconsG
    have hlaw := hasLaw_superCounting_cascadeLaw k ms μs
    have hsumG : ∀ ω, cascadeSum (k + 1) G ω = pdSum vG (superCounting ω) := fun ω => rfl
    have hVpos : ∀ᵐ p ∂η, 0 < vG p := by
      rw [hη, Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const hvG)]
      refine Filter.Eventually.of_forall fun z => ?_
      exact ae_cascadeSum_pos k (Fin.tail ms) (Fin.tail μs)
        (hG.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
        (fun zs => hGpos _) hposTail
    have hRm : Measurable fun z => cascadeRec k (Fin.tail ms) (Fin.tail μs)
        (fun zs => G (Fin.cons z zs)) := measurable_cascadeRec_cons k _ _ hG
    have hQ : ∀ z, ∫⁻ ω', vG (z, ω') ^ ms 0 ∂cascadeLaw k (Fin.tail ms) (Fin.tail μs)
        = cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs)) ^ ms 0
          * cascadeConst k (ms 0) (Fin.tail ms) := fun z =>
      lintegral_cascadeSum_rpow k (Fin.tail ms) (Fin.tail μs)
        (hG.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
        hm hsm' (fun i => hlt i.succ)
    have hQ' : ∀ z, ∫⁻ ω, cascadeSum k (fun zs => G (Fin.cons z zs)) ω ^ ms 0
        ∂cascadeLaw k (Fin.tail ms) (Fin.tail μs)
        = cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs)) ^ ms 0
          * cascadeConst k (ms 0) (Fin.tail ms) := hQ
    obtain ⟨hCk0, hCktop⟩ := cascadeConst_pos_ne_top k hm hsm' (fun i => hlt i.succ)
    set R := cascadeRec (k + 1) ms μs G with hRdef
    have hR0 : R ≠ 0 := (cascadeRec_pos (k + 1) ms μs hG hGpos hposAll).ne'
    have hRtop : R ≠ ∞ := cascadeRec_ne_top (k + 1) ms μs hG hposAll (fun i => (hlt i).le) hfin
    have hRm0 : R ^ ms 0 ≠ 0 := by
      simpa using (ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.2 hR0) hm.le).ne'
    have hRmtop : R ^ ms 0 ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hm.le hRtop
    have hκ : ∫⁻ p, vG p ^ ms 0 ∂η = cascadeConst k (ms 0) (Fin.tail ms) * R ^ ms 0 := by
      rw [hη, lintegral_prod (fun p : T × CascadeSpace T k => vG p ^ ms 0)
        (hvG.pow_const _).aemeasurable]
      simp_rw [hQ]
      rw [lintegral_mul_const _ (hRm.pow_const _), hRdef, cascadeRec_succ, ← ENNReal.rpow_mul,
        one_div_mul_cancel hm.ne', ENNReal.rpow_one, mul_comm]
    have hκtop : ∫⁻ p, vG p ^ ms 0 ∂η ≠ ∞ := by
      rw [hκ]
      exact ENNReal.mul_ne_top hCktop hRmtop
    have htransG : ∫⁻ ω, cascadeSum (k + 1) G ω ^ a ∂cascadeLaw (k + 1) ms μs
        = ∫⁻ N, pdSum vG N ^ a ∂pdProcess (ms 0) η := by
      simp_rw [hsumG]
      exact hlaw.lintegral_comp ((measurable_pdSum hvG).pow_const _).aemeasurable
    have hoff := ofReal_pdOffConst_mul_lintegral hm hm1 η hvG hVpos hκtop ha0 ham0
    have hsqc := ofReal_pdSqConst_mul_lintegral hm hm1 η hvG hVpos hκtop ha0 ham0
    have hWmul : ∀ z, cascadeRec k (Fin.tail ms) (Fin.tail μs)
          (fun zs => G (Fin.cons z zs)) ^ ms 0
        = cascadeW k ms μs G z * R ^ ms 0 := by
      intro z
      rw [cascadeW, ENNReal.div_rpow_of_nonneg _ _ hm.le, ENNReal.div_mul_cancel hRm0 hRmtop]
    have hTm : ∀ j : ℕ, Measurable fun z => cascadeTiltPair k j (Fin.tail ms) (Fin.tail μs)
        (fun zs => G (Fin.cons z zs))
        (fun zs => (fun zs : Fin (k + 1) → T × T =>
          U zs / (G (fun i => (zs i).1) * G (fun i => (zs i).2))) (Fin.cons (z, z) zs)) :=
      fun j => measurable_cascadeTiltPair_prod k j (Fin.tail ms) (Fin.tail μs)
        (Gs := fun z zs => G (Fin.cons z zs))
        (Us := fun z zs => (fun zs : Fin (k + 1) → T × T =>
          U zs / (G (fun i => (zs i).1) * G (fun i => (zs i).2))) (Fin.cons (z, z) zs))
        hconsG (hUcheck.comp (measurable_fin_cons.comp
          ((measurable_fst.prodMk measurable_fst).prodMk measurable_snd)))
    have hWT : ∀ j : ℕ, Measurable fun z : T => cascadeW k ms μs G z
        * cascadeTiltPair k j (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs))
            (fun zs => (fun zs : Fin (k + 1) → T × T =>
              U zs / (G (fun i => (zs i).1) * G (fun i => (zs i).2))) (Fin.cons (z, z) zs)) :=
      fun j => (measurable_cascadeW k ms μs hG).mul (hTm j)
    have hcoef : ∀ j : ℕ, ENNReal.ofReal ((1 - ms 0) / (1 - a))
          * ENNReal.ofReal ((mExt' (Fin.tail ms) (ms 0) (j + 1)
              - mExt' (Fin.tail ms) (ms 0) j) / (1 - ms 0))
        = ENNReal.ofReal ((mExt' ms a (j + 1 + 1) - mExt' ms a (j + 1)) / (1 - a)) := by
      intro j
      rw [← ENNReal.ofReal_mul (div_nonneg (by linarith) (by linarith)),
        mExt'_succ ms a (j + 1), mExt'_succ ms a j]
      congr 1
      field_simp
    have hconsPair : ∀ z : T,
        (fun zs : Fin k → T × T => U (Fin.cons (z, z) zs)
            / (G (Fin.cons z fun i => (zs i).1) * G (Fin.cons z fun i => (zs i).2)))
          = fun zs : Fin k → T × T => (fun zs : Fin (k + 1) → T × T =>
              U zs / (G (fun i => (zs i).1) * G (fun i => (zs i).2))) (Fin.cons (z, z) zs) := by
      intro z
      funext zs
      simp only
      rw [fin_cons_fst (z, z) zs, fin_cons_snd (z, z) zs]
    -- the diagonal term, by the induction hypothesis on the sub-cascades
    have hdiag : ∀ r' : ℕ,
        ∫⁻ p, cascadeSqPair k r' (fun zs => U (Fin.cons (p.1, p.1) zs)) p.2
            * vG p ^ (ms 0 - 2) ∂η
          = (∑ j ∈ Finset.Ico r' (k + 1),
              ENNReal.ofReal ((mExt' (Fin.tail ms) (ms 0) (j + 1)
                  - mExt' (Fin.tail ms) (ms 0) j) / (1 - ms 0))
                * cascadeTiltPair (k + 1) (j + 1) ms μs G
                    (fun zs => U zs / (G (fun i => (zs i).1) * G (fun i => (zs i).2))))
            * ∫⁻ p, vG p ^ ms 0 ∂η := by
      intro r'
      have hB : Measurable fun p : T × CascadeSpace T k =>
          cascadeSqPair k r' (fun zs => U (Fin.cons (p.1, p.1) zs)) p.2 :=
        measurable_cascadeSqPair_prod k r' (α := T)
          (U := fun z zs => U (Fin.cons (z, z) zs)) hconsU
      rw [hη, lintegral_prod (fun p : T × CascadeSpace T k =>
        cascadeSqPair k r' (fun zs => U (Fin.cons (p.1, p.1) zs)) p.2 * vG p ^ (ms 0 - 2))
        (hB.mul (hvG.pow_const _)).aemeasurable]
      have hfib : ∀ᵐ z ∂μs 0, ∫⁻ ω', cascadeSqPair k r' (fun zs => U (Fin.cons (z, z) zs)) ω'
            * vG (z, ω') ^ (ms 0 - 2) ∂cascadeLaw k (Fin.tail ms) (Fin.tail μs)
          = (∑ j ∈ Finset.Ico r' (k + 1),
              ENNReal.ofReal ((mExt' (Fin.tail ms) (ms 0) (j + 1)
                  - mExt' (Fin.tail ms) (ms 0) j) / (1 - ms 0))
                * cascadeTiltPair k j (Fin.tail ms) (Fin.tail μs)
                    (fun zs => G (Fin.cons z zs))
                    (fun zs => U (Fin.cons (z, z) zs)
                      / (G (Fin.cons z fun i => (zs i).1)
                        * G (Fin.cons z fun i => (zs i).2))))
            * (cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs)) ^ ms 0
              * cascadeConst k (ms 0) (Fin.tail ms)) := by
        filter_upwards [hfinTail] with z hz
        have h := ih (Fin.tail ms) (Fin.tail μs) (U := fun zs => U (Fin.cons (z, z) zs))
          (G := fun zs => G (Fin.cons z zs))
          (hU.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
          (hG.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
          (fun zs => hGpos _) hz (strictMono_of_strictMono_cons hsm') (fun i => hlt i.succ)
          hm.le hm1 (fun i => hsm (Fin.succ_pos i)) r'
        rw [hQ' z] at h
        exact h
      rw [lintegral_congr_ae hfib]
      simp_rw [hWmul, hconsPair]
      have hpt : ∀ z : T, (∑ j ∈ Finset.Ico r' (k + 1),
              ENNReal.ofReal ((mExt' (Fin.tail ms) (ms 0) (j + 1)
                  - mExt' (Fin.tail ms) (ms 0) j) / (1 - ms 0))
                * cascadeTiltPair k j (Fin.tail ms) (Fin.tail μs)
                    (fun zs => G (Fin.cons z zs))
                    (fun zs => (fun zs : Fin (k + 1) → T × T =>
                      U zs / (G (fun i => (zs i).1) * G (fun i => (zs i).2)))
                      (Fin.cons (z, z) zs)))
            * (cascadeW k ms μs G z * R ^ ms 0 * cascadeConst k (ms 0) (Fin.tail ms))
          = ∑ j ∈ Finset.Ico r' (k + 1), (R ^ ms 0 * cascadeConst k (ms 0) (Fin.tail ms)
              * ENNReal.ofReal ((mExt' (Fin.tail ms) (ms 0) (j + 1)
                  - mExt' (Fin.tail ms) (ms 0) j) / (1 - ms 0)))
              * (cascadeW k ms μs G z * cascadeTiltPair k j (Fin.tail ms) (Fin.tail μs)
                  (fun zs => G (Fin.cons z zs))
                  (fun zs => (fun zs : Fin (k + 1) → T × T =>
                    U zs / (G (fun i => (zs i).1) * G (fun i => (zs i).2)))
                    (Fin.cons (z, z) zs))) := by
        intro z
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
      simp_rw [hpt]
      rw [lintegral_finsetSum (μ := μs 0) (Finset.Ico r' (k + 1))
        (f := fun (j : ℕ) (z : T) => (R ^ ms 0 * cascadeConst k (ms 0) (Fin.tail ms)
            * ENNReal.ofReal ((mExt' (Fin.tail ms) (ms 0) (j + 1)
                - mExt' (Fin.tail ms) (ms 0) j) / (1 - ms 0)))
            * (cascadeW k ms μs G z * cascadeTiltPair k j (Fin.tail ms) (Fin.tail μs)
                (fun zs => G (Fin.cons z zs))
                (fun zs => (fun zs : Fin (k + 1) → T × T =>
                  U zs / (G (fun i => (zs i).1) * G (fun i => (zs i).2)))
                  (Fin.cons (z, z) zs))))
        (fun j _ => measurable_const.mul (hWT j))]
      have hterm : ∀ j : ℕ, ∫⁻ z, (R ^ ms 0 * cascadeConst k (ms 0) (Fin.tail ms)
              * ENNReal.ofReal ((mExt' (Fin.tail ms) (ms 0) (j + 1)
                  - mExt' (Fin.tail ms) (ms 0) j) / (1 - ms 0)))
              * (cascadeW k ms μs G z * cascadeTiltPair k j (Fin.tail ms) (Fin.tail μs)
                  (fun zs => G (Fin.cons z zs))
                  (fun zs => (fun zs : Fin (k + 1) → T × T =>
                    U zs / (G (fun i => (zs i).1) * G (fun i => (zs i).2)))
                    (Fin.cons (z, z) zs))) ∂μs 0
          = (R ^ ms 0 * cascadeConst k (ms 0) (Fin.tail ms)
              * ENNReal.ofReal ((mExt' (Fin.tail ms) (ms 0) (j + 1)
                  - mExt' (Fin.tail ms) (ms 0) j) / (1 - ms 0)))
            * cascadeTiltPair (k + 1) (j + 1) ms μs G
                (fun zs => U zs / (G (fun i => (zs i).1) * G (fun i => (zs i).2))) := by
        intro j
        rw [lintegral_const_mul _ (hWT j), cascadeTiltPair_succ]
      simp_rw [hterm]
      rw [hκ, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    rcases r with _ | r
    · -- `Q₀`: the top level contributes both an off-diagonal and a diagonal term
      set vB : (T × CascadeSpace T k) × (T × CascadeSpace T k) → ℝ≥0∞ :=
        fun r => cascadePairSum k (fun zs => U (Fin.cons (r.1.1, r.2.1) zs)) r.1.2 r.2.2
        with hvB_def
      have hvB : Measurable vB := by
        have h := measurable_cascadePairSum_prod k (α := T × T)
          (U := fun q zs => U (Fin.cons q zs)) (hU.comp measurable_fin_cons)
        have hmap : Measurable fun r : (T × CascadeSpace T k) × (T × CascadeSpace T k) =>
            ((r.1.1, r.2.1), (r.1.2, r.2.2)) :=
          ((measurable_fst.comp measurable_fst).prodMk
            (measurable_fst.comp measurable_snd)).prodMk
            ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd))
        have h2 := h.comp hmap
        simp only [Function.comp_def] at h2
        exact h2
      have hlawEq : cascadeLaw (k + 1) ms μs = pdSampleLaw (ms 0) η := rfl
      have hpt : ∀ ω : CascadeSpace T (k + 1),
          cascadeSqPair (k + 1) 0 U ω * cascadeSum (k + 1) G ω ^ (a - 2)
            = (∫⁻ p, ∫⁻ q, ENNReal.ofReal p.1 * ENNReal.ofReal q.1 * vB (p.2, q.2)
                ∂superCounting ω ∂superCounting ω)
              * pdSum vG (superCounting ω) ^ (a - 2) := by
        intro ω
        rw [cascadeSqPair_zero, cascadePairSum_succ]
        rfl
      have htrans : ∫⁻ ω, cascadeSqPair (k + 1) 0 U ω * cascadeSum (k + 1) G ω ^ (a - 2)
            ∂cascadeLaw (k + 1) ms μs
          = ∫⁻ ω, (∫⁻ p, ∫⁻ q, ENNReal.ofReal p.1 * ENNReal.ofReal q.1 * vB (p.2, q.2)
                ∂superCounting ω ∂superCounting ω) * pdSum vG (superCounting ω) ^ (a - 2)
              ∂pdSampleLaw (ms 0) η := by
        conv_lhs => rw [hlawEq]
        exact lintegral_congr hpt
      have hoffJ : ∫⁻ g, vG g ^ (ms 0 - 1) * ∫⁻ g', vB (g, g') * vG g' ^ (ms 0 - 1) ∂η ∂η
          = cascadeTiltProd (k + 1) ms μs G G
              (fun zs => U zs / (G (fun i => (zs i).1) * G (fun i => (zs i).2)))
            * ((∫⁻ p, vG p ^ ms 0 ∂η) * ∫⁻ p, vG p ^ ms 0 ∂η) :=
        lintegral_prod_cascadePairSum_mul_rpow k ms μs hU hG hG hGpos hGpos hfin hfin hsm
          hposAll hlt
      have hoffshape : ∫⁻ g, ∫⁻ g', vB (g, g') * vG g ^ (ms 0 - 1) * vG g' ^ (ms 0 - 1) ∂η ∂η
          = ∫⁻ g, vG g ^ (ms 0 - 1) * ∫⁻ g', vB (g, g') * vG g' ^ (ms 0 - 1) ∂η ∂η := by
        refine lintegral_congr fun g => ?_
        have hin : Measurable fun g' : T × CascadeSpace T k =>
            vB (g, g') * vG g' ^ (ms 0 - 1) :=
          (hvB.comp (measurable_const.prodMk measurable_id)).mul (hvG.pow_const _)
        rw [← lintegral_const_mul _ hin]
        exact lintegral_congr fun g' => by ring
      have hdiagshape : ∫⁻ g, vB (g, g) * vG g ^ (ms 0 - 2) ∂η
          = ∫⁻ p, cascadeSqPair k 0 (fun zs => U (Fin.cons (p.1, p.1) zs)) p.2
              * vG p ^ (ms 0 - 2) ∂η :=
        lintegral_congr fun g => by rw [cascadeSqPair_zero]
      rw [htrans, lintegral_pdSumPair_mul_rpow_pdSum hm hm1 η hvB hvG hVpos hκtop ham0,
        hoffshape, hoffJ, hdiagshape, hdiag 0, htransG,
        combine_off_diag_pair _ _ _ _ _ _ _ _ hoff hsqc]
      congr 1
      rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < k + 2), ← sum_Ico_shift k 0,
        Finset.sum_mul]
      have hbot : ENNReal.ofReal ((mExt' ms a (0 + 1) - mExt' ms a 0) / (1 - a))
            * cascadeTiltPair (k + 1) 0 ms μs G
              (fun zs => U zs / (G (fun i => (zs i).1) * G (fun i => (zs i).2)))
          = ENNReal.ofReal ((ms 0 - a) / (1 - a))
            * cascadeTiltProd (k + 1) ms μs G G
              (fun zs => U zs / (G (fun i => (zs i).1) * G (fun i => (zs i).2))) := by
        rw [cascadeTiltPair_zero, mExt'_zero, zero_add, mExt'_succ_eq, mExt_one]
      rw [hbot]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by
        rw [mul_comm _ (ENNReal.ofReal ((1 - ms 0) / (1 - a))), ← mul_assoc, hcoef j]
    · -- `Q_{r+1}`: only the diagonal survives
      have hB : Measurable fun p : T × CascadeSpace T k =>
          cascadeSqPair k r (fun zs => U (Fin.cons (p.1, p.1) zs)) p.2 :=
        measurable_cascadeSqPair_prod k r (α := T)
          (U := fun z zs => U (Fin.cons (z, z) zs)) hconsU
      have htrans : ∫⁻ ω, cascadeSqPair (k + 1) (r + 1) U ω
            * cascadeSum (k + 1) G ω ^ (a - 2) ∂cascadeLaw (k + 1) ms μs
          = ∫⁻ N, (∫⁻ p, ENNReal.ofReal p.1 * ENNReal.ofReal p.1
              * cascadeSqPair k r (fun zs => U (Fin.cons (p.2.1, p.2.1) zs)) p.2.2 ∂N)
              * pdSum vG N ^ (a - 2) ∂pdProcess (ms 0) η := by
        have hpt : ∀ ω : CascadeSpace T (k + 1),
            cascadeSqPair (k + 1) (r + 1) U ω * cascadeSum (k + 1) G ω ^ (a - 2)
              = (∫⁻ p, ENNReal.ofReal p.1 * ENNReal.ofReal p.1
                  * cascadeSqPair k r (fun zs => U (Fin.cons (p.2.1, p.2.1) zs)) p.2.2
                  ∂superCounting ω) * pdSum vG (superCounting ω) ^ (a - 2) := fun ω => rfl
        simp_rw [hpt]
        have hUW : Measurable fun p : ℝ × (T × CascadeSpace T k) =>
            ENNReal.ofReal p.1 * ENNReal.ofReal p.1
              * cascadeSqPair k r (fun zs => U (Fin.cons (p.2.1, p.2.1) zs)) p.2.2 :=
          ((ENNReal.measurable_ofReal.comp measurable_fst).mul
            (ENNReal.measurable_ofReal.comp measurable_fst)).mul (hB.comp measurable_snd)
        exact hlaw.lintegral_comp ((Measure.measurable_lintegral hUW).mul
          ((measurable_pdSum hvG).pow_const _)).aemeasurable
      rw [htrans, htransG,
        lintegral_pdSumSq_mul_rpow_pdSum hm hm1 η hB hvG hVpos hκtop ham0, hdiag r,
        ← mul_assoc, mul_comm (ENNReal.ofReal (pdSqConst (ms 0) a (stableConst (ms 0))
          (∫⁻ p, vG p ^ ms 0 ∂η).toReal)), mul_assoc, hsqc, ← mul_assoc, ← sum_Ico_shift k r]
      congr 1
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_comm _ (ENNReal.ofReal ((1 - ms 0) / (1 - a))), ← mul_assoc, hcoef j]

/-- **Talagrand's (14.47) in cumulative form**: for the cascade Gibbs average and `0 ≤ r ≤ k + 1`,

`𝔼 ⟨1_{α|r = γ|r} Ũ(α, γ)⟩
  = ∑_{r < p ≤ k+1} (m_p - m_{p-1}) 𝔼(W₁ ⋯ W_{p-1} W_p¹ W_p² ⋯ W_k¹ W_k² Ǔ)`,

with the conventions `m_0 = 0`, `m_{k+1} = 1`. Here `Ũ` is the *unweighted* numerator `U`, so
that Talagrand's Gibbs average of a function `V(α, γ)` is the case `U = (G ⊗ G) · V`, and then
`Ǔ = U / (G ⊗ G)` is his `V`; since `U` is an arbitrary measurable function the two readings are
equivalent. At `U = A ⊗ A` it is `lintegral_cascadeSq_num_mul_inv_sq`, by `cascadeSqPair_prod`
and `cascadeTiltPair_prod`. -/
theorem lintegral_cascadeSqPair_mul_inv_sq (k : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {U : (Fin k → T × T) → ℝ≥0∞} {G : (Fin k → T) → ℝ≥0∞}
    (hU : Measurable U) (hG : Measurable G) (hGpos : ∀ zs, 0 < G zs)
    (hfin : ∫⁻ zs, G zs ∂Measure.pi μs ≠ ∞) (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i)
    (hlt : ∀ i, ms i < 1) (r : ℕ) :
    ∫⁻ ω, cascadeSqPair k r U ω * (cascadeSum k G ω)⁻¹ ^ 2 ∂cascadeLaw k ms μs
      = ∑ j ∈ Finset.Ico r (k + 1), ENNReal.ofReal (mExt ms (j + 1) - mExt ms j)
          * cascadeTiltPair k j ms μs G
              (fun zs => U zs / (G (fun i => (zs i).1) * G (fun i => (zs i).2))) := by
  have h := lintegral_cascadeSqPair_mul_rpow k ms μs hU hG hGpos hfin hsm hlt
    (a := 0) le_rfl one_pos hpos r
  simp only [ENNReal.rpow_zero, lintegral_const, measure_univ, mul_one, sub_zero, div_one,
    mExt'_zero_exp] at h
  rw [← h]
  refine lintegral_congr fun ω => ?_
  rw [zero_sub, ENNReal.rpow_neg, ENNReal.rpow_two, ENNReal.inv_pow]

/-- **Talagrand's Theorem 14.3.5** (Vol. II, (14.47)): for `1 ≤ r ≤ k + 1`,

`𝔼 ⟨1_{(α,γ) = r} Ũ(α, γ)⟩
  = (m_r - m_{r-1}) 𝔼(W₁ ⋯ W_{r-1} W_r¹ W_r² ⋯ W_k¹ W_k² Ǔ)`,

where `1_{(α,γ)=r} = 1_{α|(r-1) = γ|(r-1)} - 1_{α|r = γ|r}` and the two copies of the marks agree
below level `r` and are independent from level `r` on. Stated additively, since subtraction in
`ℝ≥0∞` is truncated: the level-`r` average plus the term is the level-`(r-1)` average.

Talagrand proves this by polarization from the case `Ũ = U ⊗ U'` — where it is (14.43), obtained
from Proposition 14.3.2 through (14.42) — and then approximates a general `Ũ` by sums of
products. Here the identity is proved directly for a general `Ũ` by induction on the number of
levels, so no approximation argument is needed; (14.42) itself is `cascadeTiltPair_prod`. -/
theorem lintegral_cascadeSqPair_succ_add (k : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {U : (Fin k → T × T) → ℝ≥0∞} {G : (Fin k → T) → ℝ≥0∞}
    (hU : Measurable U) (hG : Measurable G) (hGpos : ∀ zs, 0 < G zs)
    (hfin : ∫⁻ zs, G zs ∂Measure.pi μs ≠ ∞) (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i)
    (hlt : ∀ i, ms i < 1) {j : ℕ} (hj : j ≤ k) :
    (∫⁻ ω, cascadeSqPair k (j + 1) U ω * (cascadeSum k G ω)⁻¹ ^ 2 ∂cascadeLaw k ms μs)
        + ENNReal.ofReal (mExt ms (j + 1) - mExt ms j)
          * cascadeTiltPair k j ms μs G
              (fun zs => U zs / (G (fun i => (zs i).1) * G (fun i => (zs i).2)))
      = ∫⁻ ω, cascadeSqPair k j U ω * (cascadeSum k G ω)⁻¹ ^ 2 ∂cascadeLaw k ms μs := by
  rw [lintegral_cascadeSqPair_mul_inv_sq k ms μs hU hG hGpos hfin hsm hpos hlt j,
    lintegral_cascadeSqPair_mul_inv_sq k ms μs hU hG hGpos hfin hsm hpos hlt (j + 1),
    Finset.sum_eq_sum_Ico_succ_bot (by omega : j < k + 1)]
  ring

/-! ### Consistency with the identities for a product numerator -/

omit [Nonempty T] in
/-- **The coupled tilted average of a product numerator is the tilted square**: for a numerator
`U = A ⊗ A`, `Ǔ = (A/G) ⊗ (A/G)` and `cascadeTiltPair` collapses to `cascadeTiltSq` by (14.42).
Together with `cascadeSqPair_prod` this exhibits `lintegral_cascadeSqPair_mul_inv_sq` at
`U = A ⊗ A` as `lintegral_cascadeSq_num_mul_inv_sq`, so Theorem 14.3.5 and (14.33) — proved by
two separate inductions — agree. -/
theorem cascadeTiltPair_div_prod (k j : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {A G : (Fin k → T) → ℝ≥0∞} (hA : Measurable A)
    (hG : Measurable G) (hGpos : ∀ zs, 0 < G zs) :
    cascadeTiltPair k j ms μs G
        (fun zs => A (fun i => (zs i).1) * A (fun i => (zs i).2)
          / (G (fun i => (zs i).1) * G (fun i => (zs i).2)))
      = cascadeTiltSq k j ms μs G (fun zs => A zs / G zs) := by
  rw [show (fun zs : Fin k → T × T => A (fun i => (zs i).1) * A (fun i => (zs i).2)
        / (G (fun i => (zs i).1) * G (fun i => (zs i).2)))
      = fun zs : Fin k → T × T => (fun zs => A zs / G zs) (fun i => (zs i).1)
        * (fun zs => A zs / G zs) (fun i => (zs i).2) from by
    funext zs
    exact (ENNReal.div_mul_div_comm_of_ne_zero (hGpos _).ne' (hGpos _).ne').symm]
  exact cascadeTiltPair_prod k j ms μs hG (hA.div hG)

/-- **Theorem 14.3.5 specializes to (14.33)**: the two identities, proved by separate inductions,
agree at a product numerator. -/
theorem lintegral_cascadeSqPair_mul_inv_sq_prod (k : ℕ) (ms : Fin k → ℝ)
    (μs : Fin k → Measure T) [∀ i, IsProbabilityMeasure (μs i)] {A G : (Fin k → T) → ℝ≥0∞}
    (hA : Measurable A) (hG : Measurable G) (hGpos : ∀ zs, 0 < G zs)
    (hfin : ∫⁻ zs, G zs ∂Measure.pi μs ≠ ∞) (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i)
    (hlt : ∀ i, ms i < 1) (r : ℕ) :
    ∫⁻ ω, cascadeSqPair k r (fun zs => A (fun i => (zs i).1) * A (fun i => (zs i).2)) ω
        * (cascadeSum k G ω)⁻¹ ^ 2 ∂cascadeLaw k ms μs
      = ∑ j ∈ Finset.Ico r (k + 1), ENNReal.ofReal (mExt ms (j + 1) - mExt ms j)
          * cascadeTiltSq k j ms μs G (fun zs => A zs / G zs) := by
  have hAA : Measurable fun zs : Fin k → T × T =>
      A (fun i => (zs i).1) * A (fun i => (zs i).2) :=
    (hA.comp measurable_pairFst).mul (hA.comp measurable_pairSnd)
  rw [lintegral_cascadeSqPair_mul_inv_sq k ms μs hAA hG hGpos hfin hsm hpos hlt r]
  exact Finset.sum_congr rfl fun j _ => by
    rw [cascadeTiltPair_div_prod k j ms μs hA hG hGpos]

/-- The two left-hand sides also agree, by `cascadeSqPair_prod`: Theorem 14.3.5 at a product
numerator *is* `lintegral_cascadeSq_num_mul_inv_sq`. -/
theorem lintegral_cascadeSqPair_prod_eq_cascadeSq (k : ℕ) (ms : Fin k → ℝ)
    (μs : Fin k → Measure T) [∀ i, IsProbabilityMeasure (μs i)] {A G : (Fin k → T) → ℝ≥0∞}
    (hA : Measurable A) (r : ℕ) :
    ∫⁻ ω, cascadeSqPair k r (fun zs => A (fun i => (zs i).1) * A (fun i => (zs i).2)) ω
        * (cascadeSum k G ω)⁻¹ ^ 2 ∂cascadeLaw k ms μs
      = ∫⁻ ω, cascadeSq k r A ω * (cascadeSum k G ω)⁻¹ ^ 2 ∂cascadeLaw k ms μs :=
  lintegral_congr fun ω => by rw [cascadeSqPair_prod k r hA ω]

/-! ### The coupled cascade of Lemma 14.3.6 -/

/-- **Talagrand's sequence (14.48)** `m*`: the parameters below level `r` are halved, because
below `r` the two copies of the marks coincide and the coupled recursion `J_p = F_p¹ + F_p²`
doubles the exponent. -/
def halveBelow {k : ℕ} (r : ℕ) (ms : Fin k → ℝ) : Fin k → ℝ :=
  fun i => if (i : ℕ) < r then ms i / 2 else ms i

/-- **The mark laws of the coupled construction (14.40)**: the two copies share their mark below
level `r` — the diagonal image of `μ_p` — and are independent from level `r` on. -/
def pairMarkLaw {k : ℕ} (r : ℕ) (μs : Fin k → Measure T) : Fin k → Measure (T × T) :=
  fun i => if (i : ℕ) < r then (μs i).map (fun z => (z, z)) else (μs i).prod (μs i)

instance {k : ℕ} (r : ℕ) (μs : Fin k → Measure T) [∀ i, IsProbabilityMeasure (μs i)] (i : Fin k) :
    IsProbabilityMeasure (pairMarkLaw r μs i) := by
  unfold pairMarkLaw
  split_ifs
  · exact Measure.isProbabilityMeasure_map (measurable_id.prodMk measurable_id).aemeasurable
  · infer_instance

omit [MeasurableSpace T] in
@[simp] lemma halveBelow_zero {k : ℕ} (ms : Fin k → ℝ) : halveBelow 0 ms = ms := by
  funext i
  simp [halveBelow]

omit [Nonempty T] in
@[simp] lemma pairMarkLaw_zero {k : ℕ} (μs : Fin k → Measure T) :
    pairMarkLaw 0 μs = fun i => (μs i).prod (μs i) := by
  funext i
  simp [pairMarkLaw]

omit [MeasurableSpace T] in
lemma halveBelow_succ_zero {k : ℕ} (r : ℕ) (ms : Fin (k + 1) → ℝ) :
    halveBelow (r + 1) ms 0 = ms 0 / 2 := by simp [halveBelow]

omit [Nonempty T] in
lemma pairMarkLaw_succ_zero {k : ℕ} (r : ℕ) (μs : Fin (k + 1) → Measure T) :
    pairMarkLaw (r + 1) μs 0 = (μs 0).map (fun z => (z, z)) := by simp [pairMarkLaw]

omit [MeasurableSpace T] in
lemma tail_halveBelow {k : ℕ} (r : ℕ) (ms : Fin (k + 1) → ℝ) :
    Fin.tail (halveBelow r ms) = halveBelow (r - 1) (Fin.tail ms) := by
  funext i
  simp only [halveBelow, Fin.tail, Fin.val_succ]
  by_cases h : (i : ℕ) + 1 < r
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h),
      ite_eq_left_of_eq_true _ _ (eq_true (show (i : ℕ) < r - 1 by omega))]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h),
      ite_eq_right_of_eq_false _ _ (eq_false (show ¬((i : ℕ) < r - 1) by omega))]

omit [Nonempty T] in
lemma tail_pairMarkLaw {k : ℕ} (r : ℕ) (μs : Fin (k + 1) → Measure T) :
    Fin.tail (pairMarkLaw r μs) = pairMarkLaw (r - 1) (Fin.tail μs) := by
  funext i
  simp only [pairMarkLaw, Fin.tail, Fin.val_succ]
  by_cases h : (i : ℕ) + 1 < r
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h),
      ite_eq_left_of_eq_true _ _ (eq_true (show (i : ℕ) < r - 1 by omega))]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h),
      ite_eq_right_of_eq_false _ _ (eq_false (show ¬((i : ℕ) < r - 1) by omega))]

omit [Nonempty T] in
/-- **The recursion factorizes over two independent copies**: this is the case `p ≥ r` of
Talagrand's Lemma 14.3.6(a), `J_p = F_p¹ + F_p²`, in the `ℝ≥0∞` form `R̂_p = R_p¹ R_p²`. -/
theorem cascadeRec_prod (k : ℕ) :
    ∀ (ms : Fin k → ℝ) (μs : Fin k → Measure T) [∀ i, IsProbabilityMeasure (μs i)]
      {G₁ G₂ : (Fin k → T) → ℝ≥0∞}, Measurable G₁ → Measurable G₂ → (∀ i, 0 < ms i) →
      cascadeRec k ms (fun i => (μs i).prod (μs i))
          (fun zs => G₁ (fun i => (zs i).1) * G₂ (fun i => (zs i).2))
        = cascadeRec k ms μs G₁ * cascadeRec k ms μs G₂ := by
  induction k with
  | zero =>
    intro ms μs _ G₁ G₂ _ _ _
    simp only [cascadeRec_zero]
    congr 1 <;> exact congrArg _ (Subsingleton.elim _ _)
  | succ k ih =>
    intro ms μs hμs G₁ G₂ hG₁ hG₂ hpos
    have (i : Fin (k + 1)) : IsProbabilityMeasure (μs i) := hμs i
    have hm : 0 < ms 0 := hpos 0
    rw [cascadeRec_succ, cascadeRec_succ, cascadeRec_succ]
    have hcons : ∀ p : T × T,
        (fun zs : Fin k → T × T => (fun zs : Fin (k + 1) → T × T =>
            G₁ (fun i => (zs i).1) * G₂ (fun i => (zs i).2)) (Fin.cons p zs))
          = fun zs : Fin k → T × T => G₁ (Fin.cons p.1 fun i => (zs i).1)
            * G₂ (Fin.cons p.2 fun i => (zs i).2) := by
      intro p
      funext zs
      simp only
      rw [fin_cons_fst p zs, fin_cons_snd p zs]
    have hin : ∀ p : T × T,
        cascadeRec k (Fin.tail ms) (Fin.tail fun i => (μs i).prod (μs i))
            (fun zs => (fun zs : Fin (k + 1) → T × T =>
              G₁ (fun i => (zs i).1) * G₂ (fun i => (zs i).2)) (Fin.cons p zs))
          = cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G₁ (Fin.cons p.1 zs))
            * cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G₂ (Fin.cons p.2 zs)) := by
      intro p
      rw [hcons p]
      exact ih (Fin.tail ms) (Fin.tail μs)
        (G₁ := fun zs => G₁ (Fin.cons p.1 zs)) (G₂ := fun zs => G₂ (Fin.cons p.2 zs))
        (hG₁.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
        (hG₂.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
        (fun i => hpos i.succ)
    simp_rw [hin]
    have hR₁ : Measurable fun z : T =>
        cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G₁ (Fin.cons z zs)) :=
      measurable_cascadeRec_cons k _ _ hG₁
    have hR₂ : Measurable fun z : T =>
        cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G₂ (Fin.cons z zs)) :=
      measurable_cascadeRec_cons k _ _ hG₂
    have hsplit : ∀ p : T × T,
        (cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G₁ (Fin.cons p.1 zs))
            * cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G₂ (Fin.cons p.2 zs))) ^ ms 0
          = cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G₁ (Fin.cons p.1 zs)) ^ ms 0
            * cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G₂ (Fin.cons p.2 zs)) ^ ms 0 :=
      fun p => ENNReal.mul_rpow_of_nonneg _ _ hm.le
    simp_rw [hsplit]
    have hprod : ∫⁻ p : T × T,
          cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G₁ (Fin.cons p.1 zs)) ^ ms 0
            * cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G₂ (Fin.cons p.2 zs)) ^ ms 0
          ∂(μs 0).prod (μs 0)
        = (∫⁻ z, cascadeRec k (Fin.tail ms) (Fin.tail μs)
              (fun zs => G₁ (Fin.cons z zs)) ^ ms 0 ∂μs 0)
          * ∫⁻ z, cascadeRec k (Fin.tail ms) (Fin.tail μs)
              (fun zs => G₂ (Fin.cons z zs)) ^ ms 0 ∂μs 0 := by
      rw [lintegral_prod (fun p : T × T =>
        cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G₁ (Fin.cons p.1 zs)) ^ ms 0
          * cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G₂ (Fin.cons p.2 zs)) ^ ms 0)
        (((hR₁.comp measurable_fst).pow_const _).mul
          ((hR₂.comp measurable_snd).pow_const _)).aemeasurable]
      have hz : ∀ z₁ : T, ∫⁻ z₂, cascadeRec k (Fin.tail ms) (Fin.tail μs)
              (fun zs => G₁ (Fin.cons z₁ zs)) ^ ms 0
            * cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G₂ (Fin.cons z₂ zs)) ^ ms 0
            ∂μs 0
          = cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G₁ (Fin.cons z₁ zs)) ^ ms 0
            * ∫⁻ z, cascadeRec k (Fin.tail ms) (Fin.tail μs)
                (fun zs => G₂ (Fin.cons z zs)) ^ ms 0 ∂μs 0 := fun z₁ =>
        lintegral_const_mul _ (hR₂.pow_const _)
      simp_rw [hz]
      exact lintegral_mul_const _ (hR₁.pow_const _)
    rw [hprod, ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1 / ms 0)]

omit [MeasurableSpace T] [Nonempty T] in
/-- The `Fin.cons` of a product function splits. -/
lemma cons_prod_fun {k : ℕ} (G₁ G₂ : (Fin (k + 1) → T) → ℝ≥0∞) (p : T × T) :
    (fun zs : Fin k → T × T => (fun zs : Fin (k + 1) → T × T =>
        G₁ (fun i => (zs i).1) * G₂ (fun i => (zs i).2)) (Fin.cons p zs))
      = fun zs : Fin k → T × T => G₁ (Fin.cons p.1 fun i => (zs i).1)
        * G₂ (Fin.cons p.2 fun i => (zs i).2) := by
  funext zs
  simp only
  rw [fin_cons_fst p zs, fin_cons_snd p zs]

omit [Nonempty T] in
/-- **The tilting weight of the doubled cascade is the product of the two weights**: the case
`p ≥ r` of Talagrand's Lemma 14.3.6(b), `V_p = W_p¹ W_p²`. -/
theorem cascadeW_prod (k : ℕ) (ms : Fin (k + 1) → ℝ) (μs : Fin (k + 1) → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {G₁ G₂ : (Fin (k + 1) → T) → ℝ≥0∞}
    (hG₁ : Measurable G₁) (hG₂ : Measurable G₂) (hG₁pos : ∀ zs, 0 < G₁ zs)
    (hG₂pos : ∀ zs, 0 < G₂ zs) (hpos : ∀ i, 0 < ms i) (p : T × T) :
    cascadeW k ms (fun i => (μs i).prod (μs i))
        (fun zs => G₁ (fun i => (zs i).1) * G₂ (fun i => (zs i).2)) p
      = cascadeW k ms μs G₁ p.1 * cascadeW k ms μs G₂ p.2 := by
  have hR₁0 : cascadeRec (k + 1) ms μs G₁ ≠ 0 :=
    (cascadeRec_pos (k + 1) ms μs hG₁ hG₁pos hpos).ne'
  have hR₂0 : cascadeRec (k + 1) ms μs G₂ ≠ 0 :=
    (cascadeRec_pos (k + 1) ms μs hG₂ hG₂pos hpos).ne'
  have htailprod : (Fin.tail fun i => (μs i).prod (μs i))
      = fun i => (Fin.tail μs i).prod (Fin.tail μs i) := rfl
  unfold cascadeW
  rw [cons_prod_fun G₁ G₂ p, htailprod,
    cascadeRec_prod k (Fin.tail ms) (Fin.tail μs)
      (G₁ := fun zs => G₁ (Fin.cons p.1 zs)) (G₂ := fun zs => G₂ (Fin.cons p.2 zs))
      (hG₁.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
      (hG₂.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
      (fun i => hpos i.succ),
    cascadeRec_prod (k + 1) ms μs hG₁ hG₂ hpos,
    ← ENNReal.div_mul_div_comm_of_ne_zero hR₁0 hR₂0,
    ENNReal.mul_rpow_of_nonneg _ _ (hpos 0).le]

omit [Nonempty T] in
/-- **The two-copy tilted average is the tilted average of the doubled cascade**: the case `r = 0`
of Corollary 14.3.7. The mark laws are the products `μ_p ⊗ μ_p` and the function is
`Ĝ = G₁ ⊗ G₂`, i.e. `F̂ = F¹ + F²`. -/
theorem cascadeTiltProd_eq_cascadeTilt (k : ℕ) :
    ∀ (ms : Fin k → ℝ) (μs : Fin k → Measure T) [∀ i, IsProbabilityMeasure (μs i)]
      {G₁ G₂ : (Fin k → T) → ℝ≥0∞} {U : (Fin k → T × T) → ℝ≥0∞}, Measurable G₁ → Measurable G₂ →
      Measurable U → (∀ zs, 0 < G₁ zs) → (∀ zs, 0 < G₂ zs) → (∀ i, 0 < ms i) →
      cascadeTiltProd k ms μs G₁ G₂ U
        = cascadeTilt k ms (fun i => (μs i).prod (μs i))
            (fun zs => G₁ (fun i => (zs i).1) * G₂ (fun i => (zs i).2)) U := by
  induction k with
  | zero =>
    intro ms μs _ G₁ G₂ U _ _ _ _ _ _
    rw [cascadeTiltProd_zero, cascadeTilt_zero]
  | succ k ih =>
    intro ms μs hμs G₁ G₂ U hG₁ hG₂ hU hG₁pos hG₂pos hpos
    have (i : Fin (k + 1)) : IsProbabilityMeasure (μs i) := hμs i
    rw [cascadeTiltProd_succ, cascadeTilt_succ]
    have hin : ∀ p : T × T,
        cascadeW k ms (fun i => (μs i).prod (μs i))
              (fun zs => G₁ (fun i => (zs i).1) * G₂ (fun i => (zs i).2)) p
            * cascadeTilt k (Fin.tail ms) (Fin.tail fun i => (μs i).prod (μs i))
                (fun zs => (fun zs : Fin (k + 1) → T × T =>
                  G₁ (fun i => (zs i).1) * G₂ (fun i => (zs i).2)) (Fin.cons p zs))
                (fun zs => U (Fin.cons p zs))
          = cascadeW k ms μs G₁ p.1 * cascadeW k ms μs G₂ p.2
            * cascadeTiltProd k (Fin.tail ms) (Fin.tail μs)
                (fun zs => G₁ (Fin.cons p.1 zs)) (fun zs => G₂ (Fin.cons p.2 zs))
                (fun zs => U (Fin.cons p zs)) := by
      intro p
      rw [cascadeW_prod k ms μs hG₁ hG₂ hG₁pos hG₂pos hpos p, cons_prod_fun G₁ G₂ p]
      congr 1
      exact (ih (Fin.tail ms) (Fin.tail μs)
        (G₁ := fun zs => G₁ (Fin.cons p.1 zs)) (G₂ := fun zs => G₂ (Fin.cons p.2 zs))
        (U := fun zs => U (Fin.cons p zs))
        (hG₁.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
        (hG₂.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
        (hU.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
        (fun zs => hG₁pos _) (fun zs => hG₂pos _) (fun i => hpos i.succ)).symm
    simp_rw [hin]
    have hjoint : Measurable fun p : T × T => cascadeW k ms μs G₁ p.1 * cascadeW k ms μs G₂ p.2
        * cascadeTiltProd k (Fin.tail ms) (Fin.tail μs)
            (fun zs => G₁ (Fin.cons p.1 zs)) (fun zs => G₂ (Fin.cons p.2 zs))
            (fun zs => U (Fin.cons p zs)) := by
      refine (((measurable_cascadeW k ms μs hG₁).comp measurable_fst).mul
        ((measurable_cascadeW k ms μs hG₂).comp measurable_snd)).mul ?_
      refine measurable_cascadeTiltProd_prod k (Fin.tail ms) (Fin.tail μs) ?_ ?_ ?_
      · exact hG₁.comp (measurable_fin_cons.comp
          ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
      · exact hG₂.comp (measurable_fin_cons.comp
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
      · exact hU.comp measurable_fin_cons
    rw [lintegral_prod _ hjoint.aemeasurable]

omit [MeasurableSpace T] [Nonempty T] in
private lemma ENNReal.sq_rpow_half {m : ℝ} (_hm : m ≠ 0) (x : ℝ≥0∞) :
    (x ^ (2 : ℕ)) ^ (m / 2) = x ^ m := by
  rw [← ENNReal.rpow_natCast x 2, ← ENNReal.rpow_mul]
  congr 1
  push_cast
  ring

omit [MeasurableSpace T] [Nonempty T] in
private lemma ENNReal.rpow_one_div_half {m : ℝ} (hm : m ≠ 0) (y : ℝ≥0∞) :
    y ^ (1 / (m / 2)) = (y ^ (1 / m)) ^ (2 : ℕ) := by
  rw [← ENNReal.rpow_natCast (y ^ (1 / m)) 2, ← ENNReal.rpow_mul]
  congr 1
  push_cast
  field_simp


/-- `cascadeTilt` is congruent in the mark laws: the instance argument is a `Prop`, so equal
mark laws give equal tilted averages. Needed because rewriting a measure inside `cascadeTilt`
directly is blocked by the instance argument (`motive is not type correct`). -/
lemma cascadeTilt_congr_measure {S : Type u} [MeasurableSpace S] {k : ℕ} (ms : Fin k → ℝ)
    {νs₁ νs₂ : Fin k → Measure S} [∀ i, IsProbabilityMeasure (νs₁ i)]
    [∀ i, IsProbabilityMeasure (νs₂ i)] (h : νs₁ = νs₂) (G A : (Fin k → S) → ℝ≥0∞) :
    cascadeTilt k ms νs₁ G A = cascadeTilt k ms νs₂ G A := by
  subst h
  rfl

omit [Nonempty T] in
/-- The diagonal map into the pair space. -/
lemma measurable_diagT : Measurable fun z : T => ((z, z) : T × T) :=
  measurable_id.prodMk measurable_id

omit [MeasurableSpace T] [Nonempty T] in
/-- The pair function along a diagonal `Fin.cons`. -/
lemma cons_diag_fun {k : ℕ} (G : (Fin (k + 1) → T) → ℝ≥0∞) (z : T) :
    (fun zs : Fin k → T × T =>
        G (fun i => ((Fin.cons (z, z) zs : Fin (k + 1) → T × T) i).1)
          * G (fun i => ((Fin.cons (z, z) zs : Fin (k + 1) → T × T) i).2))
      = fun zs : Fin k → T × T => (fun zs => G (Fin.cons z zs)) (fun i => (zs i).1)
        * (fun zs => G (Fin.cons z zs)) (fun i => (zs i).2) := by
  funext zs
  rw [fin_cons_fst (z, z) zs, fin_cons_snd (z, z) zs]

/-- **The coupling map of Talagrand's (14.151)** on a pair of raw marks: below level `τ` the two
copies are given the *same* mark, from `τ` on they keep their own. Pushing the product law
`μ ⊗ μ` forward along it gives the coupled mark laws `pairMarkLaw`
(`map_couplingMap_prod_eq_pairMarkLaw`). -/
def couplingMap (τ p : ℕ) : T × T → T × T :=
  if p < τ then fun z => (z.1, z.1) else id

omit [Nonempty T] in
lemma measurable_couplingMap (τ p : ℕ) : Measurable (couplingMap (T := T) τ p) := by
  unfold couplingMap
  split_ifs
  · exact measurable_fst.prodMk measurable_fst
  · exact measurable_id

omit [Nonempty T] in
/-- The coupled mark laws are the pushforwards of the product laws along the coupling maps. -/
lemma map_couplingMap_prod_eq_pairMarkLaw {k : ℕ} (τ : ℕ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] :
    (fun p : Fin k => ((μs p).prod (μs p)).map (couplingMap τ p)) = pairMarkLaw τ μs := by
  funext p
  unfold couplingMap pairMarkLaw
  split_ifs with hp
  · have hcomp : (fun z : T × T => (z.1, z.1)) = (fun x : T => (x, x)) ∘ Prod.fst := rfl
    rw [hcomp, ← Measure.map_map measurable_diagT measurable_fst,
      Measure.map_fst_prod, measure_univ, one_smul]
  · exact Measure.map_id

omit [Nonempty T] in
/-- **Talagrand's Lemma 14.3.6(a)** in `ℝ≥0∞` form: for the coupled cascade — the two copies of
the marks sharing their mark below level `r`, with the halved parameters (14.48) — the recursion
of `Ĝ = G ⊗ G` is the square of the recursion of `G`. This is `J_p = F_p¹ + F_p²`, together with
`F_p¹ = F_p² = F_p` for `p ≤ r`. -/
theorem cascadeRec_pairMarkLaw (k : ℕ) :
    ∀ (r : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T) [∀ i, IsProbabilityMeasure (μs i)]
      {G : (Fin k → T) → ℝ≥0∞}, Measurable G → (∀ i, 0 < ms i) →
      cascadeRec k (halveBelow r ms) (pairMarkLaw r μs)
          (fun zs => G (fun i => (zs i).1) * G (fun i => (zs i).2))
        = cascadeRec k ms μs G ^ (2 : ℕ) := by
  induction k with
  | zero =>
    intro r ms μs _ G _ _
    simp only [cascadeRec_zero, pow_two]
    congr 1 <;> exact congrArg _ (Subsingleton.elim _ _)
  | succ k ih =>
    intro r ms μs hμs G hG hpos
    have (i : Fin (k + 1)) : IsProbabilityMeasure (μs i) := hμs i
    have hm : 0 < ms 0 := hpos 0
    cases r with
    | zero =>
      rw [halveBelow_zero, pairMarkLaw_zero, cascadeRec_prod (k + 1) ms μs hG hG hpos, pow_two]
    | succ r =>
      have hcons : Measurable (uncurry fun p : T × T => fun zs : Fin k → T × T =>
          G (fun i => ((Fin.cons p zs : Fin (k + 1) → T × T) i).1)
            * G (fun i => ((Fin.cons p zs : Fin (k + 1) → T × T) i).2)) :=
        ((hG.comp measurable_pairFst).mul (hG.comp measurable_pairSnd)).comp measurable_fin_cons
      have hfm : Measurable fun p : T × T =>
          (cascadeRec k (halveBelow r (Fin.tail ms)) (pairMarkLaw r (Fin.tail μs))
            (fun zs => G (fun i => ((Fin.cons p zs : Fin (k + 1) → T × T) i).1)
              * G (fun i => ((Fin.cons p zs : Fin (k + 1) → T × T) i).2)))
            ^ (halveBelow (r + 1) ms 0) :=
        (measurable_cascadeRec_prod k (halveBelow r (Fin.tail ms))
          (pairMarkLaw r (Fin.tail μs)) (α := T × T) hcons).pow_const _
      rw [cascadeRec_succ, cascadeRec_succ, tail_halveBelow, tail_pairMarkLaw,
        pairMarkLaw_succ_zero]
      simp only [Nat.add_sub_cancel]
      rw [lintegral_map hfm measurable_diagT]
      have hpt : ∀ z : T,
          (cascadeRec k (halveBelow r (Fin.tail ms)) (pairMarkLaw r (Fin.tail μs))
            (fun zs => G (fun i => ((Fin.cons (z, z) zs : Fin (k + 1) → T × T) i).1)
              * G (fun i => ((Fin.cons (z, z) zs : Fin (k + 1) → T × T) i).2)))
            ^ (halveBelow (r + 1) ms 0)
            = cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs)) ^ ms 0 := by
        intro z
        rw [cons_diag_fun G z, halveBelow_succ_zero,
          ih r (Fin.tail ms) (Fin.tail μs) (G := fun zs => G (Fin.cons z zs))
            (hG.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
            (fun i => hpos i.succ),
          ENNReal.sq_rpow_half hm.ne']
      simp_rw [hpt]
      rw [halveBelow_succ_zero, ENNReal.rpow_one_div_half hm.ne']

omit [Nonempty T] in
/-- **`Y₀ = 2X₀` in raw coordinates** (Talagrand Vol. II, Proposition 14.6.3): on independent
pairs of marks, the recursion with the parameters halved below `τ` of a product `G ⊗ G` of the
same terminal function evaluated on the coupled marks `couplingMap τ p` is the square of the
one-copy recursion. -/
theorem cascadeRec_coupling (k τ : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {G : (Fin k → T) → ℝ≥0∞} (hG : Measurable G)
    (hpos : ∀ i, 0 < ms i) :
    cascadeRec k (halveBelow τ ms) (fun p => (μs p).prod (μs p))
        (fun zs => G (fun i => (couplingMap τ i (zs i)).1)
          * G (fun i => (couplingMap τ i (zs i)).2))
      = cascadeRec k ms μs G ^ (2 : ℕ) := by
  have hĜ : Measurable fun zs : Fin k → T × T => G (fun i => (zs i).1) * G (fun i => (zs i).2) :=
    (hG.comp (measurable_pi_lambda _ fun i => measurable_fst.comp (measurable_pi_apply i))).mul
      (hG.comp (measurable_pi_lambda _ fun i => measurable_snd.comp (measurable_pi_apply i)))
  rw [← cascadeRec_map k (halveBelow τ ms) (fun p => (μs p).prod (μs p))
    (fun i => couplingMap τ i) (fun i => measurable_couplingMap τ i) hĜ,
    map_couplingMap_prod_eq_pairMarkLaw τ μs, cascadeRec_pairMarkLaw k τ ms μs hG hpos]


omit [Nonempty T] in
/-- **Talagrand's Lemma 14.3.6(b)**, case `p < r`: the tilting weight of the coupled cascade on
the diagonal is the single weight `W_p`. -/
theorem cascadeW_pairMarkLaw_diag (k r : ℕ) (ms : Fin (k + 1) → ℝ)
    (μs : Fin (k + 1) → Measure T) [∀ i, IsProbabilityMeasure (μs i)]
    {G : (Fin (k + 1) → T) → ℝ≥0∞} (hG : Measurable G) (hpos : ∀ i, 0 < ms i) (z : T) :
    cascadeW k (halveBelow (r + 1) ms) (pairMarkLaw (r + 1) μs)
        (fun zs => G (fun i => (zs i).1) * G (fun i => (zs i).2)) (z, z)
      = cascadeW k ms μs G z := by
  have hm : 0 < ms 0 := hpos 0
  unfold cascadeW
  rw [tail_halveBelow, tail_pairMarkLaw]
  simp only [Nat.add_sub_cancel]
  rw [cons_diag_fun G z,
    cascadeRec_pairMarkLaw k r (Fin.tail ms) (Fin.tail μs) (G := fun zs => G (Fin.cons z zs))
      (hG.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
      (fun i => hpos i.succ),
    cascadeRec_pairMarkLaw (k + 1) (r + 1) ms μs hG hpos, halveBelow_succ_zero,
    ← ENNReal.div_pow, ENNReal.sq_rpow_half hm.ne']

omit [Nonempty T] in
/-- **Corollary 14.3.7** (Talagrand Vol. II, (14.52)): the coupled tilted average
`𝔼(W₁ ⋯ W_r W_{r+1}¹ W_{r+1}² ⋯ W_k¹ W_k² Ũ)` is an *ordinary* tilted average `𝔼(V₁ ⋯ V_k Ũ)` —
of exactly the shape appearing on the left of (14.27) — for the cascade whose marks are the
coupled pairs `pairMarkLaw r μs` of (14.40), whose parameters are the halved sequence
`halveBelow r ms` of (14.48), and whose function is `Ĝ = G ⊗ G`, i.e. `F̂ = F¹ + F²`.

This is the point of Lemma 14.3.6, and what makes the right-hand side of Theorem 14.3.5
accessible to the machinery of §14.2: combined with `lintegral_cascadeSum_div_cascadeSum` it
turns the right-hand side of (14.47) into a cascade Gibbs average, which is the entry point of
§14.5. -/
theorem cascadeTiltPair_eq_cascadeTilt (k : ℕ) :
    ∀ (r : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T) [∀ i, IsProbabilityMeasure (μs i)]
      {G : (Fin k → T) → ℝ≥0∞} {U : (Fin k → T × T) → ℝ≥0∞}, Measurable G → Measurable U →
      (∀ zs, 0 < G zs) → (∀ i, 0 < ms i) →
      cascadeTiltPair k r ms μs G U
        = cascadeTilt k (halveBelow r ms) (pairMarkLaw r μs)
            (fun zs => G (fun i => (zs i).1) * G (fun i => (zs i).2)) U := by
  induction k with
  | zero =>
    intro r ms μs _ G U _ _ _ _
    rw [cascadeTiltPair_zero_levels, cascadeTilt_zero]
  | succ k ih =>
    intro r ms μs hμs G U hG hU hGpos hpos
    have (i : Fin (k + 1)) : IsProbabilityMeasure (μs i) := hμs i
    cases r with
    | zero =>
      rw [cascadeTiltPair_zero, halveBelow_zero]
      exact cascadeTiltProd_eq_cascadeTilt (k + 1) ms μs hG hG hU hGpos hGpos hpos
    | succ r =>
      have hcons : Measurable (uncurry fun p : T × T => fun zs : Fin k → T × T =>
          G (fun i => ((Fin.cons p zs : Fin (k + 1) → T × T) i).1)
            * G (fun i => ((Fin.cons p zs : Fin (k + 1) → T × T) i).2)) :=
        ((hG.comp measurable_pairFst).mul (hG.comp measurable_pairSnd)).comp measurable_fin_cons
      have hfm : Measurable fun p : T × T =>
          cascadeW k (halveBelow (r + 1) ms) (pairMarkLaw (r + 1) μs)
              (fun zs => G (fun i => (zs i).1) * G (fun i => (zs i).2)) p
            * cascadeTilt k (halveBelow r (Fin.tail ms)) (pairMarkLaw r (Fin.tail μs))
                (fun zs => G (fun i => ((Fin.cons p zs : Fin (k + 1) → T × T) i).1)
                  * G (fun i => ((Fin.cons p zs : Fin (k + 1) → T × T) i).2))
                (fun zs => U (Fin.cons p zs)) := by
        refine (measurable_cascadeW k (halveBelow (r + 1) ms) (pairMarkLaw (r + 1) μs)
          ((hG.comp measurable_pairFst).mul (hG.comp measurable_pairSnd))).mul ?_
        exact measurable_cascadeTilt_prod k (halveBelow r (Fin.tail ms))
          (pairMarkLaw r (Fin.tail μs)) hcons (hU.comp measurable_fin_cons)
      have htailEq : Fin.tail (pairMarkLaw (r + 1) μs) = pairMarkLaw r (Fin.tail μs) := by
        rw [tail_pairMarkLaw]
        simp
      have hswap : ∀ p : T × T,
          cascadeTilt k (Fin.tail (halveBelow (r + 1) ms)) (Fin.tail (pairMarkLaw (r + 1) μs))
              (fun zs => G (fun i => ((Fin.cons p zs : Fin (k + 1) → T × T) i).1)
                * G (fun i => ((Fin.cons p zs : Fin (k + 1) → T × T) i).2))
              (fun zs => U (Fin.cons p zs))
            = cascadeTilt k (halveBelow r (Fin.tail ms)) (pairMarkLaw r (Fin.tail μs))
              (fun zs => G (fun i => ((Fin.cons p zs : Fin (k + 1) → T × T) i).1)
                * G (fun i => ((Fin.cons p zs : Fin (k + 1) → T × T) i).2))
              (fun zs => U (Fin.cons p zs)) := by
        intro p
        rw [cascadeTilt_congr_measure (Fin.tail (halveBelow (r + 1) ms)) htailEq,
          tail_halveBelow]
        simp
      rw [cascadeTiltPair_succ, cascadeTilt_succ, pairMarkLaw_succ_zero]
      simp_rw [hswap]
      rw [lintegral_map hfm measurable_diagT]
      refine lintegral_congr fun z => ?_
      rw [cascadeW_pairMarkLaw_diag k r ms μs hG hpos z, cons_diag_fun G z,
        ih r (Fin.tail ms) (Fin.tail μs) (G := fun zs => G (Fin.cons z zs))
          (U := fun zs => U (Fin.cons (z, z) zs))
          (hG.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
          (hU.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
          (fun zs => hGpos _) (fun i => hpos i.succ)]

omit [MeasurableSpace T] [Nonempty T] in
lemma halveBelow_pos {k : ℕ} {ms : Fin k → ℝ} (hpos : ∀ i, 0 < ms i) (r : ℕ) (i : Fin k) :
    0 < halveBelow r ms i := by
  unfold halveBelow
  split_ifs
  · linarith [hpos i]
  · exact hpos i

omit [MeasurableSpace T] [Nonempty T] in
lemma halveBelow_lt_one {k : ℕ} {ms : Fin k → ℝ} (hlt : ∀ i, ms i < 1) (r : ℕ) (i : Fin k) :
    halveBelow r ms i < 1 := by
  unfold halveBelow
  split_ifs
  · linarith [hlt i]
  · exact hlt i

omit [MeasurableSpace T] [Nonempty T] in
lemma halveBelow_strictMono {k : ℕ} {ms : Fin k → ℝ} (hsm : StrictMono ms)
    (hpos : ∀ i, 0 < ms i) (r : ℕ) : StrictMono (halveBelow r ms) := by
  intro i j hij
  have hij' : (i : ℕ) < j := hij
  have h := hsm hij
  unfold halveBelow
  split_ifs with hi hj hj
  · linarith
  · linarith [hpos i]
  · exact absurd hj (by omega)
  · exact h

omit [MeasurableSpace T] [Nonempty T] in
lemma strictMono_halveBelow {k : ℕ} {ms : Fin k → ℝ} (hsm : StrictMono ms)
    (hpos : ∀ i, 0 < ms i) (r : ℕ) : StrictMono (halveBelow r ms) := by
  intro i j hij
  have hij' : (i : ℕ) < (j : ℕ) := hij
  have h := hsm hij
  unfold halveBelow
  by_cases h1 : (i : ℕ) < r
  · by_cases h2 : (j : ℕ) < r
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_left_of_eq_true _ _ (eq_true h2)]
      linarith
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_right_of_eq_false _ _ (eq_false h2)]
      linarith [hpos i]
  · by_cases h2 : (j : ℕ) < r
    · exact absurd hij' (by omega)
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false h2)]
      exact h

/-- **Corollary 14.3.7** (Talagrand Vol. II, (14.52)) in the form of Theorem 14.3.5: the
right-hand side of (14.47) is the *ordinary* tilted average `𝔼(V₁ ⋯ V_k Ǔ)` of the coupled
cascade. -/
theorem lintegral_cascadeSqPair_succ_add_tilt (k : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {U : (Fin k → T × T) → ℝ≥0∞} {G : (Fin k → T) → ℝ≥0∞}
    (hU : Measurable U) (hG : Measurable G) (hGpos : ∀ zs, 0 < G zs)
    (hfin : ∫⁻ zs, G zs ∂Measure.pi μs ≠ ∞) (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i)
    (hlt : ∀ i, ms i < 1) {j : ℕ} (hj : j ≤ k) :
    (∫⁻ ω, cascadeSqPair k (j + 1) U ω * (cascadeSum k G ω)⁻¹ ^ 2 ∂cascadeLaw k ms μs)
        + ENNReal.ofReal (mExt ms (j + 1) - mExt ms j)
          * cascadeTilt k (halveBelow j ms) (pairMarkLaw j μs)
              (fun zs => G (fun i => (zs i).1) * G (fun i => (zs i).2))
              (fun zs => U zs / (G (fun i => (zs i).1) * G (fun i => (zs i).2)))
      = ∫⁻ ω, cascadeSqPair k j U ω * (cascadeSum k G ω)⁻¹ ^ 2 ∂cascadeLaw k ms μs := by
  have hĜ : Measurable fun zs : Fin k → T × T =>
      G (fun i => (zs i).1) * G (fun i => (zs i).2) :=
    (hG.comp measurable_pairFst).mul (hG.comp measurable_pairSnd)
  have hUdiv : Measurable fun zs : Fin k → T × T =>
      U zs / (G (fun i => (zs i).1) * G (fun i => (zs i).2)) := hU.div hĜ
  rw [← cascadeTiltPair_eq_cascadeTilt k j ms μs hG hUdiv hGpos hpos]
  exact lintegral_cascadeSqPair_succ_add k ms μs hU hG hGpos hfin hsm hpos hlt hj

/-- **Talagrand's (14.54)**: the coupled tilted average is a *cascade Gibbs average* — for the
cascade with the coupled marks (14.40), the halved parameters (14.48) and the function
`Ĝ = G ⊗ G`, i.e. `F̂ = F¹ + F²`. This is (14.27) applied to the coupled cascade, and it is the
form in which §14.5 uses Corollary 14.3.7. The hypothesis `hfin` is Talagrand's (14.4) for `F̂`;
it does not follow from (14.4) for `F`, because the diagonal levels square `G`. -/
theorem cascadeTiltPair_eq_lintegral_cascadeSum_div (k r : ℕ) (ms : Fin k → ℝ)
    (μs : Fin k → Measure T) [∀ i, IsProbabilityMeasure (μs i)]
    {G : (Fin k → T) → ℝ≥0∞} {U : (Fin k → T × T) → ℝ≥0∞} (hG : Measurable G)
    (hU : Measurable U) (hGpos : ∀ zs, 0 < G zs) (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i)
    (hlt : ∀ i, ms i < 1)
    (hfin : ∫⁻ zs, (fun zs : Fin k → T × T =>
        G (fun i => (zs i).1) * G (fun i => (zs i).2)) zs ∂Measure.pi (pairMarkLaw r μs) ≠ ∞) :
    cascadeTiltPair k r ms μs G
        (fun zs => U zs / (G (fun i => (zs i).1) * G (fun i => (zs i).2)))
      = ∫⁻ ω, cascadeSum k U ω
          / cascadeSum k (fun zs => G (fun i => (zs i).1) * G (fun i => (zs i).2)) ω
          ∂cascadeLaw k (halveBelow r ms) (pairMarkLaw r μs) := by
  have hĜ : Measurable fun zs : Fin k → T × T =>
      G (fun i => (zs i).1) * G (fun i => (zs i).2) :=
    (hG.comp measurable_pairFst).mul (hG.comp measurable_pairSnd)
  have hUdiv : Measurable fun zs : Fin k → T × T =>
      U zs / (G (fun i => (zs i).1) * G (fun i => (zs i).2)) := hU.div hĜ
  rw [cascadeTiltPair_eq_cascadeTilt k r ms μs hG hUdiv hGpos hpos,
    lintegral_cascadeSum_div_cascadeSum k (halveBelow r ms) (pairMarkLaw r μs) hU hĜ
      (fun zs => pos_iff_ne_zero.2 (mul_ne_zero (hGpos _).ne' (hGpos _).ne')) hfin
      (strictMono_halveBelow hsm hpos r) (fun i => halveBelow_pos hpos r i)
      (fun i => halveBelow_lt_one hlt r i)]

end

end ProbabilityTheory
