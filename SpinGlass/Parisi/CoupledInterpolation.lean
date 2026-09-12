/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.Parisi.CoupledScheme
import SpinGlass.Parisi.PairTreeFieldIndep

/-!
# The two-dimensional scheme of §14.6 with the external field (14.136)

Talagrand, Vol. II, §14.6, (14.130)–(14.139). On a cascade with `κ` levels over the sites
`Fin N × J`, the interpolating field `H` of (14.135) has per-level factors `L₀, L_p` and the
external field `H⁰` of (14.136) has factors `L₀', L'_p`, the two families using disjoint columns of
`J` (so that the fields are independent, `indepFun_pairTreeField_of_disjoint`); `H⁰` also carries a
deterministic per-site field `a` (Talagrand's `h_i`). When the covariances of `H` are the
increments of `ξ' ∘ ρ` (14.130) with `ρ_0 = 0` (14.131) and `ρ_{κ+1} = 1, u` (14.132), Lemma
14.6.1 integrated over `s` gives (14.139) before the evaluation of the endpoints
(`wFreeEnergy_coupledScheme_sub_le`):

`𝔼 F_w(H_N(σ¹) + H_N(σ²) + H⁰) - 𝔼 F_w(H + H⁰)
  ≤ ∫₀¹ 𝔼 [-θ(1) - θ(u) + (1/2) ∑_{ℓ,ℓ'} ⟨θ(ρ^{ℓ,ℓ'}_{(α,γ)+1})⟩_{H_s}] ds`,

the expectation on the right being over the joint sample of `H_N`, `H` and `H⁰`.
-/

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable section

variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]

/-- The deterministic external field `∑_ℓ ∑_i σ^ℓ_i a(i,ℓ)` on the pairs. -/
def pairFieldHam (N : ℕ) (A : Type*) [Fintype A] (a : Fin N × Fin 2 → ℝ) :
    FiniteGibbs.EnergySpace (PairConfig N A) :=
  WithLp.toLp 2 fun x => ∑ l : Fin 2, ∑ i, isingSpin (x.1 l i) * a (i, l)

variable (N) {κ : ℕ} {J : Type*} [Fintype J] [DecidableEq J]

/-- The model field `H_N(σ¹) + H_N(σ²)` on the product of the model law with the marks law. -/
def coupledModelField (M : ℕ) (ξ : ℝ → ℝ)
    (G₀ : GaussianField (α := Config N) Pm (fun σ τ => overlapCovMatrix N ξ σ τ))
    (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) :
    GaussianField (α := PairConfig N (TruncBranch κ M))
      (Pm.prod (siteMarksLaw (Fin N × J) κ v₀ vs)) (pairModelKernel N ξ) :=
  (pairModelFieldOverlap (A := TruncBranch κ M) ξ G₀).prodLeft (siteMarksLaw (Fin N × J) κ v₀ vs)

/-- A coupled marks field with factors `L₀, L`, on the product of the model law with the marks
law. -/
def coupledTreeField (M : ℕ) (Pm : Measure Ω) [IsProbabilityMeasure Pm] (v₀ : ℝ≥0)
    (vs : Fin κ → ℝ≥0) (L₀ : Fin 2 → J → ℝ) (L : Fin κ → Fin 2 → J → ℝ) :
    GaussianField (α := PairConfig N (TruncBranch κ M))
      (Pm.prod (siteMarksLaw (Fin N × J) κ v₀ vs)) (pairTreeFieldKernel N κ M v₀ vs L₀ L) :=
  (pairTreeField N κ M v₀ vs L₀ L).prodRight Pm

/-- The external field `H⁰` of (14.136): the coupled marks field with factors `L₀', L'` plus the
deterministic field `a`. -/
def coupledExtField (M : ℕ) (Pm : Measure Ω) [IsProbabilityMeasure Pm] (v₀ : ℝ≥0)
    (vs : Fin κ → ℝ≥0) (L₀' : Fin 2 → J → ℝ) (L' : Fin κ → Fin 2 → J → ℝ)
    (a : Fin N × Fin 2 → ℝ) (ω : Ω × SiteMarksSpace (Fin N × J) κ) :
    FiniteGibbs.EnergySpace (PairConfig N (TruncBranch κ M)) :=
  (coupledTreeField N M Pm v₀ vs L₀' L').U ω + pairFieldHam N (TruncBranch κ M) a

lemma measurable_coupledExtField (M : ℕ) (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) (L₀' : Fin 2 → J → ℝ)
    (L' : Fin κ → Fin 2 → J → ℝ) (a : Fin N × Fin 2 → ℝ) :
    Measurable (coupledExtField N M Pm v₀ vs L₀' L' a) :=
  (coupledTreeField N M Pm v₀ vs L₀' L').measU.add_const _

lemma integrable_coupledExtField (M : ℕ) (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) (L₀' : Fin 2 → J → ℝ)
    (L' : Fin κ → Fin 2 → J → ℝ) (a : Fin N × Fin 2 → ℝ) :
    Integrable (coupledExtField N M Pm v₀ vs L₀' L' a)
      (Pm.prod (siteMarksLaw (Fin N × J) κ v₀ vs)) :=
  (coupledTreeField N M Pm v₀ vs L₀' L').integrable.add (integrable_const _)

/-- **The pair of the model field and of the interpolating field is independent of the external
field** when the two families of factors use disjoint columns. -/
theorem indepFun_pair_coupledExtField (M : ℕ) (ξ : ℝ → ℝ)
    (G₀ : GaussianField (α := Config N) Pm (fun σ τ => overlapCovMatrix N ξ σ τ)) (v₀ : ℝ≥0)
    (vs : Fin κ → ℝ≥0) {J₁ : Finset J} {L₀ L₀' : Fin 2 → J → ℝ} {L L' : Fin κ → Fin 2 → J → ℝ}
    (hL0 : ∀ l j, j ∉ J₁ → L₀ l j = 0) (hL : ∀ p l j, j ∉ J₁ → L p l j = 0)
    (hL0' : ∀ l j, j ∈ J₁ → L₀' l j = 0) (hL' : ∀ p l j, j ∈ J₁ → L' p l j = 0)
    (a : Fin N × Fin 2 → ℝ) :
    pair (coupledModelField N M ξ G₀ v₀ vs) (coupledTreeField N M Pm v₀ vs L₀ L)
      ⟂ᵢ[Pm.prod (siteMarksLaw (Fin N × J) κ v₀ vs)] coupledExtField N M Pm v₀ vs L₀' L' a := by
  have hind := indepFun_pairTreeField_of_disjoint N κ M v₀ vs hL0 hL hL0' hL'
  have hlift := IndepFun.prodMk_fst_comp_snd Pm (pairTreeField N κ M v₀ vs L₀ L).measU
    (pairTreeField N κ M v₀ vs L₀' L').measU hind
  have hΨ : Measurable fun q : Ω × FiniteGibbs.EnergySpace (PairConfig N (TruncBranch κ M)) =>
      (WithLp.toLp 2 ((pairModelFieldOverlap (A := TruncBranch κ M) ξ G₀).U q.1, q.2) :
        PairSpace (PairConfig N (TruncBranch κ M))) :=
    measurable_toLp_prodMk
      ((pairModelFieldOverlap (A := TruncBranch κ M) ξ G₀).measU.comp measurable_fst)
      measurable_snd
  have hφ : Measurable fun V : FiniteGibbs.EnergySpace (PairConfig N (TruncBranch κ M)) =>
      V + pairFieldHam N (TruncBranch κ M) a := measurable_id.add_const _
  exact hlift.comp hΨ hφ

/-- **Lemma 14.6.1 for the two-dimensional scheme with the external field (14.136)**
(Talagrand's (14.139) before the evaluation of the endpoints): with the interpolating field of
(14.135) whose covariances are the increments of `ξ' ∘ ρ` and the external field `H⁰`, for
weights carrying the constraint `R_{1,2} = u`,

`𝔼 F_w(H_N(σ¹) + H_N(σ²) + H⁰) - 𝔼 F_w(H + H⁰)
  ≤ ∫₀¹ 𝔼 [(1/2) c₀ + (1/2) ∑_{ℓ,ℓ'} ⟨θ(ρ^{ℓ,ℓ'}_{(α,γ)+1})⟩_{H_s}] ds`,

with the diagonal constant `c₀ = pairDiagConst ξ u (ρ_{κ+1})`, which is `-2θ(1) - 2θ(u)` under
Talagrand's (14.132) `ρ^{ℓ,ℓ}_{κ+1} = 1`, `ρ^{1,2}_{κ+1} = u`. -/
theorem wFreeEnergy_coupledScheme_sub_le (M : ℕ) (hN : 0 < N) (ξ : ℝ → ℝ)
    (ρ : Fin 2 → Fin 2 → ℕ → ℝ) (u : ℝ) (hρ0 : ∀ l l', ρ l l' 0 = 0)
    {S : Set ℝ} (hρS : ∀ l l' r, ρ l l' r ∈ S)
    (htan : ∀ x ∈ Icc (-1 : ℝ) 1, ∀ q ∈ S, ξ q + (x - q) * deriv ξ q ≤ ξ x) (h0 : deriv ξ 0 = 0)
    (G₀ : GaussianField (α := Config N) Pm (fun σ τ => overlapCovMatrix N ξ σ τ))
    (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) {J₁ : Finset J} {L₀ L₀' : Fin 2 → J → ℝ}
    {L L' : Fin κ → Fin 2 → J → ℝ}
    (hC0 : ∀ l l', (v₀ : ℝ) * gram L₀ l l' = deriv ξ (ρ l l' 1) - deriv ξ (ρ l l' 0))
    (hC : ∀ (p : Fin κ) l l', (vs p : ℝ) * gram (L p) l l'
      = deriv ξ (ρ l l' (p.val + 2)) - deriv ξ (ρ l l' (p.val + 1)))
    (hL0 : ∀ l j, j ∉ J₁ → L₀ l j = 0) (hL : ∀ p l j, j ∉ J₁ → L p l j = 0)
    (hL0' : ∀ l j, j ∈ J₁ → L₀' l j = 0) (hL' : ∀ p l j, j ∈ J₁ → L' p l j = 0)
    (a : Fin N × Fin 2 → ℝ) (wt : PairConfig N (TruncBranch κ M) → ℝ) (hwt : ∀ x, 0 ≤ wt x)
    (hne : ∃ x, wt x ≠ 0) (hu : ∀ x, wt x ≠ 0 → overlap N (x.1 0) (x.1 1) = u) :
    (∫ ω, wFreeEnergy wt N ((coupledModelField N M ξ G₀ v₀ vs).U ω
          + coupledExtField N M Pm v₀ vs L₀' L' a ω) ∂Pm.prod (siteMarksLaw (Fin N × J) κ v₀ vs))
        - (∫ ω, wFreeEnergy wt N ((coupledTreeField N M Pm v₀ vs L₀ L).U ω
          + coupledExtField N M Pm v₀ vs L₀' L' a ω) ∂Pm.prod (siteMarksLaw (Fin N × J) κ v₀ vs))
      ≤ ∫ t in (0 : ℝ)..1, ∫ ω, treeBoundIntegrand wt
          (pairDiagConst ξ u fun l l' => ρ l l' (κ + 1))
          (fun x y => ∑ l : Fin 2, ∑ l' : Fin 2, parisiTheta ξ (ρ l l' (branchLevel x.2 y.2 + 1)))
          (gaussianInterp t (pair (coupledModelField N M ξ G₀ v₀ vs)
            (coupledTreeField N M Pm v₀ vs L₀ L) ω) + coupledExtField N M Pm v₀ vs L₀' L' a ω)
          ∂Pm.prod (siteMarksLaw (Fin N × J) κ v₀ vs) := by
  refine wFreeEnergy_sub_le_of_le_treeBoundIntegrand_indep' (coupledModelField N M ξ G₀ v₀ vs)
    (coupledTreeField N M Pm v₀ vs L₀ L) (GaussianField.prodLeft_indepFun_prodRight _ _) wt hwt
    hne N (measurable_coupledExtField N M v₀ vs L₀' L' a)
    (integrable_coupledExtField N M v₀ vs L₀' L' a)
    (indepFun_pair_coupledExtField N M ξ G₀ v₀ vs hL0 hL hL0' hL' a) _ _ fun H => ?_
  have hK₂ := pairTreeFieldKernel_eq_pairTreeKernel N κ M hN ξ ρ v₀ vs L₀ L hρ0 h0 hC0 hC
  change wGuerraTrace wt (pairModelKernel N ξ) (pairTreeFieldKernel N κ M v₀ vs L₀ L) N H ≤ _
  rw [hK₂]
  exact (wGuerraTrace_pair_le hN ξ (fun α γ l l' => ρ l l' (branchLevel α γ + 1)) u
    (fun l l' => ρ l l' (κ + 1)) (fun α l l' => by rw [branchLevel_self]) (S := S)
    (fun _ _ l l' => hρS l l' _) htan wt hwt hne hu H).trans (le_of_eq rfl)

end

end SpinGlass
