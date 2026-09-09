/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.MixedPSpinThermodynamicLimit
import SpinGlass.FiniteGibbs.PointwiseFluctuation
import SpinGlass.MixedPSpinLimit
import SpinGlass.MixedPSpinGhirlandaGuerra
import SpinGlass.MixedPSpinComponent
import SpinGlass.MultiComponent
import Common.Mathlib.Probability.Distributions.Gaussian.MultivariateSum

/-!
# Ghirlanda–Guerra identities at almost every temperature, without perturbation

Talagrand, *Mean Field Models for Spin Glasses*, Vol. II, Theorem 12.1.3 (Panchenko) and the
second half of Theorem 12.1.10, for an even mixed `p`-spin model with external field.

Along the temperature path `β ↦ H_field + β H`, the mean free energy `p_N(β)` is convex and
converges (Guerra–Toninelli, `MixedPSpinThermodynamicLimit`) to a convex limit `𝒫(β)`, which is
differentiable off a countable set. At every `β` where `𝒫` is differentiable, Theorem 12.1.3
gives energy self-averaging `𝔼⟨|H/N - 𝔼⟨H⟩/N|⟩_β → 0` **at that `β`** — no window average, no
perturbation — and therefore the Ghirlanda–Guerra defect of the model's own profile `ξ` vanishes
at `β` (Theorem 12.1.10 with `lim δ = 0`, for `β ≠ 0`). Every subsequential limit of the overlap
array laws at such a `β` satisfies the identity (15.40) for `ξ`.

## Main statements

- `SpinGlass.mixedPSpinPathFreeEnergy`, `SpinGlass.mixedPSpinPathLimit`: `p_N(β)` and `𝒫(β)`.
- `SpinGlass.tendsto_mixedPSpinTotalFluct_of_differentiableAt`: **Theorem 12.1.3**.
- `SpinGlass.ae_tendsto_mixedPSpinTotalFluct`: energy self-averaging at almost every `β`.
- `SpinGlass.abs_ggDefect_mixedPSpin_le`: the finite-volume defect of the model's own profile is
  bounded by `‖g‖ 𝔼⟨|H/N - 𝔼⟨H⟩/N|⟩/(n|β|)`, with the external field.
- `SpinGlass.tendsto_ggDefect_mixedPSpin_of_differentiableAt`,
  `SpinGlass.ae_tendsto_ggDefect_mixedPSpin`: **Theorem 12.1.10, second half**.
- `SpinGlass.ggDefect_eq_zero_of_tendsto_mixedPSpin`: the identity for every limit law.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology Set

namespace SpinGlass

noncomputable section

variable {N : ℕ}

/-! ### Scaled profiles -/

lemma overlapCovMatrix_smul (N : ℕ) (ξ : ℝ → ℝ) (c : ℝ) :
    overlapCovMatrix N (fun r => c * ξ r) = c • overlapCovMatrix N ξ := by
  ext σ τ
  simp only [overlapCovMatrix_apply, Matrix.smul_apply, smul_eq_mul]
  ring

section Polynomial

variable {P : Polynomial ℝ}

lemma convexOn_sq_mul_eval (hP : ∀ k, 0 ≤ P.coeff k) (hodd : ∀ k, Odd k → P.coeff k = 0)
    (β : ℝ) : ConvexOn ℝ (Icc (-1 : ℝ) 1) fun r => β ^ 2 * P.eval r :=
  ((convexOn_eval_of_even_coeff hP hodd).smul (sq_nonneg β)).subset (subset_univ _)
    (convex_Icc _ _)

lemma posSemidef_overlapCovMatrix_sq_mul (hP : ∀ k, 0 ≤ P.coeff k) (β : ℝ) (N : ℕ) :
    (overlapCovMatrix N fun r => β ^ 2 * P.eval r).PosSemidef := by
  rw [overlapCovMatrix_smul]
  exact (posSemidef_overlapCovMatrix_of_polynomial N hP).smul_sq β

/-! ### The temperature path -/

/-- **The free energy along the temperature path** `β ↦ H_field + β H` of the mixed `p`-spin
model with profile `P`: `p_N(β) = 𝔼 F_N(H_field + β H)`, `H ~ gaussField (N ξ(R))`. -/
def mixedPSpinPathFreeEnergy (N : ℕ) (P : Polynomial ℝ) (h β : ℝ) : ℝ :=
  ∫ H : EnergySpace N, free_energy_density (N := N) (H_field N h + β • H)
    ∂(gaussField N (overlapCovMatrix N fun r => P.eval r))

/-- `p_N(β)` is the free energy of the model with profile `β² ξ`. -/
lemma mixedPSpinPathFreeEnergy_eq (hP : ∀ k, 0 ≤ P.coeff k) (N : ℕ) (h β : ℝ) :
    mixedPSpinPathFreeEnergy N P h β = mixedPSpinFreeEnergy N (fun r => β ^ 2 * P.eval r) h := by
  unfold mixedPSpinPathFreeEnergy mixedPSpinFreeEnergy
  rw [overlapCovMatrix_smul,
    gaussFreeEnergy_eq_integral_smul (posSemidef_overlapCovMatrix_of_polynomial N hP) β h]

/-- **The limiting free energy along the temperature path**, `𝒫(β) = lim_N p_N(β)`, for an even
mixed `p`-spin model. -/
def mixedPSpinPathLimit (hP : ∀ k, 0 ≤ P.coeff k) (hodd : ∀ k, Odd k → P.coeff k = 0)
    (h β : ℝ) : ℝ :=
  mixedPSpinFreeEnergyLimit (convexOn_sq_mul_eval hP hodd β)
    (posSemidef_overlapCovMatrix_sq_mul hP β) h

theorem tendsto_mixedPSpinPathFreeEnergy (hP : ∀ k, 0 ≤ P.coeff k)
    (hodd : ∀ k, Odd k → P.coeff k = 0) (h β : ℝ) :
    Tendsto (fun N : ℕ => mixedPSpinPathFreeEnergy N P h β) atTop
      (𝓝 (mixedPSpinPathLimit hP hodd h β)) :=
  (tendsto_mixedPSpinFreeEnergy (convexOn_sq_mul_eval hP hodd β)
    (posSemidef_overlapCovMatrix_sq_mul hP β) h).congr
    fun N => (mixedPSpinPathFreeEnergy_eq hP N h β).symm

/-- `p_N` is convex in the inverse temperature. -/
theorem convexOn_mixedPSpinPathFreeEnergy (N : ℕ) (P : Polynomial ℝ) (h : ℝ) :
    ConvexOn ℝ (univ : Set ℝ) (mixedPSpinPathFreeEnergy N P h) :=
  FiniteGibbs.convexOn_integral_free_energy_density (α := Config N)
    (P := gaussField N (overlapCovMatrix N fun r => P.eval r)) (U := fun _ => H_field N h)
    (V := fun H => H) N measurable_const measurable_id (integrable_const _)
    (integrable_norm_gaussField N _)

/-- `p_N'(β) = -𝔼⟨H⟩_β/N`. -/
theorem hasDerivAt_mixedPSpinPathFreeEnergy (N : ℕ) (P : Polynomial ℝ) (h β : ℝ) :
    HasDerivAt (mixedPSpinPathFreeEnergy N P h)
      (∫ H : EnergySpace N, -(1 / (N : ℝ)) *
          FiniteGibbs.gibbs_average (α := Config N) (H_field N h + β • H) H
          ∂(gaussField N (overlapCovMatrix N fun r => P.eval r))) β :=
  FiniteGibbs.hasDerivAt_integral_free_energy_density (α := Config N)
    (P := gaussField N (overlapCovMatrix N fun r => P.eval r)) (U := fun _ => H_field N h)
    (V := fun H => H) measurable_const measurable_id (integrable_const _)
    (integrable_norm_gaussField N _) N β

/-- **`𝒫` is convex**: convexity survives the thermodynamic limit. -/
theorem convexOn_mixedPSpinPathLimit (hP : ∀ k, 0 ≤ P.coeff k)
    (hodd : ∀ k, Odd k → P.coeff k = 0) (h : ℝ) :
    ConvexOn ℝ (univ : Set ℝ) (mixedPSpinPathLimit hP hodd h) := by
  refine ⟨convex_univ, fun s _ t _ a b ha hb hab => ?_⟩
  refine le_of_tendsto_of_tendsto (tendsto_mixedPSpinPathFreeEnergy hP hodd h (a * s + b * t))
    (((tendsto_mixedPSpinPathFreeEnergy hP hodd h s).const_mul a).add
      ((tendsto_mixedPSpinPathFreeEnergy hP hodd h t).const_mul b)) ?_
  filter_upwards with N
  simpa [smul_eq_mul] using
    (convexOn_mixedPSpinPathFreeEnergy N P h).2 (mem_univ s) (mem_univ t) ha hb hab

/-- **`𝒫` is differentiable off a countable set of inverse temperatures.** -/
theorem countable_setOf_not_differentiableAt_mixedPSpinPathLimit (hP : ∀ k, 0 ≤ P.coeff k)
    (hodd : ∀ k, Odd k → P.coeff k = 0) (h : ℝ) :
    {β : ℝ | ¬ DifferentiableAt ℝ (mixedPSpinPathLimit hP hodd h) β}.Countable := by
  refine Set.Countable.mono ?_
    (convexOn_mixedPSpinPathLimit hP hodd h).countable_setOf_not_differentiableAt
  exact fun β hβ => ⟨by simp, hβ⟩

/-! ### Theorem 12.1.3: energy self-averaging at a fixed temperature -/

/-- **The total energy fluctuation** `𝔼⟨|H/N - 𝔼⟨H⟩/N|⟩_β` of the mixed `p`-spin model at inverse
temperature `β` and field `h`. -/
def mixedPSpinTotalFluct (N : ℕ) (P : Polynomial ℝ) (h β : ℝ) : ℝ :=
  ∫ H : EnergySpace N, FiniteGibbs.gibbs_average (α := Config N) (H_field N h + β • H)
    (fun σ => |(1 / (N : ℝ)) * H σ - ∫ H' : EnergySpace N, (1 / (N : ℝ)) *
        FiniteGibbs.gibbs_average (α := Config N) (H_field N h + β • H') H'
        ∂(gaussField N (overlapCovMatrix N fun r => P.eval r))|)
    ∂(gaussField N (overlapCovMatrix N fun r => P.eval r))

lemma mixedPSpinTotalFluct_nonneg (N : ℕ) (P : Polynomial ℝ) (h β : ℝ) :
    0 ≤ mixedPSpinTotalFluct N P h β :=
  integral_nonneg fun _ => Finset.sum_nonneg fun σ _ =>
    mul_nonneg (FiniteGibbs.gibbs_pmf_nonneg (α := Config N) _ σ) (abs_nonneg _)

/-- **Talagrand Vol. II, Theorem 12.1.3 (Panchenko), for an even mixed `p`-spin model.** At every
inverse temperature `β` where the limiting free energy `𝒫` is differentiable, the energy
self-averages: `𝔼⟨|H/N - 𝔼⟨H⟩/N|⟩_β → 0`. No average over `β` is taken. -/
theorem tendsto_mixedPSpinTotalFluct_of_differentiableAt (hP : ∀ k, 0 ≤ P.coeff k)
    (hodd : ∀ k, Odd k → P.coeff k = 0) (h : ℝ) {β : ℝ}
    (hβ : DifferentiableAt ℝ (mixedPSpinPathLimit hP hodd h) β) :
    Tendsto (fun N : ℕ => mixedPSpinTotalFluct N P h β) atTop (𝓝 0) := by
  classical
  refine FiniteGibbs.tendsto_zero_of_le_window (T := fun N => mixedPSpinTotalFluct N P h β)
    (D := fun N b =>
      (∫ H : EnergySpace N, -(1 / (N : ℝ)) *
          FiniteGibbs.gibbs_average (α := Config N) (H_field N h + (β + b) • H) H
          ∂(gaussField N (overlapCovMatrix N fun r => P.eval r)))
        - ∫ H : EnergySpace N, -(1 / (N : ℝ)) *
            FiniteGibbs.gibbs_average (α := Config N) (H_field N h + (β - b) • H) H
            ∂(gaussField N (overlapCovMatrix N fun r => P.eval r)))
    (C := fun N b => (|β| + b) * (Real.sqrt (P.eval 1) / Real.sqrt (N : ℝ)))
    (n := fun N => (N : ℝ)) (fun N => mixedPSpinTotalFluct_nonneg N P h β)
    tendsto_natCast_atTop_atTop ?_ ?_ ?_
  · -- the window bound at finite volume
    filter_upwards [eventually_ne_atTop 0] with N hN
    intro b hb η hη
    have hC : ∀ y ∈ Icc (β - b) (β + b),
        (∫ H : EnergySpace N, |free_energy_density (N := N) (H_field N h + y • H)
            - ∫ H' : EnergySpace N, free_energy_density (N := N) (H_field N h + y • H')
                ∂(gaussField N (overlapCovMatrix N fun r => P.eval r))|
            ∂(gaussField N (overlapCovMatrix N fun r => P.eval r)))
          ≤ (|β| + b) * (Real.sqrt (P.eval 1) / Real.sqrt (N : ℝ)) := by
      intro y hy
      refine (integral_abs_mixedPSpinFreeEnergy_sub_mean_le hP hN h y).trans ?_
      have hy' : |y| ≤ |β| + b := by
        rw [abs_le]
        constructor <;> linarith [hy.1, hy.2, le_abs_self β, neg_abs_le β]
      exact mul_le_mul_of_nonneg_right hy' (by positivity)
    exact FiniteGibbs.integral_totalFluct_le_window (α := Config N)
      (P := gaussField N (overlapCovMatrix N fun r => P.eval r)) (U := fun _ => H_field N h)
      (V := fun H => H) measurable_const measurable_id (integrable_const _)
      (integrable_norm_gaussField N _) (integrable_norm_sq_gaussField N _) N β hb hη hC
  · -- Lemma 12.1.9
    intro ε hε
    obtain ⟨b, hb, hev⟩ := ConvexOn.exists_eventually_deriv_sub_deriv_le (L := atTop)
      (θ := fun N => mixedPSpinPathFreeEnergy N P h) (p := mixedPSpinPathLimit hP hodd h)
      (x := β) (fun N => convexOn_mixedPSpinPathFreeEnergy N P h)
      (fun y => tendsto_mixedPSpinPathFreeEnergy hP hodd h y)
      (fun N y => (hasDerivAt_mixedPSpinPathFreeEnergy N P h y).differentiableAt) hβ hε
    refine ⟨b, hb, ?_⟩
    filter_upwards [hev] with N hN
    rwa [(hasDerivAt_mixedPSpinPathFreeEnergy N P h (β + b)).deriv,
      (hasDerivAt_mixedPSpinPathFreeEnergy N P h (β - b)).deriv] at hN
  · -- the concentration constants vanish
    intro b hb
    have h0 : 0 ≤ P.eval 1 :=
      le_trans (abs_nonneg _) (abs_polynomial_profile_le hP 1 (by simp))
    have h1 : Tendsto (fun N : ℕ => Real.sqrt (P.eval 1) / Real.sqrt (N : ℝ)) atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp
        (tendsto_const_div_atTop_nhds_zero_nat (P.eval 1))
      rw [Real.sqrt_zero] at this
      refine this.congr fun N => ?_
      simp only [Function.comp_apply]
      exact Real.sqrt_div h0 _
    simpa using h1.const_mul (|β| + b)

/-- **Energy self-averaging at almost every inverse temperature**, for every even mixed `p`-spin
model with external field. Talagrand Vol. II, Theorem 12.1.3. -/
theorem ae_tendsto_mixedPSpinTotalFluct (hP : ∀ k, 0 ≤ P.coeff k)
    (hodd : ∀ k, Odd k → P.coeff k = 0) (h : ℝ) :
    ∀ᵐ β : ℝ, Tendsto (fun N : ℕ => mixedPSpinTotalFluct N P h β) atTop (𝓝 0) := by
  have hcount : {β : ℝ | ¬ Tendsto (fun N : ℕ => mixedPSpinTotalFluct N P h β) atTop
      (𝓝 0)}.Countable := by
    refine Set.Countable.mono ?_
      (countable_setOf_not_differentiableAt_mixedPSpinPathLimit hP hodd h)
    exact fun β hβ hd => hβ (tendsto_mixedPSpinTotalFluct_of_differentiableAt hP hodd h hd)
  have := hcount.measure_zero (μ := (volume : Measure ℝ))
  rwa [MeasureTheory.ae_iff]

/-! ### Theorem 12.1.10, second half: the Ghirlanda–Guerra defect at a fixed temperature -/

/-- **The zero disorder**: the Hamiltonian `0`, a centered Gaussian disorder with kernel `0`. -/
def GaussianDisorder.zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (N : ℕ) :
    GaussianDisorder (Ω := Ω) (N := N) P
      (fun σ τ => (0 : Matrix (Config N) (Config N) ℝ) σ τ) :=
  GaussianDisorder.ofMap (U := fun _ => (0 : EnergySpace N)) measurable_const
    Matrix.PosSemidef.zero (by
      rw [Measure.map_const, measure_univ, one_smul, gaussField, multivariateGaussian_zero])

/-- **The Ghirlanda–Guerra defect of the model's own profile is bounded by the energy fluctuation
at the same temperature**, with the external field: for `β ≠ 0` and every continuous test `g` of
the `n × n` overlap block,

`|defect_N(β)| ≤ ‖g‖ 𝔼⟨|H/N - 𝔼⟨H⟩/N|⟩_β / (n |β|)`.

The Hamiltonian `H_field + β H` is the affine image `(0, H) ↦ 0 + β H + H_field` of the disorder
pair `(0, H)`, so `abs_ghirlandaGuerraCombinationOf_component_le` applies with the zero disorder
in the first slot. Talagrand Vol. II, §12.2. -/
theorem abs_ggDefect_mixedPSpin_le (hP : ∀ k, 0 ≤ P.coeff k) (hN : N ≠ 0) (h : ℝ) {β : ℝ}
    (hβ : β ≠ 0) {n : ℕ} (hn : 0 < n) (g : C(Fin n → Fin n → OverlapValue, ℝ)) :
    |ggDefect (mixedPSpinArrayLaw N (fun r => β ^ 2 * P.eval r) h) n (overlapProfileCM P) g|
      ≤ ‖g‖ * mixedPSpinTotalFluct N P h β / ((n : ℝ) * |β|) := by
  classical
  have hS : (overlapCovMatrix N fun r => P.eval r).PosSemidef :=
    posSemidef_overlapCovMatrix_of_polynomial N hP
  let _ : MeasureSpace (EnergySpace N) := ⟨gaussField N (overlapCovMatrix N fun r => P.eval r)⟩
  have : IsProbabilityMeasure (ℙ : Measure (EnergySpace N)) :=
    isProbabilityMeasure_gaussField N _
  let G₁ : GaussianDisorder (Ω := EnergySpace N) (N := N) ℙ
      (fun σ τ => (0 : Matrix (Config N) (Config N) ℝ) σ τ) := GaussianDisorder.zero ℙ N
  let G₂ : GaussianDisorder (Ω := EnergySpace N) (N := N) ℙ
      (fun σ τ => (overlapCovMatrix N fun r => P.eval r) σ τ) :=
    GaussianDisorder.ofMap (U := id) measurable_id hS Measure.map_id
  have hU₁ : G₁.U = fun _ => (0 : EnergySpace N) := rfl
  have hU₂ : G₂.U = id := rfl
  have hindep : G₁.U ⟂ᵢ[(ℙ : Measure (EnergySpace N))] G₂.U := by
    rw [hU₁]; exact indepFun_const_left _ _
  have hdiag : ∀ σ : Config N, (overlapCovMatrix N fun r => P.eval r) σ σ = (N : ℝ) * P.eval 1 :=
    fun σ => overlapCovMatrix_diag N _ σ
  have hcomb := abs_ghirlandaGuerraCombinationOf_component_le (Ω := EnergySpace N) (N := N)
    G₁ G₂ hindep hN β (H_field N h) hdiag n (overlapReplicaFun N g) ⟨0, hn⟩
    (abs_overlapReplicaFun_le N g)
  rw [integral_disorderPairLaw_totalFluct (Ω := EnergySpace N) (N := N) G₁ G₂ (H_field N h) β]
    at hcomb
  simp only [hU₁, hU₂, id_eq, zero_add] at hcomb
  change _ ≤ ‖g‖ * ((N : ℝ) * mixedPSpinTotalFluct N P h β) at hcomb
  have hNR : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hκ : β * (N : ℝ) ≠ 0 := mul_ne_zero hβ hNR.ne'
  have hcov : ∀ σ τ : Config N,
      FiniteGibbs.crossKernel (disorderPairLaw (Ω := EnergySpace N) (N := N) G₁ G₂)
          (pairAffine N β) (std_basis_right (N := N)) σ τ
        = (β * (N : ℝ)) * overlapProfileCM P (overlapUnit N σ τ) := by
    intro σ τ
    rw [crossKernel_pairAffine_std_basis_right (Ω := EnergySpace N) (N := N) G₁ G₂ hindep β σ τ]
    simp only [overlapCovMatrix_apply, overlapProfileCM_apply, overlapUnit_coe]
    ring
  have : IsProbabilityMeasure (disorderPairLaw (Ω := EnergySpace N) (N := N) G₁ G₂) :=
    Measure.isProbabilityMeasure_map
      (measurable_disorderPair (Ω := EnergySpace N) (N := N) G₁ G₂).aemeasurable
  have : IsProbabilityMeasure ((disorderPairLaw (Ω := EnergySpace N) (N := N) G₁ G₂).map
      (fun p => pairAffine N β p + H_field N h)) :=
    Measure.isProbabilityMeasure_map
      ((pairAffine N β).continuous.measurable.add_const _).aemeasurable
  have hdef := abs_ghirlandaGuerra_defect_of_le hn
    ((disorderPairLaw (Ω := EnergySpace N) (N := N) G₁ G₂).map
      (fun p => pairAffine N β p + H_field N h)) hκ (overlapProfileCM P) hcov g hcomb
  have hν : (disorderPairLaw (Ω := EnergySpace N) (N := N) G₁ G₂).map
        (fun p => pairAffine N β p + H_field N h)
      = (gaussField N (overlapCovMatrix N fun r => β ^ 2 * P.eval r)).map
          (fun H : EnergySpace N => H + H_field N h) := by
    rw [overlapCovMatrix_smul, ← gaussField_map_smul hS β, disorderPairLaw,
      Measure.map_map ((pairAffine N β).continuous.measurable.add_const _)
        (measurable_disorderPair (Ω := EnergySpace N) (N := N) G₁ G₂),
      Measure.map_map (measurable_add_const _) (measurable_const_smul β)]
    congr 1
    funext ω
    simp [Function.comp, disorderPair, hU₁, hU₂, pairAffine_apply]
  rw [hν] at hdef
  have hβ' : (0 : ℝ) < |β| := abs_pos.2 hβ
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  calc |ggDefect (mixedPSpinArrayLaw N (fun r => β ^ 2 * P.eval r) h) n (overlapProfileCM P) g|
      ≤ ‖g‖ * ((N : ℝ) * mixedPSpinTotalFluct N P h β) / ((n : ℝ) * |β * (N : ℝ)|) := hdef
    _ = ‖g‖ * mixedPSpinTotalFluct N P h β / ((n : ℝ) * |β|) := by
        rw [abs_mul, abs_of_pos hNR, div_eq_div_iff (by positivity) (by positivity)]
        ring

/-- **Talagrand Vol. II, Theorem 12.1.10, second half.** For an even mixed `p`-spin model with
external field, at every `β ≠ 0` where the limiting free energy is differentiable, the
Ghirlanda–Guerra defect of the model's own profile vanishes as `N → ∞`, for every `n` and every
continuous test function of the `n × n` overlap block. No perturbation, no window average. -/
theorem tendsto_ggDefect_mixedPSpin_of_differentiableAt (hP : ∀ k, 0 ≤ P.coeff k)
    (hodd : ∀ k, Odd k → P.coeff k = 0) (h : ℝ) {β : ℝ} (hβ0 : β ≠ 0)
    (hβ : DifferentiableAt ℝ (mixedPSpinPathLimit hP hodd h) β) {n : ℕ} (hn : 0 < n)
    (g : C(Fin n → Fin n → OverlapValue, ℝ)) :
    Tendsto (fun N : ℕ =>
        ggDefect (mixedPSpinArrayLaw N (fun r => β ^ 2 * P.eval r) h) n (overlapProfileCM P) g)
      atTop (𝓝 0) := by
  have hT := tendsto_mixedPSpinTotalFluct_of_differentiableAt hP hodd h hβ
  have hlim : Tendsto (fun N : ℕ => ‖g‖ * mixedPSpinTotalFluct N P h β / ((n : ℝ) * |β|))
      atTop (𝓝 0) := by
    simpa using (hT.const_mul ‖g‖).div_const ((n : ℝ) * |β|)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ne_atTop 0] with N hN
  exact abs_ggDefect_mixedPSpin_le hP hN h hβ0 hn g

/-- **The Ghirlanda–Guerra identity of the model's own profile holds asymptotically at almost every
inverse temperature**, for every even mixed `p`-spin model with external field.
Talagrand Vol. II, Theorem 12.1.10. -/
theorem ae_tendsto_ggDefect_mixedPSpin (hP : ∀ k, 0 ≤ P.coeff k)
    (hodd : ∀ k, Odd k → P.coeff k = 0) (h : ℝ) {n : ℕ} (hn : 0 < n)
    (g : C(Fin n → Fin n → OverlapValue, ℝ)) :
    ∀ᵐ β : ℝ, Tendsto (fun N : ℕ =>
        ggDefect (mixedPSpinArrayLaw N (fun r => β ^ 2 * P.eval r) h) n (overlapProfileCM P) g)
      atTop (𝓝 0) := by
  have hcount : {β : ℝ | ¬ Tendsto (fun N : ℕ =>
      ggDefect (mixedPSpinArrayLaw N (fun r => β ^ 2 * P.eval r) h) n (overlapProfileCM P) g)
      atTop (𝓝 0)}.Countable := by
    refine Set.Countable.mono ?_
      ((countable_setOf_not_differentiableAt_mixedPSpinPathLimit hP hodd h).union
        (Set.countable_singleton (0 : ℝ)))
    intro β hβ
    by_contra hmem
    rw [Set.mem_union, not_or, Set.mem_ofPred_eq, not_not, Set.mem_singleton_iff] at hmem
    exact hβ (tendsto_ggDefect_mixedPSpin_of_differentiableAt hP hodd h hmem.2 hmem.1 hn g)
  have := hcount.measure_zero (μ := (volume : Measure ℝ))
  rwa [MeasureTheory.ae_iff]

/-- **Every limit law satisfies the identity for the model's own profile.** If a subsequence of
the overlap array laws at a differentiability point `β ≠ 0` converges in distribution to `μ`,
then `μ` satisfies Talagrand's identity (15.40) for `ξ` and every test function. -/
theorem ggDefect_eq_zero_of_tendsto_mixedPSpin (hP : ∀ k, 0 ≤ P.coeff k)
    (hodd : ∀ k, Odd k → P.coeff k = 0) (h : ℝ) {β : ℝ} (hβ0 : β ≠ 0)
    (hβ : DifferentiableAt ℝ (mixedPSpinPathLimit hP hodd h) β)
    {μ : ProbabilityMeasure (ℕ → ℕ → OverlapValue)} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hlim : Tendsto (fun k => mixedPSpinArray (φ k) (fun r => β ^ 2 * P.eval r) h) atTop (𝓝 μ))
    {n : ℕ} (hn : 0 < n) (g : C(Fin n → Fin n → OverlapValue, ℝ)) :
    ggDefect (μ : Measure (ℕ → ℕ → OverlapValue)) n (overlapProfileCM P) g = 0 :=
  tendsto_nhds_unique (((continuous_ggDefect n (overlapProfileCM P) g).tendsto μ).comp hlim)
    ((tendsto_ggDefect_mixedPSpin_of_differentiableAt hP hodd h hβ0 hβ hn g).comp
      hφ.tendsto_atTop)

end Polynomial

end

end SpinGlass
