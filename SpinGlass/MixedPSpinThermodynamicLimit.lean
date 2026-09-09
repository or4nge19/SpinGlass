/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.GuerraToninelli
import SpinGlass.ThermodynamicLimit
import SpinGlass.GaussianPerturbation

/-!
# The thermodynamic limit of a mixed `p`-spin model with a convex profile

Talagrand Vol. I, Theorem 1.3.9 (Guerra–Toninelli), for every mean-field model whose covariance is
overlap-driven, `𝔼 H(σ) H(τ) = N ξ(R_{στ})`, with a profile `ξ` convex on `[-1,1]` (Vol. II, §12.1).

The free energy `p_N = mixedPSpinFreeEnergy N ξ h` is a function of the covariance alone
(`gaussFreeEnergy`). Guerra–Toninelli superadditivity `N₁ p_{N₁} + N₂ p_{N₂} ≤ (N₁+N₂) p_{N₁+N₂}`
follows from the general kernel comparison `mul_integral_free_energy_density_add_le_of_kernel_le`:
the whole-system kernel `N ξ(R)` is dominated by the non-interacting split kernel by Jensen's
inequality (`overlapCovKernel_le_splitCovKernel`) and agrees with it on the diagonal. The annealed
bound `p_N ≤ log 2 + |h| + ξ(1)/2` supplies the `BddAbove` hypothesis of Fekete's lemma, which
produces the limit and identifies it with the supremum.

The SK model is the profile `β² r²/2`; `skFreeEnergy_eq_mixedPSpinFreeEnergy` is `rfl` and
`skFreeEnergyLimit_eq_mixedPSpinFreeEnergyLimit` identifies the two limits. An even mixed `p`-spin
model — nonnegative coefficients, only even powers — has a convex profile on all of `ℝ`
(`convexOn_eval_of_even_coeff`), hence a thermodynamic limit.

Finally, Lemma 12.2.1 (`abs_gaussFreeEnergy_perturbedProfile_sub_le`) shows that the
Ghirlanda–Guerra perturbation of the capstone `MixedPSpinLimit` does not change the free-energy
limit, both for arbitrary vanishing weights and for the explicit scaling `β_s N^{-1/16}`.

## Main statements

- `SpinGlass.mixedPSpinFreeEnergy`: `p_N(ξ, h)`.
- `SpinGlass.mul_mixedPSpinFreeEnergy_add_le`: **Guerra–Toninelli superadditivity.**
- `SpinGlass.mixedPSpinFreeEnergy_le`: `p_N ≤ log 2 + |h| + ξ(1)/2`.
- `SpinGlass.mixedPSpinFreeEnergyLimit`, `SpinGlass.tendsto_mixedPSpinFreeEnergy`,
  `SpinGlass.mixedPSpinFreeEnergy_le_limit`: **the thermodynamic limit exists** and is the
  supremum.
- `SpinGlass.tendsto_mixedPSpinFreeEnergy_of_polynomial`: every even mixed `p`-spin model has a
  thermodynamic limit.
- `SpinGlass.tendsto_mixedPSpinFreeEnergy_perturbedProfile`,
  `SpinGlass.tendsto_mixedPSpinFreeEnergy_perturbedProfile_explicit`: the perturbed models of the
  Ghirlanda–Guerra capstone have the same free-energy limit.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology Set

namespace SpinGlass

noncomputable section

variable {N : ℕ}

/-! ### The free energy of a mixed `p`-spin model -/

/-- **The mixed `p`-spin free energy at size `N`**, profile `ξ` and external field `h`: the free
energy of the centered Gaussian disorder with covariance `N ξ(R)`. Talagrand Vol. II, §12.1. -/
def mixedPSpinFreeEnergy (N : ℕ) (ξ : ℝ → ℝ) (h : ℝ) : ℝ :=
  gaussFreeEnergy N (overlapCovMatrix N ξ) h

/-- The SK free energy is the mixed `p`-spin free energy at the profile `β² r²/2`. -/
lemma skFreeEnergy_eq_mixedPSpinFreeEnergy (N : ℕ) (β h : ℝ) :
    skFreeEnergy N β h = mixedPSpinFreeEnergy N (skCovXi β) h := rfl

/-! ### Guerra–Toninelli superadditivity -/

/-- **Guerra–Toninelli superadditivity for a mixed `p`-spin model.** For a profile `ξ` convex on
`[-1,1]` whose overlap-driven kernels are covariances,
`N₁ p_{N₁} + N₂ p_{N₂} ≤ (N₁ + N₂) p_{N₁+N₂}`.
Talagrand Vol. I, Theorem 1.3.9; Vol. II, §12.1. -/
theorem mul_mixedPSpinFreeEnergy_add_le {N₁ N₂ : ℕ} (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) {ξ : ℝ → ℝ}
    (hξ : ConvexOn ℝ (Icc (-1 : ℝ) 1) ξ) (hPSD : ∀ N, (overlapCovMatrix N ξ).PosSemidef)
    (h : ℝ) :
    (N₁ : ℝ) * mixedPSpinFreeEnergy N₁ ξ h + (N₂ : ℝ) * mixedPSpinFreeEnergy N₂ ξ h
      ≤ ((N₁ + N₂ : ℕ) : ℝ) * mixedPSpinFreeEnergy (N₁ + N₂) ξ h := by
  classical
  obtain ⟨Ω, instΩ, instP, G₁, G₂, G, h12, hsplit⟩ :=
    exists_disorder_triple N₁ N₂ (hPSD N₁) (hPSD N₂) (hPSD (N₁ + N₂))
  have hGT := mul_integral_free_energy_density_add_le_overlapCovKernel (Ω := Ω) hN₁ hN₂ hξ h
    G₁ G₂ G h12 hsplit
  rwa [integral_free_energy_density_eq_gaussFreeEnergy (S := overlapCovMatrix N₁ ξ)
      (fun _ _ => rfl) h G₁,
    integral_free_energy_density_eq_gaussFreeEnergy (S := overlapCovMatrix N₂ ξ)
      (fun _ _ => rfl) h G₂,
    integral_free_energy_density_eq_gaussFreeEnergy (S := overlapCovMatrix (N₁ + N₂) ξ)
      (fun _ _ => rfl) h G] at hGT

/-! ### The annealed bound -/

/-- **The annealed bound** `p_N ≤ log 2 + |h| + ξ(1)/2`: Jensen's inequality for the Gaussian
disorder against the free energy of the pure external field. Talagrand Vol. I, §1.3. -/
theorem mixedPSpinFreeEnergy_le (hN : 0 < N) {ξ : ℝ → ℝ}
    (hPSD : (overlapCovMatrix N ξ).PosSemidef) (h : ℝ) :
    mixedPSpinFreeEnergy N ξ h ≤ Real.log 2 + |h| + ξ 1 / 2 := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hJ := integral_free_energy_density_add_le (N := N) hN.ne' hPSD
    (D := (N : ℝ) * ξ 1) (fun σ => (overlapCovMatrix_diag N ξ σ).le) (H_field N h)
  have heq : mixedPSpinFreeEnergy N ξ h
      = ∫ v : EnergySpace N, free_energy_density (N := N) (H_field N h + v)
          ∂(gaussField N (overlapCovMatrix N ξ)) := by
    simp only [mixedPSpinFreeEnergy, gaussFreeEnergy, gaussField]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only [add_comm]
  have hD : (N : ℝ) * ξ 1 / (2 * (N : ℝ)) = ξ 1 / 2 := by
    rw [mul_comm (2 : ℝ), ← div_div, mul_div_cancel_left₀ _ hNR.ne']
  have hfield := free_energy_density_H_field_le hN h
  rw [heq]
  linarith [hJ, hD, hfield]

/-! ### The thermodynamic limit -/

/-- **`N ↦ N p_N` is superadditive**, by Guerra–Toninelli. -/
theorem superadditive_mul_mixedPSpinFreeEnergy {ξ : ℝ → ℝ} (hξ : ConvexOn ℝ (Icc (-1 : ℝ) 1) ξ)
    (hPSD : ∀ N, (overlapCovMatrix N ξ).PosSemidef) (h : ℝ) :
    Superadditive (fun N : ℕ => (N : ℝ) * mixedPSpinFreeEnergy N ξ h) := by
  intro m n
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  exact mul_mixedPSpinFreeEnergy_add_le hm hn hξ hPSD h

/-- The averages `p_N` are bounded above, uniformly in `N`. -/
theorem bddAbove_mixedPSpinFreeEnergy {ξ : ℝ → ℝ}
    (hPSD : ∀ N, (overlapCovMatrix N ξ).PosSemidef) (h : ℝ) :
    BddAbove (Set.range fun N : ℕ => ((N : ℝ) * mixedPSpinFreeEnergy N ξ h) / N) := by
  refine ⟨Real.log 2 + |h| + |ξ 1| / 2, ?_⟩
  rintro y ⟨N, rfl⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    simp only [Nat.cast_zero, zero_mul, zero_div]
    linarith [abs_nonneg h, abs_nonneg (ξ 1)]
  · have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    simp only []
    rw [mul_div_cancel_left₀ _ hNR.ne']
    have := mixedPSpinFreeEnergy_le hN (hPSD N) h
    linarith [le_abs_self (ξ 1)]

/-- **The free energy of a mixed `p`-spin model in the thermodynamic limit**,
`p(ξ, h) = lim_N p_N(ξ, h)`, for a profile convex on `[-1,1]` whose kernels are covariances.
Talagrand Vol. I, Theorem 1.3.9; Vol. II, §12.1. -/
def mixedPSpinFreeEnergyLimit {ξ : ℝ → ℝ} (hξ : ConvexOn ℝ (Icc (-1 : ℝ) 1) ξ)
    (hPSD : ∀ N, (overlapCovMatrix N ξ).PosSemidef) (h : ℝ) : ℝ :=
  (superadditive_mul_mixedPSpinFreeEnergy hξ hPSD h).lim

/-- **The thermodynamic limit of a convex mixed `p`-spin model exists**: `p_N → p`.
Fekete's lemma applied to the superadditive sequence `N ↦ N p_N`, whose averages are bounded above
by the annealed bound. Talagrand Vol. I, Theorem 1.3.9; Vol. II, §12.1. -/
theorem tendsto_mixedPSpinFreeEnergy {ξ : ℝ → ℝ} (hξ : ConvexOn ℝ (Icc (-1 : ℝ) 1) ξ)
    (hPSD : ∀ N, (overlapCovMatrix N ξ).PosSemidef) (h : ℝ) :
    Tendsto (fun N : ℕ => mixedPSpinFreeEnergy N ξ h) atTop
      (𝓝 (mixedPSpinFreeEnergyLimit hξ hPSD h)) := by
  have hfek := (superadditive_mul_mixedPSpinFreeEnergy hξ hPSD h).tendsto_lim
    (bddAbove_mixedPSpinFreeEnergy hPSD h)
  refine hfek.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [mul_div_cancel_left₀ _ hNR.ne']

/-- **The limit is the supremum**: every finite-volume free energy is below it. -/
theorem mixedPSpinFreeEnergy_le_limit {ξ : ℝ → ℝ} (hξ : ConvexOn ℝ (Icc (-1 : ℝ) 1) ξ)
    (hPSD : ∀ N, (overlapCovMatrix N ξ).PosSemidef) (h : ℝ) (hN : N ≠ 0) :
    mixedPSpinFreeEnergy N ξ h ≤ mixedPSpinFreeEnergyLimit hξ hPSD h := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
  have := (superadditive_mul_mixedPSpinFreeEnergy hξ hPSD h).div_le_lim
    (bddAbove_mixedPSpinFreeEnergy hPSD h) hN
  rwa [mul_div_cancel_left₀ _ hNR.ne'] at this

/-- The SK limit is the mixed `p`-spin limit at the profile `β² r²/2`. -/
theorem skFreeEnergyLimit_eq_mixedPSpinFreeEnergyLimit (β h : ℝ) :
    skFreeEnergyLimit β h
      = mixedPSpinFreeEnergyLimit (convexOn_skCovXi β) (fun N => posSemidef_skCovMatrix N β) h :=
  tendsto_nhds_unique (tendsto_skFreeEnergy β h) (tendsto_mixedPSpinFreeEnergy _ _ h)

/-! ### Even mixed `p`-spin models -/

/-- **A polynomial with nonnegative coefficients on even powers only is convex on `ℝ`.** -/
theorem convexOn_eval_of_even_coeff {P : Polynomial ℝ} (hP : ∀ n, 0 ≤ P.coeff n)
    (hodd : ∀ n, Odd n → P.coeff n = 0) :
    ConvexOn ℝ Set.univ fun r : ℝ => P.eval r := by
  have hterm : ∀ i : ℕ, ConvexOn ℝ Set.univ fun r : ℝ => P.coeff i * r ^ i := by
    intro i
    rcases Nat.even_or_odd i with hi | hi
    · simpa only [smul_eq_mul] using (Even.convexOn_pow (𝕜 := ℝ) hi).smul (hP i)
    · simpa [hodd i hi] using convexOn_const (0 : ℝ) (convex_univ (𝕜 := ℝ) (E := ℝ))
  have key : ∀ s : Finset ℕ, ConvexOn ℝ Set.univ fun r : ℝ => ∑ i ∈ s, P.coeff i * r ^ i := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simpa using convexOn_const (0 : ℝ) (convex_univ (𝕜 := ℝ) (E := ℝ))
    · intro i s hi ih
      simp_rw [Finset.sum_insert hi]
      exact (hterm i).add ih
  have hfun : (fun r : ℝ => P.eval r)
      = fun r : ℝ => ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * r ^ i := by
    funext r
    exact Polynomial.eval_eq_sum_range r
  rw [hfun]
  exact key _

/-- **Every even mixed `p`-spin model has a thermodynamic limit.** For a polynomial profile with
nonnegative coefficients on even powers only, the profile is convex and its kernels are
covariances (Talagrand's criterion (14.57)), so Guerra–Toninelli applies.
Talagrand Vol. I, Theorem 1.3.9; Vol. II, §12.1. -/
theorem tendsto_mixedPSpinFreeEnergy_of_polynomial {P : Polynomial ℝ} (hP : ∀ n, 0 ≤ P.coeff n)
    (hodd : ∀ n, Odd n → P.coeff n = 0) (h : ℝ) :
    Tendsto (fun N : ℕ => mixedPSpinFreeEnergy N (fun r => P.eval r) h) atTop
      (𝓝 (mixedPSpinFreeEnergyLimit
        ((convexOn_eval_of_even_coeff hP hodd).subset (Set.subset_univ _) (convex_Icc _ _))
        (fun N => posSemidef_overlapCovMatrix_of_polynomial N hP) h)) :=
  tendsto_mixedPSpinFreeEnergy _ _ h

/-! ### The Ghirlanda–Guerra perturbation does not change the limit

Lemma 12.2.1 bounds `|p_N(ξ + ∑ₛ wₛ² rˢ⁺¹) - p_N(ξ)|` by `∑ₛ wₛ²/2`; when the weights vanish the
perturbed free energies converge to the limit of the unperturbed ones. Talagrand Vol. II,
Lemma 12.2.1 and the discussion following it. -/

/-- **The perturbed free energies have the unperturbed limit**, for any vanishing perturbation
weights. Talagrand Vol. II, Lemma 12.2.1. -/
theorem tendsto_mixedPSpinFreeEnergy_perturbedProfile {P : Polynomial ℝ}
    (hP : ∀ k, 0 ≤ P.coeff k) {m : ℕ → ℕ} (w : ∀ N : ℕ, Fin (m N + 1) → ℝ)
    (hw : Tendsto (fun N : ℕ => ∑ s : Fin (m N + 1), (w N s) ^ 2) atTop (𝓝 0)) (h : ℝ) {L : ℝ}
    (hL : Tendsto (fun N : ℕ => mixedPSpinFreeEnergy N (fun r => P.eval r) h) atTop (𝓝 L)) :
    Tendsto (fun N : ℕ => mixedPSpinFreeEnergy N (perturbedProfile (fun r => P.eval r) (w N)) h)
      atTop (𝓝 L) := by
  have hd : Tendsto (fun N : ℕ =>
      mixedPSpinFreeEnergy N (perturbedProfile (fun r => P.eval r) (w N)) h
        - mixedPSpinFreeEnergy N (fun r => P.eval r) h) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa using hw.div_const (2 : ℝ))
    filter_upwards [eventually_ne_atTop 0] with N hN
    exact abs_gaussFreeEnergy_perturbedProfile_sub_le hN hP (w N) h
  simpa using hL.add hd

/-- **The perturbed free energies of the explicit Ghirlanda–Guerra capstone have the unperturbed
limit**: with `⌊N^{1/16}⌋ + 1` components of weights `β_s N^{-1/16}`, `β_s ∈ [a,b]`, the total
perturbation `∑ₛ wₛ² ≤ b² (⌊N^{1/16}⌋ + 1) N^{-1/8}` vanishes. Talagrand Vol. II, Lemma 12.2.1. -/
theorem tendsto_mixedPSpinFreeEnergy_perturbedProfile_explicit {P : Polynomial ℝ}
    (hP : ∀ k, 0 ≤ P.coeff k) (h : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (β : ∀ N : ℕ, Fin (⌊(N : ℝ) ^ ((1 : ℝ) / 16)⌋₊ + 1) → ℝ) (hβ : ∀ N s, β N s ∈ Set.Icc a b)
    {L : ℝ}
    (hL : Tendsto (fun N : ℕ => mixedPSpinFreeEnergy N (fun r => P.eval r) h) atTop (𝓝 L)) :
    Tendsto (fun N : ℕ => mixedPSpinFreeEnergy N
      (perturbedProfile (fun r => P.eval r) fun s => β N s * (N : ℝ) ^ (-((1 : ℝ) / 16))) h)
      atTop (𝓝 L) := by
  refine tendsto_mixedPSpinFreeEnergy_perturbedProfile hP
    (m := fun N => ⌊(N : ℝ) ^ ((1 : ℝ) / 16)⌋₊)
    (fun N s => β N s * (N : ℝ) ^ (-((1 : ℝ) / 16))) ?_ h hL
  have hlim := (tendsto_floor_rpow_mul_rpow_neg (α := (1 : ℝ) / 16) (β := (1 : ℝ) / 8)
    (by norm_num) (by norm_num)).const_mul (b ^ 2)
  rw [mul_zero] at hlim
  refine squeeze_zero (fun N => Finset.sum_nonneg fun s _ => sq_nonneg _) (fun N => ?_) hlim
  have hc : ((N : ℝ) ^ (-((1 : ℝ) / 16))) ^ 2 = (N : ℝ) ^ (-((1 : ℝ) / 8)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
    norm_num
  calc ∑ s : Fin (⌊(N : ℝ) ^ ((1 : ℝ) / 16)⌋₊ + 1), (β N s * (N : ℝ) ^ (-((1 : ℝ) / 16))) ^ 2
      = ∑ s : Fin (⌊(N : ℝ) ^ ((1 : ℝ) / 16)⌋₊ + 1),
          (β N s) ^ 2 * (N : ℝ) ^ (-((1 : ℝ) / 8)) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [mul_pow, hc]
    _ ≤ ∑ _s : Fin (⌊(N : ℝ) ^ ((1 : ℝ) / 16)⌋₊ + 1), b ^ 2 * (N : ℝ) ^ (-((1 : ℝ) / 8)) := by
        refine Finset.sum_le_sum fun s _ => ?_
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg N) _)
        have h1 := (hβ N s).1
        have h2 := (hβ N s).2
        exact sq_le_sq' (by linarith) h2
    _ = b ^ 2 * (((⌊(N : ℝ) ^ ((1 : ℝ) / 16)⌋₊ : ℝ) + 1) * (N : ℝ) ^ (-((1 : ℝ) / 8))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-- The explicit capstone is indexed by `k ↦ k + 1`; its perturbed free energies converge to the
unperturbed limit. -/
theorem tendsto_mixedPSpinFreeEnergy_perturbedProfile_explicit_succ {P : Polynomial ℝ}
    (hP : ∀ k, 0 ≤ P.coeff k) (h : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (β : ∀ N : ℕ, Fin (⌊(N : ℝ) ^ ((1 : ℝ) / 16)⌋₊ + 1) → ℝ) (hβ : ∀ N s, β N s ∈ Set.Icc a b)
    {L : ℝ}
    (hL : Tendsto (fun N : ℕ => mixedPSpinFreeEnergy N (fun r => P.eval r) h) atTop (𝓝 L)) :
    Tendsto (fun k : ℕ => mixedPSpinFreeEnergy (k + 1)
      (perturbedProfile (fun r => P.eval r)
        fun s => β (k + 1) s * ((k + 1 : ℕ) : ℝ) ^ (-((1 : ℝ) / 16))) h)
      atTop (𝓝 L) :=
  (tendsto_mixedPSpinFreeEnergy_perturbedProfile_explicit hP h ha hab β hβ hL).comp
    (tendsto_add_atTop_nat 1)

end

end SpinGlass
