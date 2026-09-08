/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.MixedPSpinComponentGG
import Common.Mathlib.Probability.Distributions.Gaussian.MultivariateSum
import Common.Mathlib.Data.Fin.InsertNthUpdate

/-!
# Finite families of independent Gaussian disorders

Talagrand's extended Ghirlanda–Guerra identities (Vol. II, Theorem 12.2.2) perturb a Hamiltonian
by a *family* of independent Gaussian components `∑ₛ βₛ Hₛ`, and isolate one component at a time:
for the `s`-th component the pair `(∑_{i ≠ s} βᵢ Hᵢ, Hₛ)` is an independent pair of centered
Gaussian disorders, to which Theorem 12.1.1 applies.

This file provides the canonical carrier of such a family — the product of the canonical fields
`gaussField N (T i)` — and the three facts the pair machinery consumes:

* the coordinates are mutually independent (`iIndepFun_eval_familyLaw`);
* a linear combination of the coordinates is the centered Gaussian field with the combined
  covariance (`familyLaw_map_sum_smul`, through
  `ProbabilityTheory.multivariateGaussian_map_sum_smul_pi`);
* hence the combination of the coordinates other than `s`, and the `s`-th coordinate, form an
  independent pair of `GaussianDisorder`s (`familyRest`, `familyCoord`,
  `indepFun_familyRest_familyCoord`).

## Main statements

- `SpinGlass.GaussianDisorder.ofMap`: a measurable Hamiltonian whose law is `gaussField N S` is a
  Gaussian disorder with kernel `S`.
- `SpinGlass.familyLaw`, `familyLaw_map_eval`, `familyLaw_map_sum_smul`,
  `familyLaw_map_sum_erase_smul`, `iIndepFun_eval_familyLaw`, `indepFun_sum_erase_eval`.
- `SpinGlass.familyCoord`, `SpinGlass.familyRest`, `indepFun_familyRest_familyCoord`.
- `SpinGlass.familyHam`, `SpinGlass.familyFluct`, `SpinGlass.energyFluctuationBound`,
  `intervalIntegral_familyFluct_update_le`, `abs_ghirlandaGuerra_defect_family_le`,
  `setIntegral_familyFluct_le`, `exists_couplings_familyFluct_le`, and
  **`exists_couplings_abs_ghirlandaGuerra_defect_family_le`** — Talagrand's Theorem 12.2.2 at
  finite volume.
-/

open MeasureTheory ProbabilityTheory Real BigOperators Filter Topology Set
open scoped InnerProductSpace ENNReal

namespace SpinGlass

noncomputable section

variable {N : ℕ}

/-! ### A Gaussian disorder from its law -/

/-- A measurable Hamiltonian whose law is the canonical centered Gaussian field with covariance `S`
is a `GaussianDisorder` with kernel `S`. -/
def GaussianDisorder.ofMap {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {U : Ω → EnergySpace N} (hU : Measurable U) {S : Matrix (Config N) (Config N) ℝ}
    (hS : S.PosSemidef) (hlaw : P.map U = gaussField N S) :
    GaussianDisorder (Ω := Ω) (N := N) P (fun σ τ => S σ τ) where
  U := U
  measU := hU
  hU := ⟨by rw [hlaw]; infer_instance⟩
  mean0 := by rw [hlaw]; exact integral_id_gaussField N S
  cov_eq := fun σ τ => by
    rw [hlaw]
    exact inner_covarianceOperator_multivariateGaussian_std_basis S hS σ τ

@[simp] lemma GaussianDisorder.ofMap_U {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {U : Ω → EnergySpace N} (hU : Measurable U) {S : Matrix (Config N) (Config N) ℝ}
    (hS : S.PosSemidef) (hlaw : P.map U = gaussField N S) :
    (GaussianDisorder.ofMap (N := N) hU hS hlaw).U = U := rfl

/-! ### The canonical carrier of a finite family of independent Gaussian disorders -/

section Family

variable {n : ℕ} (T : Fin n → Matrix (Config N) (Config N) ℝ)

/-- The canonical joint law of `n` independent centered Gaussian fields with covariances `T i`:
the product of the canonical fields. -/
def familyLaw : Measure (Fin n → EnergySpace N) := Measure.pi fun i => gaussField N (T i)

instance isProbabilityMeasure_familyLaw : IsProbabilityMeasure (familyLaw (N := N) T) := by
  unfold familyLaw; infer_instance

/-- The `i`-th coordinate has law `gaussField N (T i)`. -/
lemma familyLaw_map_eval (i : Fin n) :
    (familyLaw (N := N) T).map (fun ω => ω i) = gaussField N (T i) :=
  (measurePreserving_eval (fun i => gaussField N (T i)) i).map_eq

/-- **The law of a linear combination of the coordinates is the centered Gaussian field with the
combined covariance** `∑ i, (c i)² T i`. -/
lemma familyLaw_map_sum_smul (hT : ∀ i, (T i).PosSemidef) (c : Fin n → ℝ) :
    (familyLaw (N := N) T).map (fun ω => ∑ i, c i • ω i)
      = gaussField N (∑ i, (c i) ^ 2 • T i) := by
  unfold familyLaw gaussField
  exact multivariateGaussian_map_sum_smul_pi hT c

/-- The coordinates are mutually independent. -/
lemma iIndepFun_eval_familyLaw :
    iIndepFun (fun i (ω : Fin n → EnergySpace N) => ω i) (familyLaw (N := N) T) := by
  unfold familyLaw
  exact iIndepFun_pi (X := fun _ => id) fun _ => aemeasurable_id

/-- Dropping the `s`-th term of a combination is the combination with the `s`-th coefficient set
to zero. -/
lemma sum_erase_smul_eq_sum_update (c : Fin n → ℝ) (s : Fin n) (ω : Fin n → EnergySpace N) :
    ∑ i ∈ Finset.univ.erase s, c i • ω i = ∑ i, Function.update c s 0 i • ω i := by
  classical
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ s), Function.update_self, zero_smul, add_zero]
  exact Finset.sum_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

/-- The law of the combination of the coordinates other than `s`. -/
lemma familyLaw_map_sum_erase_smul (hT : ∀ i, (T i).PosSemidef) (c : Fin n → ℝ) (s : Fin n) :
    (familyLaw (N := N) T).map (fun ω => ∑ i ∈ Finset.univ.erase s, c i • ω i)
      = gaussField N (∑ i ∈ Finset.univ.erase s, (c i) ^ 2 • T i) := by
  classical
  have h1 : (fun ω : Fin n → EnergySpace N => ∑ i ∈ Finset.univ.erase s, c i • ω i)
      = fun ω => ∑ i, Function.update c s 0 i • ω i :=
    funext (sum_erase_smul_eq_sum_update c s)
  rw [h1, familyLaw_map_sum_smul T hT]
  congr 1
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ s), Function.update_self]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_smul, add_zero]
  exact Finset.sum_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

/-- The combination of the coordinates other than `s` is independent of the `s`-th coordinate. -/
lemma indepFun_sum_erase_eval (c : Fin n → ℝ) (s : Fin n) :
    IndepFun (fun ω : Fin n → EnergySpace N => ∑ i ∈ Finset.univ.erase s, c i • ω i)
      (fun ω => ω s) (familyLaw (N := N) T) := by
  classical
  have hind := (iIndepFun_eval_familyLaw (N := N) T).indepFun_finset (Finset.univ.erase s) {s}
    (Finset.disjoint_singleton_right.mpr (Finset.notMem_erase s _))
    (fun i => measurable_pi_apply i)
  have hφ : Measurable fun v : ↥(Finset.univ.erase s) → EnergySpace N =>
      ∑ i : ↥(Finset.univ.erase s), c i.1 • v i :=
    Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).const_smul (c i.1)
  have h := hind.comp hφ
    (measurable_pi_apply (⟨s, Finset.mem_singleton_self s⟩ : ↥({s} : Finset (Fin n))))
  convert h using 1
  · funext ω
    simp only [Function.comp]
    exact (Finset.sum_coe_sort (Finset.univ.erase s) (fun i => c i • ω i)).symm
  · rfl

/-- A finite sum of positive semidefinite matrices is positive semidefinite. -/
lemma posSemidef_sum_sq_smul (hT : ∀ i, (T i).PosSemidef) (c : Fin n → ℝ) (F : Finset (Fin n)) :
    (∑ i ∈ F, (c i) ^ 2 • T i).PosSemidef :=
  Finset.sum_induction _ Matrix.PosSemidef (fun _ _ ha hb => ha.add hb) Matrix.PosSemidef.zero
    (fun i _ => (hT i).smul_sq (c i))

/-- The `s`-th coordinate as a Gaussian disorder with kernel `T s`. -/
def familyCoord (hT : ∀ i, (T i).PosSemidef) (s : Fin n) :
    GaussianDisorder (Ω := Fin n → EnergySpace N) (N := N) (familyLaw (N := N) T)
      (fun σ τ => T s σ τ) :=
  GaussianDisorder.ofMap (measurable_pi_apply s) (hT s) (familyLaw_map_eval T s)

/-- The combination of the coordinates other than `s` as a Gaussian disorder, with kernel
`∑_{i ≠ s} (c i)² T i`. -/
def familyRest (hT : ∀ i, (T i).PosSemidef) (c : Fin n → ℝ) (s : Fin n) :
    GaussianDisorder (Ω := Fin n → EnergySpace N) (N := N) (familyLaw (N := N) T)
      (fun σ τ => (∑ i ∈ Finset.univ.erase s, (c i) ^ 2 • T i) σ τ) :=
  GaussianDisorder.ofMap
    (Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).const_smul (c i))
    (posSemidef_sum_sq_smul T hT c _) (familyLaw_map_sum_erase_smul T hT c s)

@[simp] lemma familyCoord_U (hT : ∀ i, (T i).PosSemidef) (s : Fin n) (ω : Fin n → EnergySpace N) :
    (familyCoord (N := N) T hT s).U ω = ω s := rfl

@[simp] lemma familyRest_U (hT : ∀ i, (T i).PosSemidef) (c : Fin n → ℝ) (s : Fin n)
    (ω : Fin n → EnergySpace N) :
    (familyRest (N := N) T hT c s).U ω = ∑ i ∈ Finset.univ.erase s, c i • ω i := rfl

/-- The pair `(∑_{i ≠ s} c i • ωᵢ, ωₛ)` is an independent pair of Gaussian disorders. -/
lemma indepFun_familyRest_familyCoord (hT : ∀ i, (T i).PosSemidef) (c : Fin n → ℝ) (s : Fin n) :
    (familyRest (N := N) T hT c s).U ⟂ᵢ[familyLaw (N := N) T] (familyCoord (N := N) T hT s).U :=
  indepFun_sum_erase_eval T c s

end Family

/-! ### The perturbed Hamiltonian and the fluctuation functional of a component -/

section Perturbation

variable {n : ℕ} (T : Fin (n + 1) → Matrix (Config N) (Config N) ℝ)

/-- **The perturbed Hamiltonian** `c₀ + H₀ + ∑ₛ βₛ Hₛ` on the family space: coordinate `0` is the
model's own disorder, coordinates `s.succ` the independent perturbing components with couplings
`β s`. Talagrand, Vol. II, (12.33). -/
def familyHam (c₀ : EnergySpace N) (β : Fin n → ℝ) (ω : Fin (n + 1) → EnergySpace N) :
    EnergySpace N :=
  c₀ + ω 0 + ∑ s, β s • ω s.succ

omit T in
lemma measurable_familyHam (c₀ : EnergySpace N) (β : Fin n → ℝ) :
    Measurable (familyHam (N := N) c₀ β) := by
  unfold familyHam
  exact (measurable_const.add (measurable_pi_apply 0)).add
    (Finset.measurable_sum _ fun s _ => (measurable_pi_apply s.succ).const_smul (β s))

omit T in
lemma continuous_familyHam (c₀ : EnergySpace N) (ω : Fin (n + 1) → EnergySpace N) :
    Continuous fun β : Fin n → ℝ => familyHam (N := N) c₀ β ω := by
  unfold familyHam
  exact continuous_const.add
    (continuous_finsetSum _ fun s _ => (continuous_apply s).smul continuous_const)

omit T in
/-- **Isolating one component.** With the `s`-th coupling set to `y`, the perturbed Hamiltonian is
the affine pair form `(H_A + c₀) + y • Hₛ`, where `H_A` is the combination of all other coordinates
with coefficients `Fin.cons 1 (Function.update β s 0)`. -/
lemma familyHam_update_eq (c₀ : EnergySpace N) (β : Fin n → ℝ) (s : Fin n) (y : ℝ)
    (ω : Fin (n + 1) → EnergySpace N) :
    familyHam (N := N) c₀ (Function.update β s y) ω
      = ((∑ i ∈ Finset.univ.erase s.succ,
            (Fin.cons (1 : ℝ) (Function.update β s (0 : ℝ)) : Fin (n + 1) → ℝ) i • ω i) + c₀)
          + y • ω s.succ := by
  classical
  unfold familyHam
  have hsum : ∀ y' : ℝ, ∑ p ∈ Finset.univ.erase s, Function.update β s y' p • ω p.succ
      = ∑ p ∈ Finset.univ.erase s, β p • ω p.succ := fun y' =>
    Finset.sum_congr rfl fun p hp => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hp)]
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ _), Fin.sum_univ_succ, Fin.cons_zero, one_smul,
    Fin.cons_succ, Function.update_self, zero_smul, sub_zero]
  simp only [Fin.cons_succ]
  rw [← Finset.sum_erase_add Finset.univ (fun p => Function.update β s y p • ω p.succ)
      (Finset.mem_univ s),
    ← Finset.sum_erase_add Finset.univ (fun p => Function.update β s (0 : ℝ) p • ω p.succ)
      (Finset.mem_univ s),
    hsum y, hsum 0, Function.update_self, Function.update_self, zero_smul, add_zero]
  abel

/-- Completing the kernel of the rest by the isolated component gives the kernel of the whole
perturbed model: `∑_{i ≠ s.succ} cᵢ² Tᵢ + βₛ² T_{s.succ} = T 0 + ∑ₚ βₚ² T_{p.succ}`. -/
lemma sum_erase_sq_smul_add (β : Fin n → ℝ) (s : Fin n) :
    (∑ i ∈ Finset.univ.erase s.succ,
        ((Fin.cons (1 : ℝ) (Function.update β s (0 : ℝ)) : Fin (n + 1) → ℝ) i) ^ 2 • T i)
      + (β s) ^ 2 • T s.succ
      = T 0 + ∑ p, (β p) ^ 2 • T p.succ := by
  classical
  have hsum : ∑ p ∈ Finset.univ.erase s, (Function.update β s (0 : ℝ) p) ^ 2 • T p.succ
      = ∑ p ∈ Finset.univ.erase s, (β p) ^ 2 • T p.succ :=
    Finset.sum_congr rfl fun p hp => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hp)]
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ _), Fin.sum_univ_succ, Fin.cons_zero, one_pow,
    one_smul, Fin.cons_succ, Function.update_self, zero_pow two_ne_zero, zero_smul, sub_zero]
  simp only [Fin.cons_succ]
  rw [← Finset.sum_erase_add Finset.univ (fun p => (Function.update β s (0 : ℝ) p) ^ 2 • T p.succ)
      (Finset.mem_univ s),
    ← Finset.sum_erase_add Finset.univ (fun p => (β p) ^ 2 • T p.succ) (Finset.mem_univ s),
    hsum, Function.update_self, zero_pow two_ne_zero, zero_smul, add_zero]
  abel

/-- **The fluctuation functional of component `s`**: `𝔼⟨|Hₛ/N − 𝔼⟨Hₛ/N⟩|⟩` for the perturbed model,
as a function of the couplings `β`. This is the integrand of Talagrand's (12.3) for the
component. -/
def familyFluct (c₀ : EnergySpace N) (s : Fin n) (β : Fin n → ℝ) : ℝ :=
  ∫ ω, FiniteGibbs.gibbs_average (α := Config N) (familyHam c₀ β ω)
    (fun σ => |(1 / (N : ℝ)) * ω s.succ σ
      - ∫ ω', (1 / (N : ℝ)) * FiniteGibbs.gibbs_average (α := Config N)
          (familyHam c₀ β ω') (ω' s.succ) ∂(familyLaw (N := N) T)|) ∂(familyLaw (N := N) T)

lemma integrable_norm_eval_familyLaw (i : Fin (n + 1)) :
    Integrable (fun ω : Fin (n + 1) → EnergySpace N => ‖ω i‖) (familyLaw (N := N) T) := by
  have h := integrable_norm_gaussField N (T i)
  rw [← familyLaw_map_eval T i] at h
  exact (integrable_map_measure measurable_norm.aestronglyMeasurable
    (measurable_pi_apply i).aemeasurable).1 h

lemma familyFluct_nonneg (c₀ : EnergySpace N) (s : Fin n) (β : Fin n → ℝ) :
    0 ≤ familyFluct (N := N) T c₀ s β :=
  integral_nonneg fun _ =>
    FiniteGibbs.gibbs_average_abs_smul_sub_const_nonneg (α := Config N) N _ _ _

/-- **The fluctuation functional is continuous in the couplings.** -/
lemma continuous_familyFluct (c₀ : EnergySpace N) (s : Fin n) :
    Continuous (familyFluct (N := N) T c₀ s) := by
  unfold familyFluct
  exact FiniteGibbs.continuous_integral_totalFluct_param (α := Config N) (P := familyLaw T)
    (H := fun β ω => familyHam c₀ β ω) (V := fun ω => ω s.succ) N
    (fun β => measurable_familyHam c₀ β) (fun ω => continuous_familyHam c₀ ω)
    (measurable_pi_apply s.succ) (integrable_norm_eval_familyLaw T s.succ)

/-- **Theorem 12.1.1's explicit bound** for a component whose own kernel is bounded by `M₂` and
whose complement has kernel bounded by `M₁`, over the coupling window `[a,b]` with smoothing
parameter `δ`: the three terms `O(N^{-1/2}) + O(δ) + O(N^{-1/2}/δ)` of
`intervalIntegral_component_fluctuation_le`. -/
def energyFluctuationBound (N : ℕ) (δ a b M₁ M₂ : ℝ) : ℝ :=
  Real.sqrt ((b - a) * ((1 / (N : ℝ)) * (2 * ((|a| + |b|) * M₂) / (N : ℝ))))
    + (2 * δ * (2 * ((|a| + |b| + 2 * δ) * M₂) / (N : ℝ))
      + 3 * (b - a) * (Real.sqrt (M₁ + (|a| + |b| + δ) ^ 2 * M₂) / (N : ℝ)) / δ)

/-- The isolated component, in the pair form consumed by the pair layer: the total-fluctuation
integrand at couplings `update β s y` is the pair integrand along `(H_A, Hₛ)`. -/
lemma familyFluct_update_eq (hT : ∀ i, (T i).PosSemidef) (c₀ : EnergySpace N) (β : Fin n → ℝ)
    (s : Fin n) (y : ℝ) :
    familyFluct (N := N) T c₀ s (Function.update β s y)
      = ∫ ω, FiniteGibbs.gibbs_average (α := Config N)
          (((familyRest (N := N) T hT (Fin.cons (1 : ℝ) (Function.update β s (0 : ℝ))) s.succ).U ω
              + c₀) + y • (familyCoord (N := N) T hT s.succ).U ω)
          (fun σ => |(1 / (N : ℝ)) * ((familyCoord (N := N) T hT s.succ).U ω) σ
            - ∫ ω', (1 / (N : ℝ)) * FiniteGibbs.gibbs_average (α := Config N)
                (((familyRest (N := N) T hT (Fin.cons (1 : ℝ) (Function.update β s (0 : ℝ)))
                    s.succ).U ω' + c₀) + y • (familyCoord (N := N) T hT s.succ).U ω')
                ((familyCoord (N := N) T hT s.succ).U ω') ∂(familyLaw (N := N) T)|)
          ∂(familyLaw (N := N) T) := by
  unfold familyFluct
  simp only [familyRest_U, familyCoord_U, ← familyHam_update_eq]

set_option linter.style.haveILetI false in
-- The pair layer is stated for `MeasureSpace` carriers; the canonical family law is installed as
-- the volume with `letI`, whose inlining is what lets `ℙ` unfold to `familyLaw T` by `rfl`.
/-- **Theorem 12.1.1 for one component of a family.** For fixed couplings of the other
components, the fluctuation functional of component `s`, integrated over its own coupling in
`[a,b]`, is bounded by Theorem 12.1.1's explicit expression, with `M₁` a bound on the kernel of
the rest and `M₂` a bound on the component's kernel. -/
theorem intervalIntegral_familyFluct_update_le (hT : ∀ i, (T i).PosSemidef)
    (c₀ : EnergySpace N) {δ a b : ℝ} (hδ : 0 < δ) (hab : a ≤ b) (β : Fin n → ℝ) (s : Fin n)
    {d M₁ M₂ : ℝ} (hdiag : ∀ σ : Config N, T s.succ σ σ = d)
    (hk₁ : ∀ σ τ : Config N,
      |(∑ i ∈ Finset.univ.erase s.succ,
          ((Fin.cons (1 : ℝ) (Function.update β s (0 : ℝ)) : Fin (n + 1) → ℝ) i) ^ 2 • T i) σ τ|
        ≤ M₁)
    (hk₂ : ∀ σ τ : Config N, |T s.succ σ τ| ≤ M₂) :
    (∫ y in a..b, familyFluct (N := N) T c₀ s (Function.update β s y))
      ≤ energyFluctuationBound N δ a b M₁ M₂ := by
  classical
  letI : MeasureSpace (Fin (n + 1) → EnergySpace N) := ⟨familyLaw (N := N) T⟩
  set c : Fin (n + 1) → ℝ := Fin.cons (1 : ℝ) (Function.update β s (0 : ℝ)) with hc
  let G₁ := familyRest (N := N) T hT c s.succ
  let G₂ := familyCoord (N := N) T hT s.succ
  have hindep : G₁.U ⟂ᵢ[(ℙ : Measure (Fin (n + 1) → EnergySpace N))] G₂.U :=
    indepFun_familyRest_familyCoord (N := N) T hT c s.succ
  have hpair := intervalIntegral_component_fluctuation_le (Ω := Fin (n + 1) → EnergySpace N)
    (N := N) G₁ G₂ hindep c₀ hδ hab hdiag hk₁ hk₂
  refine le_trans (le_of_eq (intervalIntegral.integral_congr fun y _ => ?_)) hpair
  rw [integral_disorderPairLaw_totalFluct (Ω := Fin (n + 1) → EnergySpace N) (N := N) G₁ G₂ c₀ y]
  exact familyFluct_update_eq (N := N) T hT c₀ β s y

set_option linter.style.haveILetI false in
-- As above: the canonical family law is installed as the volume with `letI`.
/-- **The Ghirlanda–Guerra defect of the perturbed model at the profile of component `s`** is
controlled by the fluctuation functional of that component at the same couplings: if
`Tₛ = κ φ(R)` then for every `k` and `g`

`|defect(φ, g)| ≤ ‖g‖ N · 𝔼⟨|Hₛ/N − 𝔼⟨Hₛ/N⟩|⟩ / (k |βₛ κ|)`,

for the canonical law `gaussField N (T 0 + ∑ₚ βₚ² T p.succ)` shifted by `c₀`. -/
theorem abs_ghirlandaGuerra_defect_family_le (hT : ∀ i, (T i).PosSemidef) (hN : N ≠ 0)
    (c₀ : EnergySpace N) (β : Fin n → ℝ) (s : Fin n) {d κ : ℝ} (hκ : κ ≠ 0) (hβs : β s ≠ 0)
    (φ : C(OverlapValue, ℝ)) (hdiag : ∀ σ : Config N, T s.succ σ σ = d)
    (hTs : ∀ σ τ : Config N, T s.succ σ τ = κ * φ (overlapUnit N σ τ))
    {k : ℕ} (hk : 0 < k) (g : C(Fin k → Fin k → OverlapValue, ℝ)) :
    |(∫ R, φ (R 0 k) * g (blockRestrict k R)
          ∂(((gaussField N (T 0 + ∑ p, (β p) ^ 2 • T p.succ)).map
              (fun H : EnergySpace N => H + c₀)).bind (overlapArrayLaw N)))
        - ((1 / (k : ℝ)) * ((∫ R, φ (R 0 k)
                ∂(((gaussField N (T 0 + ∑ p, (β p) ^ 2 • T p.succ)).map
                    (fun H : EnergySpace N => H + c₀)).bind (overlapArrayLaw N)))
              * ∫ R, g (blockRestrict k R)
                ∂(((gaussField N (T 0 + ∑ p, (β p) ^ 2 • T p.succ)).map
                    (fun H : EnergySpace N => H + c₀)).bind (overlapArrayLaw N)))
          + (1 / (k : ℝ)) * ∑ l ∈ Finset.Ico 1 k,
              ∫ R, φ (R 0 l) * g (blockRestrict k R)
                ∂(((gaussField N (T 0 + ∑ p, (β p) ^ 2 • T p.succ)).map
                    (fun H : EnergySpace N => H + c₀)).bind (overlapArrayLaw N)))|
      ≤ (‖g‖ * ((N : ℝ) * familyFluct (N := N) T c₀ s β)) / ((k : ℝ) * |β s * κ|) := by
  classical
  letI : MeasureSpace (Fin (n + 1) → EnergySpace N) := ⟨familyLaw (N := N) T⟩
  set c : Fin (n + 1) → ℝ := Fin.cons (1 : ℝ) (Function.update β s (0 : ℝ)) with hc
  let G₁ := familyRest (N := N) T hT c s.succ
  let G₂ := familyCoord (N := N) T hT s.succ
  have hindep : G₁.U ⟂ᵢ[(ℙ : Measure (Fin (n + 1) → EnergySpace N))] G₂.U :=
    indepFun_familyRest_familyCoord (N := N) T hT c s.succ
  have hgaussP : ProbabilityTheory.IsGaussian
      (disorderPairLaw (Ω := Fin (n + 1) → EnergySpace N) (N := N) G₁ G₂) :=
    isGaussian_disorderPairLaw_of_indep (Ω := Fin (n + 1) → EnergySpace N) (N := N) G₁ G₂ hindep
  have hcomb := abs_ghirlandaGuerraCombinationOf_component_le
    (Ω := Fin (n + 1) → EnergySpace N) (N := N) G₁ G₂ hindep hN (β s) c₀ hdiag k
    (overlapReplicaFun N g) ⟨0, hk⟩ (abs_overlapReplicaFun_le N g)
  rw [integral_disorderPairLaw_totalFluct (Ω := Fin (n + 1) → EnergySpace N) (N := N) G₁ G₂ c₀
    (β s)] at hcomb
  have hF : familyFluct (N := N) T c₀ s β
      = ∫ ω, FiniteGibbs.gibbs_average (α := Config N) ((G₁.U ω + c₀) + β s • G₂.U ω)
          (fun σ => |(1 / (N : ℝ)) * (G₂.U ω) σ
            - ∫ ω', (1 / (N : ℝ)) * FiniteGibbs.gibbs_average (α := Config N)
                ((G₁.U ω' + c₀) + β s • G₂.U ω') (G₂.U ω')
                ∂(ℙ : Measure (Fin (n + 1) → EnergySpace N))|)
          ∂(ℙ : Measure (Fin (n + 1) → EnergySpace N)) := by
    have h := familyFluct_update_eq (N := N) T hT c₀ β s (β s)
    rwa [Function.update_eq_self] at h
  rw [← hF] at hcomb
  have hprob : IsProbabilityMeasure
      ((disorderPairLaw (Ω := Fin (n + 1) → EnergySpace N) (N := N) G₁ G₂).map
        (fun q : DisorderSpace (N := N) => pairAffine N (β s) q + c₀)) :=
    MeasureTheory.Measure.isProbabilityMeasure_map
      ((pairAffine N (β s)).continuous.add continuous_const).measurable.aemeasurable
  have hc' : ∀ σ τ : Config N,
      FiniteGibbs.crossKernel (disorderPairLaw (Ω := Fin (n + 1) → EnergySpace N) (N := N) G₁ G₂)
          (pairAffine N (β s)) (std_basis_right (N := N)) σ τ
        = (β s * κ) * φ (overlapUnit N σ τ) := by
    intro σ τ
    rw [crossKernel_pairAffine_std_basis_right (Ω := Fin (n + 1) → EnergySpace N) (N := N) G₁ G₂
      hindep (β s) σ τ, hTs σ τ]
    ring
  have hfinal := abs_ghirlandaGuerra_defect_of_le hk
    ((disorderPairLaw (Ω := Fin (n + 1) → EnergySpace N) (N := N) G₁ G₂).map
      (fun q : DisorderSpace (N := N) => pairAffine N (β s) q + c₀))
    (mul_ne_zero hβs hκ) φ hc' g hcomb
  -- identify the law of the perturbed model
  have hlaw : (disorderPairLaw (Ω := Fin (n + 1) → EnergySpace N) (N := N) G₁ G₂).map
        (fun q : DisorderSpace (N := N) => pairAffine N (β s) q + c₀)
      = (gaussField N (T 0 + ∑ p, (β p) ^ 2 • T p.succ)).map
          (fun H : EnergySpace N => H + c₀) := by
    have hcomp : (fun q : DisorderSpace (N := N) => pairAffine N (β s) q + c₀)
        = (fun H : EnergySpace N => H + c₀) ∘ (pairAffine N (β s)) := rfl
    rw [hcomp, ← MeasureTheory.Measure.map_map (measurable_add_const _)
      (pairAffine N (β s)).continuous.measurable,
      map_pairAffine_disorderPairLaw (Ω := Fin (n + 1) → EnergySpace N) (N := N) G₁ G₂ hindep
        (β s)]
    congr 2
    rw [← sum_erase_sq_smul_add (N := N) T β s]
    ext σ τ
    simp only [Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hc]
  rw [hlaw] at hfinal
  exact hfinal

end Perturbation

/-! ### Averaging over the box of couplings: Talagrand's Theorem 12.2.2 at finite volume -/

section Box

variable {m : ℕ} (T : Fin (m + 1 + 1) → Matrix (Config N) (Config N) ℝ)

/-- **Fubini over the box of couplings.** The `s`-th fluctuation functional, integrated over
`[a,b]^{m+1}`, is at most `(b-a)^m` times Theorem 12.1.1's bound: integrate first in the `s`-th
coupling (`intervalIntegral_familyFluct_update_le`, uniformly in the others), then over the rest. -/
theorem setIntegral_familyFluct_le (hT : ∀ i, (T i).PosSemidef) (c₀ : EnergySpace N)
    {δ a b : ℝ} (hδ : 0 < δ) (hab : a ≤ b) (s : Fin (m + 1)) {d M₁ M₂ : ℝ}
    (hdiag : ∀ σ : Config N, T s.succ σ σ = d)
    (hk₁ : ∀ z : Fin m → ℝ, (∀ j, z j ∈ Set.Icc a b) → ∀ σ τ : Config N,
      |(∑ i ∈ Finset.univ.erase s.succ,
          ((Fin.cons (1 : ℝ) (Fin.insertNth s (0 : ℝ) z) : Fin (m + 1 + 1) → ℝ) i) ^ 2 • T i)
          σ τ| ≤ M₁)
    (hk₂ : ∀ σ τ : Config N, |T s.succ σ τ| ≤ M₂) :
    (∫ β in Set.univ.pi fun _ : Fin (m + 1) => Set.Icc a b, familyFluct (N := N) T c₀ s β)
      ≤ (b - a) ^ m * energyFluctuationBound N δ a b M₁ M₂ := by
  classical
  set F := familyFluct (N := N) T c₀ s with hF
  set ν : Measure ℝ := volume.restrict (Set.Icc a b) with hν
  have hνfin : IsFiniteMeasure ν :=
    ⟨by rw [hν, Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  have hbox : (volume : Measure (Fin (m + 1) → ℝ)).restrict (Set.univ.pi fun _ => Set.Icc a b)
      = Measure.pi fun _ => ν := by
    rw [volume_pi, Measure.restrict_pi_pi]
  have hbox' : (volume : Measure (Fin m → ℝ)).restrict (Set.univ.pi fun _ => Set.Icc a b)
      = Measure.pi fun _ => ν := by
    rw [volume_pi, Measure.restrict_pi_pi]
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) s with he
  have hpres : MeasurePreserving e (Measure.pi fun _ => ν)
      (ν.prod (Measure.pi fun _ : Fin m => ν)) :=
    measurePreserving_piFinSuccAbove (fun _ => ν) s
  have hFcont : Continuous F := continuous_familyFluct T c₀ s
  have hFint : Integrable F (Measure.pi fun _ : Fin (m + 1) => ν) := by
    rw [← hbox]
    exact hFcont.continuousOn.integrableOn_compact (isCompact_univ_pi fun _ => isCompact_Icc)
  have hfint : Integrable (F ∘ e.symm) (ν.prod (Measure.pi fun _ : Fin m => ν)) := by
    rw [← hpres.integrable_comp_emb e.measurableEmbedding]
    have : (F ∘ e.symm) ∘ e = F := by funext x; simp
    rwa [this]
  have hsymm : ∀ (y : ℝ) (z : Fin m → ℝ), e.symm (y, z) = Fin.insertNth s y z := fun y z => rfl
  have hstep1 : (∫ β in Set.univ.pi fun _ : Fin (m + 1) => Set.Icc a b, F β)
      = ∫ q, (F ∘ e.symm) q ∂(ν.prod (Measure.pi fun _ : Fin m => ν)) := by
    rw [hbox, ← hpres.integral_comp' (F ∘ e.symm)]
    congr 1
    funext x
    simp
  have hupd : ∀ z : Fin m → ℝ,
      Function.update (Fin.insertNth s (0 : ℝ) z : Fin (m + 1) → ℝ) s 0
        = (Fin.insertNth s (0 : ℝ) z : Fin (m + 1) → ℝ) := fun z => by
    rw [Function.update_eq_self_iff, Fin.insertNth_apply_same]
  have hinner : ∀ z : Fin m → ℝ, (∀ j, z j ∈ Set.Icc a b) →
      (∫ y, (F ∘ e.symm) (y, z) ∂ν) ≤ energyFluctuationBound N δ a b M₁ M₂ := by
    intro z hz
    have h := intervalIntegral_familyFluct_update_le (N := N) T hT c₀ hδ hab
      (Fin.insertNth s 0 z) s hdiag (by rw [hupd z]; exact hk₁ z hz) hk₂
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc] at h
    refine le_trans (le_of_eq ?_) h
    rw [hν]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [Function.comp, hsymm, hF]
    rw [Fin.insertNth_eq_update s y 0 z]
  have hnn : ∀ q : ℝ × (Fin m → ℝ), 0 ≤ (F ∘ e.symm) q := fun _ => familyFluct_nonneg T c₀ s _
  have hae : ∀ᵐ z ∂(Measure.pi fun _ : Fin m => ν), ∀ j, z j ∈ Set.Icc a b := by
    rw [← hbox']
    exact (ae_restrict_mem (MeasurableSet.univ_pi fun _ => measurableSet_Icc)).mono
      fun z hz => Set.mem_univ_pi.1 hz
  have hπuniv : (Measure.pi fun _ : Fin m => ν).real Set.univ = (b - a) ^ m := by
    rw [measureReal_def, Measure.pi_univ]
    simp [hν, Real.volume_Icc, ENNReal.toReal_pow, ENNReal.toReal_ofReal (sub_nonneg.2 hab)]
  rw [hstep1, integral_prod_symm _ hfint]
  calc (∫ z, ∫ y, (F ∘ e.symm) (y, z) ∂ν ∂(Measure.pi fun _ : Fin m => ν))
      ≤ ∫ _z, energyFluctuationBound N δ a b M₁ M₂ ∂(Measure.pi fun _ : Fin m => ν) :=
        integral_mono_of_nonneg
          (Eventually.of_forall fun z => integral_nonneg fun y => hnn (y, z))
          (integrable_const _) (hae.mono fun z hz => hinner z hz)
    _ = (b - a) ^ m * energyFluctuationBound N δ a b M₁ M₂ := by
        rw [integral_const, smul_eq_mul, hπuniv]

/-- **A coupling vector good for every component at once.** Averaging the sum of the
fluctuation functionals over the box `[a,b]^{m+1}` and applying the mean value principle
(`MeasureTheory.exists_le_setAverage`) produces couplings `β` in the box at which *every*
component's fluctuation functional is at most `(∑ₚ εₚ)/(b-a)`, `εₚ` being Theorem 12.1.1's bound
for component `p`. -/
theorem exists_couplings_familyFluct_le (hT : ∀ i, (T i).PosSemidef) (c₀ : EnergySpace N)
    {δ a b : ℝ} (hδ : 0 < δ) (hab : a < b) {M₁ : ℝ} {d M₂ : Fin (m + 1) → ℝ}
    (hdiag : ∀ (s : Fin (m + 1)) (σ : Config N), T s.succ σ σ = d s)
    (hk₁ : ∀ (s : Fin (m + 1)) (z : Fin m → ℝ), (∀ j, z j ∈ Set.Icc a b) → ∀ σ τ : Config N,
      |(∑ i ∈ Finset.univ.erase s.succ,
          ((Fin.cons (1 : ℝ) (Fin.insertNth s (0 : ℝ) z) : Fin (m + 1 + 1) → ℝ) i) ^ 2 • T i)
          σ τ| ≤ M₁)
    (hk₂ : ∀ (s : Fin (m + 1)) (σ τ : Config N), |T s.succ σ τ| ≤ M₂ s) :
    ∃ β : Fin (m + 1) → ℝ, (∀ s, β s ∈ Set.Icc a b) ∧
      ∀ s, familyFluct (N := N) T c₀ s β
        ≤ (∑ p, energyFluctuationBound N δ a b M₁ (M₂ p)) / (b - a) := by
  classical
  set box : Set (Fin (m + 1) → ℝ) := Set.univ.pi fun _ => Set.Icc a b with hbox
  set Φ : (Fin (m + 1) → ℝ) → ℝ := fun β => ∑ s, familyFluct (N := N) T c₀ s β with hΦ
  have hba : 0 < b - a := sub_pos.2 hab
  have hΦcont : Continuous Φ := continuous_finsetSum _ fun s _ => continuous_familyFluct T c₀ s
  have hcpt : IsCompact box := isCompact_univ_pi fun _ => isCompact_Icc
  have hΦint : IntegrableOn Φ box := hΦcont.continuousOn.integrableOn_compact hcpt
  have hFint : ∀ s, IntegrableOn (familyFluct (N := N) T c₀ s) box := fun s =>
    (continuous_familyFluct T c₀ s).continuousOn.integrableOn_compact hcpt
  have hvol : volume box = ENNReal.ofReal (b - a) ^ (m + 1) := by
    rw [hbox, volume_pi, Measure.pi_pi]
    simp [Real.volume_Icc]
  have hvol0 : volume box ≠ 0 := by
    rw [hvol]
    exact pow_ne_zero _ (by rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hba)
  have hvoltop : volume box ≠ ⊤ := by rw [hvol]; exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  obtain ⟨β, hβ, hle⟩ := exists_le_setAverage hvol0 hvoltop hΦint
  refine ⟨β, fun s => Set.mem_univ_pi.1 hβ s, fun s => ?_⟩
  have hint : (∫ β in box, Φ β)
      ≤ (b - a) ^ m * ∑ p, energyFluctuationBound N δ a b M₁ (M₂ p) := by
    simp only [hΦ]
    rw [integral_finsetSum _ fun p _ => hFint p, Finset.mul_sum]
    exact Finset.sum_le_sum fun p _ =>
      setIntegral_familyFluct_le T hT c₀ hδ hab.le p (hdiag p) (hk₁ p) (hk₂ p)
  have havg : (⨍ β in box, Φ β)
      ≤ (∑ p, energyFluctuationBound N δ a b M₁ (M₂ p)) / (b - a) := by
    rw [setAverage_eq, measureReal_def, hvol, smul_eq_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hba.le]
    have hpos : 0 < (b - a) ^ (m + 1) := pow_pos hba _
    rw [inv_mul_le_iff₀ hpos]
    calc (∫ β in box, Φ β) ≤ (b - a) ^ m * ∑ p, energyFluctuationBound N δ a b M₁ (M₂ p) := hint
      _ = (b - a) ^ (m + 1) * ((∑ p, energyFluctuationBound N δ a b M₁ (M₂ p)) / (b - a)) := by
          field_simp
          ring
  have hs : familyFluct (N := N) T c₀ s β ≤ Φ β :=
    Finset.single_le_sum (fun p _ => familyFluct_nonneg T c₀ p β) (Finset.mem_univ s)
  linarith

/-- The coefficients of the rest are bounded by `b` on the box. -/
lemma sq_cons_insertNth_succ_le {a b : ℝ} (ha : 0 ≤ a) (s : Fin (m + 1)) (z : Fin m → ℝ)
    (hz : ∀ j, z j ∈ Set.Icc a b) (p : Fin (m + 1)) :
    ((Fin.cons (1 : ℝ) (Fin.insertNth s (0 : ℝ) z) : Fin (m + 1 + 1) → ℝ) p.succ) ^ 2 ≤ b ^ 2 := by
  rw [Fin.cons_succ]
  refine s.succAboveCases ?_ ?_ p
  · rw [Fin.insertNth_apply_same, zero_pow two_ne_zero]
    exact sq_nonneg b
  · intro j
    rw [Fin.insertNth_apply_succAbove]
    exact pow_le_pow_left₀ (le_trans ha (hz j).1) (hz j).2 2

/-- On the box, the kernel of the rest is bounded by `M₀ + b² ∑ₚ M₂ p`. -/
lemma abs_rest_kernel_le {a b M₀ : ℝ} (ha : 0 ≤ a) (hk₀ : ∀ σ τ : Config N, |T 0 σ τ| ≤ M₀)
    {M₂ : Fin (m + 1) → ℝ} (hk₂ : ∀ (s : Fin (m + 1)) (σ τ : Config N), |T s.succ σ τ| ≤ M₂ s)
    (s : Fin (m + 1)) (z : Fin m → ℝ) (hz : ∀ j, z j ∈ Set.Icc a b) (σ τ : Config N) :
    |(∑ i ∈ Finset.univ.erase s.succ,
        ((Fin.cons (1 : ℝ) (Fin.insertNth s (0 : ℝ) z) : Fin (m + 1 + 1) → ℝ) i) ^ 2 • T i) σ τ|
      ≤ M₀ + b ^ 2 * ∑ p, M₂ p := by
  classical
  have hcb := sq_cons_insertNth_succ_le ha s z hz
  have hc0 : ((Fin.cons (1 : ℝ) (Fin.insertNth s (0 : ℝ) z) : Fin (m + 1 + 1) → ℝ) 0) ^ 2 = 1 := by
    rw [Fin.cons_zero, one_pow]
  have hterm : ∀ i : Fin (m + 1 + 1),
      |((Fin.cons (1 : ℝ) (Fin.insertNth s (0 : ℝ) z) : Fin (m + 1 + 1) → ℝ) i) ^ 2 * T i σ τ|
        = ((Fin.cons (1 : ℝ) (Fin.insertNth s (0 : ℝ) z) : Fin (m + 1 + 1) → ℝ) i) ^ 2
            * |T i σ τ| := fun i => by
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
  calc |(∑ i ∈ Finset.univ.erase s.succ,
          ((Fin.cons (1 : ℝ) (Fin.insertNth s (0 : ℝ) z) : Fin (m + 1 + 1) → ℝ) i) ^ 2 • T i) σ τ|
      = |∑ i ∈ Finset.univ.erase s.succ,
          ((Fin.cons (1 : ℝ) (Fin.insertNth s (0 : ℝ) z) : Fin (m + 1 + 1) → ℝ) i) ^ 2
            * T i σ τ| := by
        simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    _ ≤ ∑ i ∈ Finset.univ.erase s.succ,
          ((Fin.cons (1 : ℝ) (Fin.insertNth s (0 : ℝ) z) : Fin (m + 1 + 1) → ℝ) i) ^ 2
            * |T i σ τ| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (le_of_eq (Finset.sum_congr rfl fun i _ => hterm i))
    _ ≤ ∑ i, ((Fin.cons (1 : ℝ) (Fin.insertNth s (0 : ℝ) z) : Fin (m + 1 + 1) → ℝ) i) ^ 2
            * |T i σ τ| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun i _ _ => mul_nonneg (sq_nonneg _) (abs_nonneg _))
    _ = ((Fin.cons (1 : ℝ) (Fin.insertNth s (0 : ℝ) z) : Fin (m + 1 + 1) → ℝ) 0) ^ 2 * |T 0 σ τ|
          + ∑ p : Fin (m + 1),
            ((Fin.cons (1 : ℝ) (Fin.insertNth s (0 : ℝ) z) : Fin (m + 1 + 1) → ℝ) p.succ) ^ 2
              * |T p.succ σ τ| := Fin.sum_univ_succ _
    _ ≤ 1 * M₀ + ∑ p, b ^ 2 * M₂ p := by
        refine add_le_add ?_ (Finset.sum_le_sum fun p _ =>
          mul_le_mul (hcb p) (hk₂ p σ τ) (abs_nonneg _) (sq_nonneg _))
        rw [hc0]
        exact mul_le_mul_of_nonneg_left (hk₀ σ τ) zero_le_one
    _ = M₀ + b ^ 2 * ∑ p, M₂ p := by rw [one_mul, Finset.mul_sum]

set_option maxHeartbeats 1600000 in
-- The statement carries the (15.40) defect with its nested integrals for the family law.
/-- **Talagrand's Theorem 12.2.2 at finite volume (the extended Ghirlanda–Guerra identities).**

Let the Hamiltonian be perturbed by finitely many independent overlap-driven components
`Tₛ = κₛ φₛ(R)`, all kernels bounded (`|T 0| ≤ M₀`, `|Tₛ| ≤ M₂ s`) with constant diagonals, and
let `[a,b] ⊂ (0,∞)`. Then there are couplings `β ∈ [a,b]^{m+1}` such that the perturbed model —
the canonical field `gaussField N (T 0 + ∑ₛ βₛ² Tₛ)` shifted by the external field `c₀` —
satisfies the Ghirlanda–Guerra identity of Definition 15.3.4, Eq. (15.40), **at every profile
`φₛ` simultaneously and for every test function**, up to

`‖g‖ · N · (∑ₚ εₚ) / ((b-a) · k · |βₛ κₛ|)`,

`εₚ` being Theorem 12.1.1's bound with `M₁ = M₀ + b² ∑ M₂` and `M₂ = M₂ p`. Talagrand takes
`β ∈ [-1,1]^ℕ` and states the bound on average; the window `[a,b] ⊂ (0,∞)` avoids the
singularity at `βₛ = 0`, and the couplings are exhibited, not averaged over. -/
theorem exists_couplings_abs_ghirlandaGuerra_defect_family_le (hT : ∀ i, (T i).PosSemidef)
    (hN : N ≠ 0) (c₀ : EnergySpace N) {δ a b : ℝ} (hδ : 0 < δ) (hab : a < b) (ha : 0 < a)
    {M₀ : ℝ} (hk₀ : ∀ σ τ : Config N, |T 0 σ τ| ≤ M₀)
    {κ : Fin (m + 1) → ℝ} (hκ : ∀ s, κ s ≠ 0) (φ : Fin (m + 1) → C(OverlapValue, ℝ))
    (hTs : ∀ (s : Fin (m + 1)) (σ τ : Config N), T s.succ σ τ = κ s * φ s (overlapUnit N σ τ))
    {d M₂ : Fin (m + 1) → ℝ} (hdiag : ∀ (s : Fin (m + 1)) (σ : Config N), T s.succ σ σ = d s)
    (hk₂ : ∀ (s : Fin (m + 1)) (σ τ : Config N), |T s.succ σ τ| ≤ M₂ s) :
    ∃ β : Fin (m + 1) → ℝ, (∀ s, β s ∈ Set.Icc a b) ∧
      ∀ (s : Fin (m + 1)) {k : ℕ}, 0 < k → ∀ g : C(Fin k → Fin k → OverlapValue, ℝ),
        |(∫ R, φ s (R 0 k) * g (blockRestrict k R)
              ∂(((gaussField N (T 0 + ∑ p, (β p) ^ 2 • T p.succ)).map
                  (fun H : EnergySpace N => H + c₀)).bind (overlapArrayLaw N)))
            - ((1 / (k : ℝ)) * ((∫ R, φ s (R 0 k)
                    ∂(((gaussField N (T 0 + ∑ p, (β p) ^ 2 • T p.succ)).map
                        (fun H : EnergySpace N => H + c₀)).bind (overlapArrayLaw N)))
                  * ∫ R, g (blockRestrict k R)
                    ∂(((gaussField N (T 0 + ∑ p, (β p) ^ 2 • T p.succ)).map
                        (fun H : EnergySpace N => H + c₀)).bind (overlapArrayLaw N)))
              + (1 / (k : ℝ)) * ∑ l ∈ Finset.Ico 1 k,
                  ∫ R, φ s (R 0 l) * g (blockRestrict k R)
                    ∂(((gaussField N (T 0 + ∑ p, (β p) ^ 2 • T p.succ)).map
                        (fun H : EnergySpace N => H + c₀)).bind (overlapArrayLaw N)))|
          ≤ (‖g‖ * ((N : ℝ) *
                ((∑ p, energyFluctuationBound N δ a b (M₀ + b ^ 2 * ∑ q, M₂ q) (M₂ p))
                  / (b - a))))
              / ((k : ℝ) * |β s * κ s|) := by
  classical
  obtain ⟨β, hβ, hF⟩ := exists_couplings_familyFluct_le (N := N) T hT c₀ hδ hab
    (M₁ := M₀ + b ^ 2 * ∑ q, M₂ q) hdiag
    (fun s z hz σ τ => abs_rest_kernel_le (N := N) T ha.le hk₀ hk₂ s z hz σ τ) hk₂
  refine ⟨β, hβ, fun s {k} hk g => ?_⟩
  have hβs : β s ≠ 0 := ne_of_gt (lt_of_lt_of_le ha (hβ s).1)
  refine (abs_ghirlandaGuerra_defect_family_le (N := N) T hT hN c₀ β s (hκ s) hβs (φ s)
    (hdiag s) (hTs s) hk g).trans ?_
  have hg0 : 0 ≤ ‖g‖ := norm_nonneg g
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  gcongr
  exact hF s

end Box

end

end SpinGlass
