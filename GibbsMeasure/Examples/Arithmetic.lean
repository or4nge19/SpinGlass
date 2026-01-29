import GibbsMeasure.Potential
import Mathlib.Probability.Distributions.Gaussian.Real

open ENNReal MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace GibbsMeasure.Examples.Arithmetic

variable {P : Type*} [DecidableEq P] [Fintype P] [MeasurableSpace P] -- Primes in the window

-- Ensure Bool has a measurable space for the Specification
instance : MeasurableSpace Bool := ⊤

/-- The single-site Hamiltonian term for a prime p.
    Y_p(σ) = 1_{σ_p} - 1/p.
    Here represented as a function on spins σ_p ∈ {0, 1}. -/
def Y (p_inv : P → ℝ) (p : P) (σ : P → Bool) : ℝ :=
  (if σ p then 1 else 0) - p_inv p

/-- The potential for the Arithmetic Spin Glass.
    Φ_{p}(σ) = Y_p(σ).
    All other interaction terms are 0. -/
noncomputable def arithmeticPotential (p_inv : P → ℝ) : Potential P Bool :=
  fun Δ σ ↦
    if Δ.card = 1 then
      Finset.sum Δ (fun p => Y p_inv p σ)
    else
      0

instance (p_inv : P → ℝ) : Potential.IsFinitary (arithmeticPotential p_inv) where
  finite_support := by
    classical
    let s : Finset (Finset P) := Finset.univ.image (fun p : P => ({p} : Finset P))
    apply Set.Finite.subset (s := (s : Set (Finset P)))
    · exact Finset.finite_toSet s
    · intro Δ hΔ
      have hne : arithmeticPotential p_inv Δ ≠ 0 := by
        simpa [Set.mem_setOf_eq] using hΔ
      have hcard : Δ.card = 1 := by
        by_contra hcard
        have : arithmeticPotential p_inv Δ = 0 := by
          funext σ
          simp [arithmeticPotential, hcard]
        exact hne this
      rcases Finset.card_eq_one.1 hcard with ⟨p, rfl⟩
      simp [s]

instance (p_inv : P → ℝ) : Potential.IsPotential (arithmeticPotential p_inv) where
  measurable Δ := by
    classical
    by_cases hcard : Δ.card = 1
    · rcases Finset.card_eq_one.1 hcard with ⟨p, rfl⟩
      have hcond :
          MeasurableSet[
            cylinderEvents (X := fun _ : P ↦ Bool) ({p} : Set P)
          ] {σ : P → Bool | σ p} := by
        have hproj :
            Measurable[
              cylinderEvents (X := fun _ : P ↦ Bool) ({p} : Set P)
            ] (fun σ : P → Bool => σ p) :=
          measurable_cylinderEvent_apply (i := p) (X := fun _ : P ↦ Bool)
            (Δ := ({p} : Set P)) (by simp)
        simpa [Set.preimage] using hproj (measurableSet_singleton true)
      have :
          Measurable[
            cylinderEvents (X := fun _ : P ↦ Bool) ({p} : Set P)
          ] (fun σ : P → Bool => arithmeticPotential p_inv {p} σ) := by
        have hIte :
            Measurable[
              cylinderEvents (X := fun _ : P ↦ Bool) ({p} : Set P)
            ] (fun σ : P → Bool => (if σ p then (1 : ℝ) else 0)) := by
          refine Measurable.ite hcond ?_ ?_
          · exact measurable_const
          · exact measurable_const
        have hY :
            Measurable[
              cylinderEvents (X := fun _ : P ↦ Bool) ({p} : Set P)
            ] (fun σ : P → Bool => Y p_inv p σ) := by
          simpa [Y] using hIte.sub measurable_const
        have hrewrite :
            (fun σ : P → Bool => arithmeticPotential p_inv {p} σ) =
              (fun σ : P → Bool => Y p_inv p σ) := by
          funext σ
          simp [arithmeticPotential, Finset.sum_singleton]
        simpa [hrewrite] using hY
      simpa using this
    · have hzero : arithmeticPotential p_inv Δ = 0 := by
        funext σ
        simp [arithmeticPotential, hcard]
      rw [hzero]
      exact measurable_const

/-- The Gibbs specification for the arithmetic model. -/
noncomputable def arithmeticSpecification (p_inv : P → ℝ) (β : ℝ) (ν : Measure Bool)
    [IsProbabilityMeasure ν]
    (hZ : ∀ (Λ : Finset P) (η : P → Bool),
      Specification.premodifierZ ν (Potential.boltzmannWeight (Φ := arithmeticPotential p_inv) β) Λ η ≠ ⊤) :
    Specification P Bool :=
  Potential.gibbsSpecification (arithmeticPotential p_inv) β ν hZ

/-- The finite-volume free energy density. -/
noncomputable def freeEnergyDensity (p_inv : P → ℝ) (β : ℝ) (ν : Measure Bool)
    [IsProbabilityMeasure ν] (Λ : Finset P) (η : P → Bool) : ℝ :=
  let Z := Specification.premodifierZ ν (Potential.boltzmannWeight (Φ := arithmeticPotential p_inv) β) Λ η
  (1 / (Λ.card : ℝ)) * Real.log (ENNReal.toReal Z)

/-- The prime overlap q_{12}.
    Relates to the covariance of the Gaussian field G(σ) = ∑_p g_p Y_p(σ) by:
    Cov(G(σ₁), G(σ₂)) = L * primeOverlap σ₁ σ₂. -/
noncomputable def primeOverlap (p_inv : P → ℝ) (L : ℝ) (σ₁ σ₂ : P → Bool) : ℝ :=
  (1 / L) * ∑ p : P, Y p_inv p σ₁ * Y p_inv p σ₂

/-- The self-overlap q_{11}. -/
noncomputable def selfOverlap (p_inv : P → ℝ) (L : ℝ) (σ : P → Bool) : ℝ :=
  primeOverlap p_inv L σ σ

/-- The finite-volume free energy density for the interpolated potential. -/
noncomputable def interpolatedPotential (p_inv : P → ℝ) (g : P → ℝ) (t : ℝ) : Potential P Bool :=
  fun Δ σ ↦
    if Δ.card = 1 then
      Real.sqrt t * Finset.sum Δ (fun p => g p * Y p_inv p σ)
    else
      0

instance (p_inv : P → ℝ) (g : P → ℝ) (t : ℝ) :
    Potential.IsFinitary (interpolatedPotential p_inv g t) where
  finite_support := by
    classical
    let s : Finset (Finset P) := Finset.univ.image (fun p : P => ({p} : Finset P))
    apply Set.Finite.subset (s := (s : Set (Finset P)))
    · exact Finset.finite_toSet s
    · intro Δ hΔ
      have hne : interpolatedPotential p_inv g t Δ ≠ 0 := by
        simpa [Set.mem_setOf_eq] using hΔ
      have hcard : Δ.card = 1 := by
        by_contra hcard
        have : interpolatedPotential p_inv g t Δ = 0 := by
          funext σ
          simp [interpolatedPotential, hcard]
        exact hne this
      rcases Finset.card_eq_one.1 hcard with ⟨p, rfl⟩
      simp [s]

instance (p_inv : P → ℝ) (g : P → ℝ) (t : ℝ) :
    Potential.IsPotential (interpolatedPotential p_inv g t) where
  measurable Δ := by
    classical
    by_cases hcard : Δ.card = 1
    · rcases Finset.card_eq_one.1 hcard with ⟨p, rfl⟩
      have hcond :
          MeasurableSet[
            cylinderEvents (X := fun _ : P ↦ Bool) ({p} : Set P)
          ] {σ : P → Bool | σ p} := by
        have hproj :
            Measurable[
              cylinderEvents (X := fun _ : P ↦ Bool) ({p} : Set P)
            ] (fun σ : P → Bool => σ p) :=
          measurable_cylinderEvent_apply (i := p) (X := fun _ : P ↦ Bool)
            (Δ := ({p} : Set P)) (by simp)
        simpa [Set.preimage] using hproj (measurableSet_singleton true)
      have :
          Measurable[
            cylinderEvents (X := fun _ : P ↦ Bool) ({p} : Set P)
          ] (fun σ : P → Bool => interpolatedPotential p_inv g t {p} σ) := by
        have hIte :
            Measurable[
              cylinderEvents (X := fun _ : P ↦ Bool) ({p} : Set P)
            ] (fun σ : P → Bool => (if σ p then (1 : ℝ) else 0)) := by
          refine Measurable.ite hcond ?_ ?_
          · exact measurable_const
          · exact measurable_const
        have hY :
            Measurable[
              cylinderEvents (X := fun _ : P ↦ Bool) ({p} : Set P)
            ] (fun σ : P → Bool => Y p_inv p σ) := by
          simpa [Y] using hIte.sub measurable_const
        have hterm :
            Measurable[
              cylinderEvents (X := fun _ : P ↦ Bool) ({p} : Set P)
            ] (fun σ : P → Bool => (Real.sqrt t) * (g p * Y p_inv p σ)) := by
          simpa [mul_assoc] using (measurable_const.mul (measurable_const.mul hY))
        have hrewrite :
            (fun σ : P → Bool => interpolatedPotential p_inv g t {p} σ) =
              (fun σ : P → Bool => (Real.sqrt t) * (g p * Y p_inv p σ)) := by
          funext σ
          simp [interpolatedPotential, Finset.sum_singleton]
        simpa [hrewrite] using hterm
      simpa using this
    · have hzero : interpolatedPotential p_inv g t Δ = 0 := by
        funext σ
        simp [interpolatedPotential, hcard]
      rw [hzero]
      exact measurable_const

noncomputable def interpolatedFreeEnergyDensity (p_inv : P → ℝ) (g : P → ℝ) (t : ℝ) (β : ℝ) (ν : Measure Bool)
    [IsProbabilityMeasure ν] (Λ : Finset P) (η : P → Bool) : ℝ :=
  let Z := Specification.premodifierZ ν (Potential.boltzmannWeight (Φ := interpolatedPotential p_inv g t) β) Λ η
  (1 / (Λ.card : ℝ)) * Real.log (ENNReal.toReal Z)

/-- The derivative of the free energy density with respect to t.
    ∂_t F_N(t) = - (β / (2 * N * √t)) * ⟨ ∑_p g_p Y_p ⟩_t
    where the expectation is taken with respect to the Gibbs measure at time t. -/
noncomputable def interpolatedFreeEnergyDerivative (p_inv : P → ℝ) (g : P → ℝ) (t : ℝ) (β : ℝ) (ν : Measure Bool)
    [IsProbabilityMeasure ν] (Λ : Finset P) (η : P → Bool) : ℝ :=
  let μ := Specification.isssd ν Λ η
  let ρ := Potential.boltzmannWeight (Φ := interpolatedPotential p_inv g t) β Λ
  let Z := ∫⁻ σ, ρ σ ∂μ
  let H_deriv := fun σ ↦ ∑ p ∈ Λ, g p * Y p_inv p σ
  let num := ∫ σ, H_deriv σ * (ρ σ).toReal ∂μ
  let expectation := num / Z.toReal;
  -(β / (2 * Real.sqrt t * Λ.card)) * expectation

/-- The standard Gaussian measure on the space of coefficients P → ℝ. -/
noncomputable def standardGaussianMeasure : Measure (P → ℝ) :=
  Measure.pi (fun _ ↦ gaussianReal 0 1)

/- The Guerra interpolation identity.
    ∂_t E[F_N(t)] = - (β^2 L / (2 N)) * E[ ⟨ q_{11} - q_{12} ⟩_t ].
    This relates the change in free energy to the variance of the overlap. -/
/-
theorem guerra_interpolation_identity
    (p_inv : P → ℝ) (β : ℝ) (ν : Measure Bool) [IsProbabilityMeasure ν]
    (Λ : Finset P) (η : P → Bool)
    :
    ∀ t > 0,
    deriv (fun t ↦ ∫ g, interpolatedFreeEnergyDensity p_inv g t β ν Λ η ∂standardGaussianMeasure) t =
    - (β^2 * Λ.card / (2 * Λ.card)) * -- Assuming L ≈ Λ.card for normalization
      ∫ g, (
        let μ := Specification.isssd ν Λ η
        let H := interpolatedPotential p_inv g t
        let ρ := Potential.boltzmannWeight (Φ := H) β Λ
        let Z := ∫⁻ σ, ρ σ ∂μ
        -- The Gibbs expectation of (q11 - q12)
        (∫ σ, (selfOverlap p_inv Λ.card σ) * (ρ σ).toReal ∂μ) / Z.toReal -
        (∫ σ, (∫ σ', (primeOverlap p_inv Λ.card σ σ') * (ρ σ').toReal ∂μ) * (ρ σ).toReal ∂μ) / (Z.toReal ^ 2)
      ) ∂standardGaussianMeasure := sorry
      -/

end GibbsMeasure.Examples.Arithmetic
