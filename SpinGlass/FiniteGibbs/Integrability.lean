import SpinGlass.FiniteGibbs.Calculus
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Notation
import Common.Mathlib.Probability.Distributions.Gaussian.CameronMartinFernique

/-!
# Finite Gibbs integrability

Growth bounds from `SpinGlass.FiniteGibbs.Calculus` as measure-theoretic integrability, for
differentiation under the integral along Gaussian disorder.
-/

open MeasureTheory ProbabilityTheory Real BigOperators Filter Topology

namespace SpinGlass

namespace FiniteGibbs

noncomputable section

variable {α : Type*} [Fintype α] [Nonempty α]

section

variable {Ω : Type*} [MeasureSpace Ω] (P : Measure Ω)

lemma integrable_free_energy_density_of_integrable_norm
    [IsFiniteMeasure P] (n : ℕ) {g : Ω → EnergySpace α} (hg_meas : Measurable g)
    (hg_int : Integrable (fun ω : Ω => ‖g ω‖) P) :
    Integrable (fun ω : Ω => free_energy_density (α := α) n (g ω)) P := by
  let C : ℝ := Real.log (Fintype.card α) + 1
  have hdom : Integrable (fun ω : Ω => C * (1 + ‖g ω‖)) P := by
    have : Integrable (fun ω : Ω => (1 : ℝ) + ‖g ω‖) P :=
      (integrable_const (μ := P) (c := (1 : ℝ))).add hg_int
    exact this.const_mul C
  refine hdom.mono' ?_ (ae_of_all _ (fun ω => ?_))
  · have hF : Measurable (fun x : EnergySpace α => free_energy_density (α := α) n x) :=
      (contDiff_free_energy_density (α := α) (n := n)).continuous.measurable
    exact (hF.comp hg_meas).aestronglyMeasurable
  · have hgrowth := abs_free_energy_density_le (α := α) (n := n) (H := g ω)
    have hnonneg : 0 ≤ C * (1 + ‖g ω‖) := by positivity
    simpa [C, Real.norm_eq_abs, abs_of_nonneg hnonneg] using hgrowth

lemma integrable_free_energy_density_of_isGaussian_map
    [IsProbabilityMeasure P] (n : ℕ) {g : Ω → EnergySpace α} (hg_meas : Measurable g)
    (hg_gauss : ProbabilityTheory.IsGaussian (P.map g)) :
    Integrable (fun ω : Ω => free_energy_density (α := α) n (g ω)) P := by
  classical
  let μ : Measure (EnergySpace α) := P.map g
  haveI : ProbabilityTheory.IsGaussian μ := hg_gauss
  have hIntμ : Integrable (fun x : EnergySpace α => free_energy_density (α := α) n x) μ := by
    refine ProbabilityTheory.IsGaussian.integrable_of_abs_le_mul_one_add_norm_pow
      (μ := μ)
      (F := fun x : EnergySpace α => free_energy_density (α := α) n x)
      ?_ (hC := by positivity) (m := 1) (C := Real.log (Fintype.card α) + 1) ?_
    · exact (contDiff_free_energy_density (α := α) (n := n)).continuous.measurable
    · intro x
      simpa [one_pow] using (abs_free_energy_density_le (α := α) (n := n) (H := x))
  have hpull :=
    (integrable_map_measure (μ := P) (f := g)
      (g := fun x : EnergySpace α => free_energy_density (α := α) n x)
      (by
        have hF : Measurable (fun x : EnergySpace α => free_energy_density (α := α) n x) :=
          (contDiff_free_energy_density (α := α) (n := n)).continuous.measurable
        exact hF.aestronglyMeasurable)
      hg_meas.aemeasurable).1 hIntμ
  simpa [Function.comp] using hpull

end

end

end FiniteGibbs

end SpinGlass
