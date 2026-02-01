import SpinGlass.Defs
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Independence.InfinitePi

/-!
# Hopfield model (Talagrand, Hopfield chapter): prerequisites

This file introduces a finite-volume Hopfield Hamiltonian and proves the
**Hubbard–Stratonovich transform** in a form aligned with Talagrand’s §4.2:

\[
\exp\Big(\frac{\beta N}{2}\,\|m(\sigma)\|^2\Big)
= \int \exp\big(\sqrt{\beta N}\,\langle z, m(\sigma)\rangle\big)\,d\gamma(z),
\]

where `γ` is the standard Gaussian measure on `ℝ^M` (here `Fin M → ℝ`).

We keep everything finite-dimensional and purely measurable; no topological assumptions.
-/

open MeasureTheory ProbabilityTheory Real BigOperators
open scoped ENNReal NNReal

namespace SpinGlass

variable {N M : ℕ}

/-! ## Patterns and overlaps -/

/-- A Hopfield "pattern family": `M` stored patterns, each a configuration in `{-1,+1}^N`. -/
abbrev Patterns (N M : ℕ) : Type := Fin M → Config N

/-- Overlap of a configuration `σ` with a stored pattern `ξ` (normalized dot product). -/
noncomputable def hopfieldOverlap (N : ℕ) (σ ξ : Config N) : ℝ :=
  (1 / (N : ℝ)) * ∑ i : Fin N, (spin N σ i) * (spin N ξ i)

/-- The Hopfield overlap vector \(m(\sigma)\in \mathbb R^M\). -/
noncomputable def hopfieldOverlapVec (N M : ℕ) (Ξ : Patterns N M) (σ : Config N) : Fin M → ℝ :=
  fun k => hopfieldOverlap (N := N) σ (Ξ k)

/-! ## Site-wise pattern matrix (Talagrand’s `η_{i,k}`) -/

/-- The pattern matrix in \(\{\pm 1\}\): `eta i k = η_{i,k}`. -/
noncomputable def hopfieldEta (N M : ℕ) (Ξ : Patterns N M) (i : Fin N) (k : Fin M) : ℝ :=
  spin N (Ξ k) i

lemma hopfieldOverlap_eq_eta (N M : ℕ) (Ξ : Patterns N M) (σ : Config N) (k : Fin M) :
    hopfieldOverlapVec (N := N) (M := M) Ξ σ k
      =
      (1 / (N : ℝ)) * ∑ i : Fin N, (hopfieldEta (N := N) (M := M) Ξ i k) * (spin N σ i) := by
  classical
  simp [hopfieldOverlapVec, hopfieldOverlap, hopfieldEta, mul_comm]

/-- Talagrand’s “first pattern constant” assumption: `η_{i,k0} = 1` for all sites `i`. -/
def IsConstantPattern (N : ℕ) {M : ℕ} (Ξ : Patterns N M) (k0 : Fin M) : Prop :=
  ∀ i : Fin N, Ξ k0 i = true

lemma hopfieldEta_eq_one_of_isConstantPattern (N : ℕ) {M : ℕ} {Ξ : Patterns N M} {k0 : Fin M}
    (hΞ : IsConstantPattern (N := N) Ξ k0) (i : Fin N) :
    hopfieldEta (N := N) (M := M) Ξ i k0 = 1 := by
  simp [hopfieldEta, spin, hΞ i]

/-! ## Hopfield Hamiltonian (as an `EnergySpace N` element) -/

/--
Hopfield energy functional (finite volume).

We define it with the sign convention compatible with `gibbs_pmf` in this repo:
`gibbs_pmf` uses weights `exp (-H σ)`. With this choice, the Gibbs weight becomes

`exp ((β*N/2) * ∑k (m_k(σ))^2)`,

matching Talagrand’s HS linearization formula.
-/
noncomputable def hopfieldEnergy (N M : ℕ) (β : ℝ) (Ξ : Patterns N M) : EnergySpace N :=
  WithLp.toLp 2 (fun σ : Config N =>
    -((β * (N : ℝ)) / 2) * ∑ k : Fin M, (hopfieldOverlapVec (N := N) (M := M) Ξ σ k) ^ 2)

/-!
Talagrand (Eq. 4.25) adds an external field term aligned with the first pattern:
\[
-H_{N,M}(\sigma) = \frac{N\beta}{2}\sum_{k\le M} m_k(\sigma)^2 + N h\, m_1(\sigma).
\]

We keep the index `k0 : Fin M` explicit (so we don't force `M > 0` globally).
-/
noncomputable def hopfieldEnergyWithField (N M : ℕ) (β h : ℝ) (Ξ : Patterns N M) (k0 : Fin M) :
    EnergySpace N :=
  WithLp.toLp 2 (fun σ : Config N =>
    -((β * (N : ℝ)) / 2) * ∑ k : Fin M, (hopfieldOverlapVec (N := N) (M := M) Ξ σ k) ^ 2
      - (h * (N : ℝ)) * (hopfieldOverlapVec (N := N) (M := M) Ξ σ k0))

lemma exp_neg_hopfieldEnergyWithField_eq
    (N M : ℕ) (β h : ℝ) (Ξ : Patterns N M) (k0 : Fin M) (σ : Config N) :
    Real.exp (-(hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0) σ)
      =
      Real.exp (((β * (N : ℝ)) / 2) * ∑ k : Fin M, (hopfieldOverlapVec (N := N) (M := M) Ξ σ k) ^ 2
        + (h * (N : ℝ)) * (hopfieldOverlapVec (N := N) (M := M) Ξ σ k0)) := by
  classical
  simp [hopfieldEnergyWithField, sub_eq_add_neg]
  ac_rfl

/-! ## The basic cosh-factorization identity -/

/-!
For any `a : Fin N → ℝ`,
\[
\sum_{\sigma \in \{-1,1\}^N} \exp\Big(\sum_i a_i \sigma_i\Big)
= \prod_i 2 \cosh(a_i).
\]

This is the finite algebraic step behind Talagrand’s `ψ(z)` (Eq. 4.34).
-/
lemma sum_exp_sum_spin (N : ℕ) (a : Fin N → ℝ) :
    (∑ σ : Config N, Real.exp (∑ i : Fin N, (a i) * (spin N σ i)))
      =
      ∏ i : Fin N, (Real.exp (a i) + Real.exp (-a i)) := by
  classical
  induction N with
  | zero =>
      simp
  | succ N ih =>
      -- split `σ : Fin (N+1) → Bool` into head `σ0` and tail `σtail`
      let e : (Bool × (Fin N → Bool)) ≃ (Fin (N + 1) → Bool) :=
        Fin.consEquiv (fun _ : Fin (N + 1) => Bool)
      -- rewrite the sum over `Config (N+1)` as a double sum over `(Bool × Config N)`
      have hsum :
          (∑ σ : Config (N + 1),
              Real.exp (∑ i : Fin (N + 1), (a i) * (spin (N + 1) σ i)))
            =
            ∑ p : Bool × (Fin N → Bool),
              Real.exp (∑ i : Fin (N + 1), (a i) * (spin (N + 1) (e p) i)) := by
        simpa using
          (Fintype.sum_equiv e
            (f := fun p => Real.exp (∑ i : Fin (N + 1), (a i) * (spin (N + 1) (e p) i)))
            (g := fun σ => Real.exp (∑ i : Fin (N + 1), (a i) * (spin (N + 1) σ i)))
            (h := fun _ => rfl)).symm
      -- compute the inner expression: it splits into the `i=0` term + a sum over the tail
      have hsplit (b : Bool) (σtail : Fin N → Bool) :
          (∑ i : Fin (N + 1), (a i) * (spin (N + 1) (e (b, σtail)) i))
            =
            (a 0) * (if b then 1 else -1)
              + ∑ j : Fin N, (a (Fin.succ j)) * (spin N σtail j) := by
        -- `Fin (N+1)` is `0` plus the `succ` indices
        simp [e, Fin.sum_univ_succ, spin]
      -- now sum over `b : Bool` explicitly, producing an `(exp(a0)+exp(-a0))` factor
      calc
        (∑ σ : Config (N + 1),
              Real.exp (∑ i : Fin (N + 1), (a i) * (spin (N + 1) σ i)))
            =
            ∑ p : Bool × (Fin N → Bool),
              Real.exp (∑ i : Fin (N + 1), (a i) * (spin (N + 1) (e p) i)) := hsum
        _ =
            ∑ σtail : (Fin N → Bool),
              (Real.exp (a 0) + Real.exp (-a 0))
                * Real.exp (∑ j : Fin N, (a (Fin.succ j)) * (spin N σtail j)) := by
            -- expand the sum over `b : Bool` at fixed `σtail`
            -- `Fintype.sum_prod_type` splits the sum over `Bool × Config N` into nested sums.
            -- After expanding `exp (A + B)` as `exp A * exp B`, we use distributivity to collect terms.
            simp [Fintype.sum_prod_type, hsplit, Real.exp_add, add_mul, mul_comm,
              Finset.sum_add_distrib]
        _ =
            (Real.exp (a 0) + Real.exp (-a 0))
              * (∑ σtail : (Fin N → Bool),
                  Real.exp (∑ j : Fin N, (a (Fin.succ j)) * (spin N σtail j))) := by
            simp [Finset.mul_sum]
        _ =
            (Real.exp (a 0) + Real.exp (-a 0))
              * (∏ j : Fin N, (Real.exp (a (Fin.succ j)) + Real.exp (-a (Fin.succ j)))) := by
            -- apply IH to the tail
            have ih' :
                (∑ σtail : (Fin N → Bool),
                    Real.exp (∑ j : Fin N, (a (Fin.succ j)) * (spin N σtail j)))
                  =
                  ∏ j : Fin N, (Real.exp (a (Fin.succ j)) + Real.exp (-a (Fin.succ j))) := by
              simpa using (ih (a := fun j => a (Fin.succ j)))
            simp [ih']
        _ = ∏ i : Fin (N + 1), (Real.exp (a i) + Real.exp (-a i)) := by
            -- finish by recognizing the product over `Fin (N+1)` as head * tail product
            simp [Fin.prod_univ_succ]

-- NOTE: Talagrand writes the RHS as `∏ i, 2 * cosh (a i)`. We keep the equivalent
-- `∏ i, (exp (a i) + exp (-a i))` form to avoid rewriting loops in the simp set around `cosh`.

/-! ## Standard Gaussian on `ℝ^M` and Hubbard–Stratonovich -/

/-- Standard Gaussian measure on `ℝ^M` (as `Fin M → ℝ`) with independent `N(0,1)` coordinates. -/
noncomputable def stdGaussianMeasure (M : ℕ) : Measure (Fin M → ℝ) :=
  Measure.infinitePi (fun _ : Fin M => (ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0)))

instance (M : ℕ) : IsProbabilityMeasure (stdGaussianMeasure M) := by
  classical
  dsimp [stdGaussianMeasure]
  infer_instance

private lemma mgf_eval_stdGaussian (M : ℕ) (k : Fin M) :
    ProbabilityTheory.mgf (fun z : Fin M → ℝ => z k) (stdGaussianMeasure M)
      = ProbabilityTheory.mgf id (ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0)) := by
  have hmap :
      (stdGaussianMeasure M).map (fun z : Fin M → ℝ => z k)
        = ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0) := by
    simpa [stdGaussianMeasure] using
      (measurePreserving_eval_infinitePi (μ := fun _ : Fin M =>
        (ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0))) k).map_eq
  have hm :
      ProbabilityTheory.mgf id ((stdGaussianMeasure M).map (fun z : Fin M → ℝ => z k))
        =
        ProbabilityTheory.mgf (fun z : Fin M → ℝ => z k) (stdGaussianMeasure M) := by
    have hmeas : AEMeasurable (fun z : Fin M → ℝ => z k) (stdGaussianMeasure M) := by
      exact (measurable_pi_apply k).aemeasurable
    simpa using (ProbabilityTheory.mgf_id_map (μ := stdGaussianMeasure M)
      (X := fun z : Fin M → ℝ => z k) hmeas)
  simpa [hmap] using hm.symm

/--
Hubbard–Stratonovich / Gaussian linearization identity on `ℝ^M` with product standard Gaussian.

This is the core identity used in Talagrand’s Hopfield analysis (his §4.2).
We state it in the form “mgf of a linear form”.
-/
theorem hubbardStratonovich_stdGaussian (M : ℕ) (c : ℝ) (hc : 0 ≤ c) (m : Fin M → ℝ) :
    (∫ z : Fin M → ℝ, Real.exp ((Real.sqrt c) * (∑ k : Fin M, m k * z k))
        ∂(stdGaussianMeasure M))
      =
      Real.exp ((c / 2) * ∑ k : Fin M, (m k) ^ 2) := by
  let μ : Measure (Fin M → ℝ) := stdGaussianMeasure M
  let X : Fin M → (Fin M → ℝ) → ℝ := fun k z => m k * z k
  have h_indep : ProbabilityTheory.iIndepFun (fun k z => z k) μ := by
    simpa [μ, stdGaussianMeasure] using
      (ProbabilityTheory.iIndepFun_infinitePi
        (P := fun _ : Fin M => (ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0)))
        (X := fun _ : Fin M => id) (by fun_prop))
  have h_indep' : ProbabilityTheory.iIndepFun X μ :=
    (ProbabilityTheory.iIndepFun.comp h_indep (fun k x => m k * x) (fun _ => by fun_prop))
  have hX_meas : ∀ k, Measurable (X k) := by fun_prop
  have hL :
      (∫ z : Fin M → ℝ, Real.exp ((Real.sqrt c) * (∑ k : Fin M, m k * z k)) ∂μ)
        =
        ProbabilityTheory.mgf ((Finset.univ : Finset (Fin M)).sum fun k => X k) μ (Real.sqrt c) := by
    simp [ProbabilityTheory.mgf, X, μ, Finset.mul_sum, mul_assoc, mul_comm]
  have hmgf_sum :
      ProbabilityTheory.mgf ((Finset.univ : Finset (Fin M)).sum fun k => X k) μ (Real.sqrt c)
        = ∏ k : Fin M, ProbabilityTheory.mgf (X k) μ (Real.sqrt c) := by
    simpa using (h_indep'.mgf_sum (μ := μ) (t := Real.sqrt c) hX_meas (Finset.univ : Finset (Fin M)))
  have hmgf_one (k : Fin M) :
      ProbabilityTheory.mgf (X k) μ (Real.sqrt c) =
        Real.exp (((Real.sqrt c) * m k) ^ 2 / 2) := by
    have hmap_val :
        ProbabilityTheory.mgf (fun z : Fin M → ℝ => z k) μ ((m k) * (Real.sqrt c))
          =
          ProbabilityTheory.mgf id (ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0))
            ((m k) * (Real.sqrt c)) := by
      simpa [μ, stdGaussianMeasure] using
        congrArg (fun F : ℝ → ℝ => F ((m k) * (Real.sqrt c))) (mgf_eval_stdGaussian (M := M) k)
    have hscale :
        ProbabilityTheory.mgf (X k) μ (Real.sqrt c)
          = ProbabilityTheory.mgf (fun z : Fin M → ℝ => z k) μ ((m k) * (Real.sqrt c)) := by
      simpa [X, mul_assoc, mul_left_comm, mul_comm] using
        (ProbabilityTheory.mgf_const_mul (μ := μ) (X := fun z : Fin M → ℝ => z k) (α := m k)
          (t := Real.sqrt c))
    have hgauss :
        ProbabilityTheory.mgf id (ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0)) ((m k) * (Real.sqrt c))
          = Real.exp ((((m k) * (Real.sqrt c)) ^ 2) / 2) := by
      simpa using congrArg (fun F => F ((m k) * (Real.sqrt c)))
        (ProbabilityTheory.mgf_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)))
    calc
      ProbabilityTheory.mgf (X k) μ (Real.sqrt c)
          = ProbabilityTheory.mgf (fun z : Fin M → ℝ => z k) μ ((m k) * (Real.sqrt c)) := hscale
      _ = ProbabilityTheory.mgf id (ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0)) ((m k) * (Real.sqrt c)) := hmap_val
      _ = Real.exp (((m k) * (Real.sqrt c)) ^ 2 / 2) := hgauss
      _ = Real.exp (((Real.sqrt c) * m k) ^ 2 / 2) := by ring_nf
  have :
      (∏ k : Fin M, ProbabilityTheory.mgf (X k) μ (Real.sqrt c))
        = Real.exp ((c / 2) * ∑ k : Fin M, (m k) ^ 2) := by
    have hsqrt_sq : (Real.sqrt c) ^ 2 = c := by
      simpa using (Real.sq_sqrt hc)
    calc
      (∏ k : Fin M, ProbabilityTheory.mgf (X k) μ (Real.sqrt c))
          = ∏ k : Fin M, Real.exp (((Real.sqrt c) * m k) ^ 2 / 2) := by
              simp [hmgf_one]
      _ = Real.exp (∑ k : Fin M, (((Real.sqrt c) * m k) ^ 2 / 2)) := by
            simpa using (Real.exp_sum (s := (Finset.univ : Finset (Fin M)))
              (f := fun k : Fin M => (((Real.sqrt c) * m k) ^ 2 / 2))).symm
      _ = Real.exp ((c / 2) * ∑ k : Fin M, (m k) ^ 2) := by
            have : (∑ k : Fin M, (((Real.sqrt c) * m k) ^ 2 / 2))
                = (c / 2) * ∑ k : Fin M, (m k) ^ 2 := by
              have hs : (Real.sqrt c) * (Real.sqrt c) = c := by
                simpa [pow_two] using hsqrt_sq
              calc
                (∑ k : Fin M, (((Real.sqrt c) * m k) ^ 2 / 2))
                    = ∑ k : Fin M, (c / 2) * (m k) ^ 2 := by
                        refine Finset.sum_congr rfl (fun k _hk => ?_)
                        simp [pow_two, hs, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv]
                _ = (c / 2) * ∑ k : Fin M, (m k) ^ 2 := by
                      simp [Finset.mul_sum]
            simp [this]
  calc
    (∫ z : Fin M → ℝ, Real.exp ((Real.sqrt c) * (∑ k : Fin M, m k * z k)) ∂μ)
        = ProbabilityTheory.mgf ((Finset.univ : Finset (Fin M)).sum fun k => X k) μ (Real.sqrt c) := hL
    _ = ∏ k : Fin M, ProbabilityTheory.mgf (X k) μ (Real.sqrt c) := hmgf_sum
    _ = Real.exp ((c / 2) * ∑ k : Fin M, (m k) ^ 2) := this

/-! ### Specialization to Hopfield weights -/

/--
Hubbard–Stratonovich identity specialized to the Hopfield overlap vector `m(σ)`.

This is the exact “linearization of the quadratic weight” used in Talagrand §4.2, written with the
sign conventions of this repo (`gibbs_pmf` uses `exp (-H)`).
-/
theorem hubbardStratonovich_hopfield
    (N M : ℕ) (β : ℝ) (hβ : 0 ≤ β) (Ξ : Patterns N M) (σ : Config N) :
    Real.exp (-(hopfieldEnergy (N := N) (M := M) β Ξ) σ)
      =
      ∫ z : Fin M → ℝ,
        Real.exp ((Real.sqrt (β * (N : ℝ))) * (∑ k : Fin M, (hopfieldOverlapVec (N := N) (M := M) Ξ σ k) * z k))
          ∂(stdGaussianMeasure M) := by
  have hβN : 0 ≤ β * (N : ℝ) := mul_nonneg hβ (by exact_mod_cast (Nat.zero_le N))
  have hHS :=
    (hubbardStratonovich_stdGaussian (M := M) (c := β * (N : ℝ)) hβN
      (m := hopfieldOverlapVec (N := N) (M := M) Ξ σ))
  simpa [hopfieldEnergy, hHS, hopfieldOverlapVec, hopfieldOverlap, mul_assoc, mul_left_comm, mul_comm,
    sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hHS.symm

/-!
From here, the Hopfield HS transform for the actual overlap vector `m(σ)` is obtained by
instantiating `m := hopfieldOverlapVec Ξ σ` and `c := β * N`.
-/

end SpinGlass
