# SpinGlass

Lean 4 development of finite‑volume mean‑field spin glass calculus, organized as a `lean_lib`
`SpinGlass` (with an additional `GibbsMeasure` library developing https://github.com/james18lpc/GibbsMeasure and relevant for the formalziation vol 2 of Talagrand "Mean Field Models for Spin Glasses").


## Main definitions (core finite‑`N` objects)

Defined in `SpinGlass/Defs.lean` (namespace `SpinGlass`):

- **Configuration space**: `Config N := Fin N → Bool`.
- **Spin variable**: `spin N σ i : ℝ` (values `±1`).
- **Magnetization**: `magnetization N σ : ℝ`.
- **Energy space**: `EnergySpace N := PiLp 2 (fun _ : Config N => ℝ)` with an `InnerProductSpace`
  structure.
- **Canonical basis**: `std_basis N σ : EnergySpace N` and `inner_std_basis_apply`.
- **Overlap**: `overlap N σ τ : ℝ := (1/N) * ∑ i, spin σ i * spin τ i`.
- **Covariance kernels**:
  - `sk_cov_kernel N β σ τ : ℝ := (N * β^2 / 2) * (overlap N σ τ)^2`,
  - `simple_cov_kernel N β xi σ τ : ℝ := N * β^2 * xi (overlap N σ τ)`.
- **Partition function / Gibbs weights**:
  - `Z N H : ℝ := ∑ σ, exp (-H σ)`,
  - `gibbs_pmf N H σ : ℝ := exp (-H σ) / Z N H`.
- **Free energy density**: `free_energy_density N H : ℝ := (1/N) * log (Z N H)`.
- **Derivatives**:
  - `grad_free_energy_density N H : EnergySpace N →L[ℝ] ℝ`,
  - `hessian_free_energy N H h k : ℝ`,
  - `hessian_free_energy_fderiv N H : EnergySpace N →L[ℝ] EnergySpace N →L[ℝ] ℝ`.
- **Gibbs covariance**: `gibbs_covariance N H h k : ℝ`.

## Main statements (core identities and bounds)

In `SpinGlass/Defs.lean`:

- **Differentiation of partition function and Gibbs weights**:
  `hasFDerivAt_Z`, `hasFDerivAt_gibbs_pmf`, `fderiv_free_energy_density_eq`, etc.
- **Second derivative as covariance**:
  `hessian_eq_covariance` and `hessian_free_energy_fderiv_eq_hessian_free_energy`.
- **Trace formulas**:
  `trace_formula`, `trace_sk`, `trace_simple`.
- **Algebraic Guerra derivative identity** (finite‑`N`): `guerra_derivative_bound_algebra` and
  its re-export `SpinGlass.GuerraBound.guerra_derivative_bound_algebra_core`.

In `SpinGlass/Algebra.lean` (namespace `SpinGlass.Algebra`):

- `square_completion`.

## Disorder structures (Gaussian Hilbert)

In `SpinGlass/SKModel.lean`:

- `partition_function`, `gibbs_average`.
- `SKDisorder (Ω := Ω) N β h`:
  a centered Gaussian Hamiltonian `U : Ω → EnergySpace N` with covariance specified on `std_basis`
  by `sk_cov_kernel`.
- `SimpleDisorder (Ω := Ω) N β q`:
  a centered Gaussian Hamiltonian `V : Ω → EnergySpace N` with covariance specified on `std_basis`
  by `simple_cov_kernel`.

## Replica calculus and interpolation

In `SpinGlass/Replicas.lean`:

- **Replica spaces**: `ReplicaSpace N n := Fin n → Config N`, `ReplicaFun N n := ReplicaSpace N n → ℝ`.
- **Interpolated Hamiltonian**:
  `H_gauss`, `H_field := magnetic_field_vector`, `H_t`.
- **Joint Gaussian input**:
  `UV` and `isGaussianHilbert_UV` (Gaussian Hilbert structure on the product).
- **Replica Gibbs averages**:
  `gibbs_average_n_det`, `gibbs_average_n`.
- **Interpolated expectation functional**:
  `nu t f : ℝ` and its derivative statement `hasDerivAt_nu`.

In `SpinGlass/Calculus.lean`:

- `contDiff_Z`, `contDiff_free_energy_density`,
- `hessian_free_energy_eq_variance`,
- growth/integrability lemmas for Gaussian disorder (e.g. `integrable_free_energy_density_of_gaussian`).

In `SpinGlass/ComplexIBP.lean`:

- complex Wirtinger‑style auxiliaries `deriv_z`, `deriv_zbar`,
- `approx_integral_by_parts_complex` (approximate complex integration by parts under a Lipschitz
  derivative hypothesis).

In `SpinGlass/ArguinTaiFp.lean`: arithmeitc ddetour

- interval measure `μ01`, oscillatory factor `omega_p`,
- Arguin–Tai weight `arguinTaiWeight` and linear map `L_p`,
- moment and differentiability statements for `Z_p`, `N_p`, and `F_p`:
  `hasFDerivAt_Z_p_of_bounded`, `hasFDerivAt_N_p_of_bounded`, `hasFDerivAt_F_p_of_bounded`.


- `SpinGlass.Mathlib.Probability.Distributions.GaussianIntegrationByParts`:
  one-dimensional Gaussian tilt calculus (`gaussianTilt`, `gaussianTilt_hasDerivAt_left`, etc.).
- `SpinGlass.Mathlib.Probability.Distributions.Gaussian_IBP_Hilbert`:
  finite-dimensional Hilbert-space Gaussian IBP; introduces `PhysLean.Probability.GaussianIBP.IsGaussianHilbert`,
  `covOp`, and growth/integrability infrastructure (`HasModerateGrowth`).
- `SpinGlass.Mathlib.ParametricDominatedConvergence` (and the measure-theory variant):
  dominated convergence lemmas for parameter-dependent integrals.

## Build

Toolchain: see `lean-toolchain` (currently `leanprover/lean4:v4.28.0-rc1`).

```bash
lake build
```
