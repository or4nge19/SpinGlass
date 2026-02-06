**Blueprint for Volume I**, structured to minimize API reduplication vs Volume II

**Formalization Strategy Note:** We try to use Volume II to formalize Volume I, so here we highlight the specific models of Vol I as *instances* of the general frameworks defined in Vol II.
*   **Chapter 1 (SK Model)** is the $p=2$ case of the **Mixed $p$-spin Model** (Vol II, Ch 12-14).
*   **Chapter 2 (Perceptron)** and **Chapter 3** utilize the **Cavity Method** and **Gaussian Interpolation** techniques generalized in Vol II for non-linear Hamiltonians.
*   **Chapter 4 (Hopfield)** is treated as a model with a specific covariance structure (finite rank) in Vol II, Chapter 10.

---

# 1. The Sherrington-Kirkpatrick (SK) Model (Chapter 1)

This is the fundamental mean-field spin glass. In the context of Volume II, this is the **Mixed $p$-spin model** with only $p=2$.

### 1.1 Definitions
**Configuration Space:** $\Sigma_N = \{-1, 1\}^N$.
**Disorder:** $g_{ij}$ are i.i.d. standard Gaussian variables $\mathcal{N}(0,1)$ for $1 \le i < j \le N$.
**Hamiltonian:**
$$ -H_N(\sigma) = \frac{\beta}{\sqrt{N}} \sum_{1 \le i < j \le N} g_{ij} \sigma_i \sigma_j + h \sum_{i=1}^N \sigma_i $$
*Note: Talagrand uses $-H_N$ to avoid minus signs in exponentials.*
**Parameters:** Inverse temperature $\beta \ge 0$, external field $h \in \mathbb{R}$.
**Partition Function:** $Z_N(\beta, h) = \sum_{\sigma \in \Sigma_N} \exp(-H_N(\sigma))$.
**Free Energy Density:** $p_N(\beta, h) = \frac{1}{N} \mathbb{E} \log Z_N(\beta, h)$.

### 1.2 Key Results for Formalization

#### 1.2.1 Gaussian Concentration of Measure
*Ref: Theorem 1.3.4*
This is the foundational tool for proving "Self-Averaging".
**Theorem:** Let $F: \mathbb{R}^M \to \mathbb{R}$ be a function with Lipschitz constant $A$ (w.r.t. Euclidean distance). Let $X$ be a standard Gaussian vector in $\mathbb{R}^M$. Then for $t > 0$:
$$ \mathbb{P}(|F(X) - \mathbb{E}F(X)| \ge t) \le 2 \exp\left(-\frac{t^2}{2A^2}\right) $$
**Application to SK:** Proves that $\frac{1}{N} \log Z_N$ concentrates around $p_N$ with rate $O(N^{-1})$.

#### 1.2.2 Existence of the Limit (Superadditivity)
*Ref: Theorem 1.3.9 (Guerra-Toninelli)*
**Theorem:** The sequence $(N p_N(\beta, h))_{N \ge 1}$ is superadditive:
$$ (N_1 + N_2) p_{N_1+N_2} \ge N_1 p_{N_1} + N_2 p_{N_2} $$
**Limit:** $p(\beta, h) = \lim_{N \to \infty} p_N(\beta, h)$ exists.
*Proof Method:* Interpolation between a system of size $N$ and two independent systems of sizes $N_1, N_2$.

#### 1.2.3 Guerra’s Replica-Symmetric Bound (The "Simple" Bound)
*Ref: Theorem 1.3.7*
This is the $k=0$ level of the Parisi formula (Vol II).
**Theorem:** For any $q \in [0, 1]$:
$$ p_N(\beta, h) \le \text{RS}(q) := \log 2 + \mathbb{E} \log \cosh(\beta z \sqrt{q} + h) + \frac{\beta^2}{4}(1-q)^2 $$
where $z \sim \mathcal{N}(0,1)$.
**Optimization:** The bound is minimized at $q$ satisfying $q = \mathbb{E} \tanh^2(\beta z \sqrt{q} + h)$.

#### 1.2.4 The High-Temperature Regime ($\beta < 1$)
**Latala’s Argument (Theorem 1.4.1):**
If $\beta < 1/2$ (can be pushed to $\beta < 1$ with more work), the overlap $R_{1,2} = \frac{1}{N} \sum \sigma^1_i \sigma^2_i$ concentrates around $q$.
$$ \mathbb{E} \langle (R_{1,2} - q)^2 \rangle \le \frac{K}{N} $$
*Significance:* This validates the RS solution at high temperature.

**Central Limit Theorem for Overlaps (Theorem 1.10.1):**
Under high-temperature conditions, $\sqrt{N}(R_{1,2} - q)$ converges to a Gaussian distribution.
*Formalization Note:* This requires the "Smart Path" interpolation method (Vol I, Sec 1.3 & 2.2) involving explicit derivatives of the free energy path.

---

# 2. The Perceptron Model (Chapter 2)

### 2.1 Definitions
**Configuration Space:** $\Sigma_N = \{-1, 1\}^N$.
**Disorder:** $M$ random patterns (vectors) $\xi_k \in \mathbb{R}^N$ with i.i.d. $\mathcal{N}(0,1)$ components.
**Parameter:** Constraint density $\alpha = M/N$.
**Hamiltonian (Capacity version):**
$$ -H_{N,M}(\sigma) = \sum_{k=1}^M u\left(\frac{1}{\sqrt{N}} \sum_{i=1}^N \xi_{i,k} \sigma_i\right) $$
where $u(x) = -\infty \cdot \mathbb{I}(x < \kappa)$ (Hard constraint) or a smooth approximation (Soft constraint).

### 2.2 Results
**Theorem 2.2.3 (Smart Path interpolation):**
Allows comparison between the Perceptron Hamiltonian and a "decoupled" system where spins are independent.
**Key Formula (Prop 2.2.3):**
$$ \frac{d}{dt} \nu_t(f) = \dots $$
This calculates the derivative of the Gibbs measure along a path connecting the interacting system to a simple one.
*Formalization Note:* This uses the general Gaussian Interpolation API.

---

# 3. The Shcherbina-Tirozzi Model (Chapter 3)

### 3.1 Definition
A variant of the Perceptron where the configuration space is $\mathbb{R}^N$ (Continuous spins) with a spherical constraint penalty.
**Hamiltonian:**
$$ -H(\sigma) = \sum_{k=1}^M u\left(\frac{1}{\sqrt{N}} \xi_k \cdot \sigma\right) + h \cdot \sigma - \kappa \|\sigma\|^2 $$
**Assumption:** $u$ is concave.

### 3.2 The Power of Convexity
**Theorem 3.1.4 (Brascamp-Lieb / Concentration):**
Because $H$ is convex (due to concave $u$), the Gibbs measure satisfies a Poincaré inequality (or Log-Sobolev), leading to very strong concentration of measure results independent of dimension $N$.
$$ \text{Var}(f) \le \frac{1}{\kappa} \mathbb{E} \|\nabla f\|^2 $$
*Significance:* This allows proving the validity of the RS solution *without* assuming high temperature, provided the convexity modulus $\kappa$ is large enough.

---

# 4. The Hopfield Model (Chapter 4)

### 4.1 Definitions
**Hamiltonian:**
$$ -H_N(\sigma) = \frac{N \beta}{2} \sum_{k=1}^M \left(\frac{1}{N} \sum_{i=1}^N \eta_{i,k} \sigma_i\right)^2 + h \sum \sigma_i $$
where $\eta_{i,k}$ are i.i.d. Bernoulli $\pm 1$ variables (patterns).
**Regime:** $M/N \to \alpha$.

### 4.2 Results
**Theorem 4.2.2 (Bovier-Gayrard):**
The function $\psi(z)$ related to the partition function is convex in a large region with overwhelming probability.
**Theorem 4.4.3 (Retrieval):**
If $\beta > 1$ and $\alpha$ is small, the Gibbs measure concentrates on balls around the patterns $\eta_{\cdot, k}$.
*Formalization Note:* Vol II Chapter 10 revisits this using the Cavity Method to get sharp bounds.

---

# 5. Technical Ground Truths for Mathlib

These are the abstract tools defined in Vol I that you should implement as the API.

1.  **Generic Gaussian Interpolation:**
    Given two Gaussian processes $X_t$ and $Y_t$, and $Z(t) = \sqrt{t}X + \sqrt{1-t}Y$, compute $\frac{d}{dt} \mathbb{E} F(Z(t))$.
    *Formula:* involves covariance differences and $\mathbb{E} \nabla^2 F$.

2.  **Cavity Step (Induction):**
    A mapping relating the free energy of an $N$-spin system to an $(N-1)$-spin system plus a "cavity field" term.
    *Formula (Eq 1.145):*
    $$ \langle f \rangle_N = \frac{\langle \text{Av}_\varepsilon f(\sigma, \varepsilon) e^{\beta z_\text{cav} \varepsilon} \rangle_{N-1}}{\langle \text{Av}_\varepsilon e^{\beta z_\text{cav} \varepsilon} \rangle_{N-1}} $$

3.  **Self-Averaging of the Free Energy:**
    Proof that $p_N$ is essentially deterministic using Gaussian concentration.

4.  **Symmetry between Sites/Replicas:**
    If the Hamiltonian is invariant under permutation of indices (in distribution), then observables like $\mathbb{E} \langle \sigma_i \rangle$ are independent of $i$.

5.  **Integration by Parts (Stein's Method):**
    For $g \sim \mathcal{N}(0,1)$, $\mathbb{E}[g f(g)] = \mathbb{E}[f'(g)]$.
    *Generalization:* For Gaussian vector $\mathbf{g}$ with cov $C$, $\mathbb{E}[g_i F(\mathbf{g})] = \sum_j C_{ij} \mathbb{E}[\partial_j F]$.
