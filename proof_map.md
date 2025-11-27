# Riemann Hypothesis Proof Map (Hardy-Schur Pinch Route)

This document maps the logical structure of the proof strategy, tracing the implication chain from the final contradiction back to the fundamental axioms and inputs. It highlights the critical path, the analytic engines, and the current status of verification.

## I. The Logical Chain (Top-Down)

### Level 0: The Goal
**Theorem**: The Riemann Hypothesis (RH) is true.
*   **Statement**: $\xi(s) \neq 0$ for $\text{Re}(s) > 1/2$.

### Level 1: The Contradiction ("The Pinch")
**Strategy**: Assume there exists an off-critical zero $\rho$ (with $\text{Re}(\rho) > 1/2$). Construct a function $\Theta(s)$ that forces a contradiction.

*   **Object**: $\Theta(s)$ (The Schur Function).
*   **Condition 1 (N1 - Normalization)**: $\lim_{\sigma \to \infty} \Theta(\sigma + it) = -1$.
    *   *Source*: Construction of $\Theta$ from primes and outer normalization.
*   **Condition 2 (N2 - Interpolation)**: $\Theta(\rho) = 1$.
    *   *Source*: Pole of $J$ at $\rho$ (since $\xi(\rho)=0$) maps to 1 under Cayley transform.
*   **Condition 3 (Schur Property)**: $|\Theta(s)| \le 1$ for all $s \in \Omega \setminus Z(\xi)$.
    *   *Source*: Boundary Maximum Principle (from Level 2).
*   **The Conflict**:
    *   By Condition 3, $\Theta$ extends to a holomorphic function on $\Omega$ (removable singularity at $\rho$).
    *   By Maximum Modulus Principle (and Schwarz Lemma), a Schur function cannot take the value 1 in the interior unless it is constantly 1.
    *   But Condition 1 says it tends to -1.
    *   **Contradiction**: $1 \neq -1$. Thus, no such $\rho$ exists.

### Level 2: Establishing the Schur Property
**Goal**: Prove $|\Theta(s)| \le 1$ in the half-plane $\Omega$.

*   **Transformation**: Define $\Theta = \frac{F-1}{F+1}$, where $F = 2J$.
*   **Equivalence**: $|\Theta| \le 1 \iff \text{Re}(F) \ge 0$ (Herglotz Property).
*   **Mechanism**: **Poisson Transport**.
    *   If $\text{Re}(F(1/2+it)) \ge 0$ almost everywhere on the boundary (Condition **P+**),
    *   Then $\text{Re}(F(s)) \ge 0$ everywhere in the interior (for well-behaved $F$).

### Level 3: The Boundary Wedge (P+) ("The Trap")
**Goal**: Prove $\text{Re}(F(1/2+it)) \ge 0$ a.e. (or Phase Deviation $< \pi/2$).

*   **Construction of $J$**:
    *   $J(s) = \frac{\det_2(I-A(s))}{\mathcal{O}(s) \xi(s)}$.
    *   $\mathcal{O}(s)$ is an **Outer Function** chosen specifically to make $|J(1/2+it)| = 1$ a.e.
    *   Thus, $F(1/2+it)$ lies on the circle $|F/2| = 1$. Positivity of real part $\iff$ Phase of $J$ is in $[-\pi/2, \pi/2]$.

*   **The Wedge Logic (Quantitative)**:
    *   For every Whitney interval $I$, we bound the "windowed phase" $\int_I \phi (-w')$.
    *   **Lower Bound (Poisson Plateau)**: $\int \phi (-w') \ge c_0(\psi) \cdot \mu_{\text{balayage}}(Q(I))$.
        *   *Intuition*: Phase derivative picks up mass from zeros.
    *   **Upper Bound (CR-Green)**: $\int \phi (-w') \le C_{\text{test}} \sqrt{K_\xi} \sqrt{|I|}$.
        *   *Intuition*: Phase oscillation is controlled by the Dirichlet energy ($K_\xi$) of the field.
    *   **Closure**:
        *   Define dimensionless parameter $\Upsilon = \frac{\text{Upper}}{\pi \cdot \text{Lower}}$.
        *   If $\Upsilon < 1/2$, the phase oscillation is strictly smaller than the "width" of the wedge.
        *   Implies $\text{Re}(F) \ge 0$.

### Level 4: The Analytic Inputs (The "Engines")
**Goal**: Establish the Upper and Lower bounds.

*   **Engine A: Phase-Velocity Identity** (Links Geometry to Analysis)
    *   **Statement**: $-w'(t) = \pi \mu_{\text{zeros}} + \pi \sum m_\gamma \delta_\gamma$.
    *   *Meaning*: The derivative of the boundary phase is exactly the Poisson balayage of the off-critical zeros plus atoms at critical zeros.
    *   *Status*: Needs rigorous $\epsilon \to 0$ distributional convergence proof (**Gap G1**).

*   **Engine B: Carleson Energy Bound ($K_\xi$)** (The Number Theoretic Input)
    *   **Statement**: $\iint_{Q(I)} |\nabla \log \xi|^2 \sigma \, d\sigma dt \le K_\xi |I|$.
    *   **Requirement**: $K_\xi$ must be **finite** and **independent of $T$** (or sufficiently small).
    *   **Derivation**:
        1.  **Decomposition**: $\nabla \log \xi = \sum \frac{1}{s-\rho}$.
        2.  **Local**: Neutralize near zeros (Blaschke).
        3.  **Global**: Sum over annuli of zeros.
        4.  **Input**: **Vinogradov-Korobov (VK)** zero-density estimates.
            *   $\nu_k \ll (2^k L)^\theta$ (Strong bound needed to kill $\log T$ factor).
    *   *Status*: **Critical Gap (G2)**. Standard bounds give $\log T$ growth. Need rigorous VK derivation.

*   **Engine C: CR-Green Pairing** (The Functional Analysis)
    *   **Statement**: $\int \phi (-w') \approx \iint \nabla U \cdot \nabla V$.
    *   *Status*: Needs "length-free" bound for admissible windows to ensure constants don't blow up (**Gap G3**).

---

## II. Current Status of Verification

### 1. Formalized & Verified (Green)
*   **Pinch Logic**: The implication "PinchCertificate $\to$ RH" is formally proven in Lean.
*   **Outer Existence**: Construction of $\mathcal{O}$ with correct modulus is proven.
*   **Analytic Framework**: Definitions of J, F, Theta, and basic complex analysis properties are in place.
*   **Architecture**: The "if... then..." structure is sound and verified.

### 2. Stubbed / Placeholder (Red)
*   **Carleson Energy**: The bound `carleson_energy_bound` is currently proved using a trivial energy=0 placeholder.
*   **Zero Density**: `VK_annular_counts_exists` assumes an empty set of zeros.
*   **Phase-Velocity**: The identity is assumed as an axiom/hypothesis, not derived from the limit.
*   **CR-Green**: The inequality is derived from trivial 0-bounds.

### 3. The "Emptiness" Risk
*   **Concern**: Does a function $J$ exist that satisfies *both* the construction (from $\zeta$) *and* the bounds (Finite Carleson Energy)?
*   **Status**: Not proven empty, but not proven non-empty. This depends entirely on the **truth of the Carleson Bound for $\zeta$**.
    *   If VK estimates are strong enough $\implies$ Class is non-empty $\implies$ RH.
    *   If VK estimates are too weak (fundamental obstruction) $\implies$ Strategy fails (cannot close wedge).

---

## III. Finishing Strategy (The "Walk Forward")

1.  **Refactor Hypotheses**:
    *   Replace `sorry` and trivial stubs (0-energy) with explicit `Hypothesis` structures in Lean (e.g., `Hypothesis_Carleson_Bound`, `Hypothesis_Phase_Identity`).
    *   This makes the conditional proof honest and compilable.

2.  **Formalize G1 (Phase-Velocity)**:
    *   Prove the distributional limit $\epsilon \to 0$ for $-w'$.
    *   Show no singular inner factor appears (crucial for positivity).

3.  **Formalize G2 (Carleson from VK)**:
    *   **The Hardest Step**: Implement the derivation of $K_\xi$ from VK zero-density.
    *   Must rigorously show the sum over annuli converges to $O(|I|)$ and not $O(|I| \log T)$.

4.  **Execute the Trap**:
    *   Feed the constants from G2 into the Wedge inequality.
    *   Check if $\Upsilon < 1/2$.
