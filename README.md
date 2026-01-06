## Riemann: Lean 4 developments around the Riemann Hypothesis

This repository is a **monorepo of Lean 4 libraries** dedicated to the formalization of analytic number theory and the exploration of approaches to the Riemann Hypothesis (RH). The core library, `Riemann/` (umbrella import `Riemann.lean`), provides the initial infrastructure for several potential proof strategies:
*   **Classical Analytic Number Theory**: Euler products, functional equations, and Hadamard factorization.
*   **Complex Analysis & Operator Theory**: Hardy spaces, Nevanlinna theory, and de Branges spaces of entire functions.
*   **Harmonic Analysis**: Carleson measures, Whitney decompositions, and Poisson integrals on the half-plane.
*   **Statistical Mechanics**: Spin Glass theory, Guerra's interpolation, and applications to the Fyodorov-Hiary-Keating conjecture for the Riemann zeta function.
*   **Explicit Formulae**: The Weil explicit formula and the Selberg class (WIP).

This project is built on the Lean Project Template by Pietro Monticone (https://github.com/pitmonticone/LeanProject)

### Getting started

1. Install Lean 4 (version pinned by `lean-toolchain`)
2. Run `lake build Riemann` (build just the `Riemann` library)
3. Optionally run `lake build` (build all libraries in this monorepo)

### Top-level Lean libraries (root files)

- **`Riemann`** (`Riemann/`, `Riemann.lean`): The main library containing the RH-facing developments (detailed below).
- **`PrimeNumberTheoremAnd`** (`PrimeNumberTheoremAnd/`, `PrimeNumberTheoremAnd.lean`): A toolkit for the Prime Number Theorem.
- **`StrongPNT`** (`StrongPNT/`, `StrongPNT.lean`): A pipeline for a stronger form of the Prime Number Theorem.
- **`VD`** (`VD/`, `VD.lean`): Fragments of Value Distribution theory (Nevanlinna theory) being PRd to Mathlib.
- **`Carleson`** (`Carleson/`, `Carleson.lean`): Carleson’s theorem development.
- **`PhysLean`** (`PhysLean/`, `PhysLean.lean`): physics-oriented math library (independent of RH work).
- **`DeRhamCohomology`** (`DeRhamCohomology/`, `DeRhamCohomology.lean`): de Rham cohomology.
- **`GibbsMeasure`** (`GibbsMeasure/`, `GibbsMeasure.lean`): A general library for Gibbs measures and specification theory on infinite graphs, featuring **extensive novel development**.
- **`Notes/Papers`** (`Notes/`): research papers (by Connes-Consani, Tao, Radziwill-Bourdain, Arguin-Tai, etc) and ongoing research formalizations (see CW for some sorry-free research formalizations work including prerequisite theorems from other authors).

### The `Riemann/` library (main RH-facing code)

The `Riemann` library is structured into several layers, ranging from foundational analysis to high-level proof strategies.

#### 1. Academic Framework (`Riemann/academic_framework/`)
This layer establishes the analytic properties of the Riemann zeta function $\zeta(s)$ and the completed xi function $\xi(s)$.
*   **`CompletedXi.lean` & `ZetaFunctionalEquation.lean`**: Defines $\xi(s) = s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s)$ and proves the functional equation $\xi(s) = \xi(1-s)$.
*   **`HadamardFactorization.lean`**: A complete formalization of the Hadamard factorization theorem for entire functions of finite order, applied to $\xi(s)$ to relate its zeros to its growth.
*   **`GammaBounds.lean` & `StirlingBounds.lean`**: Precise estimates for the Gamma function in vertical strips, crucial for controlling the "archimedean factor" of L-functions.
*   **`EulerProduct/`**: Convergence of Euler products and prime series (`PrimeSeries.lean`), and bounds on the logarithmic derivative of zeta (`K0Bound.lean`).

#### 2. Certificates (`Riemann/Cert/`)
This layer bridges the gap between analytic estimates and formal verification, packaging bounds as "certificates" for use in the (RS) exploratory strategy.
*   **`K0PPlus.lean` & `KxiPPlus.lean`**: Prop-level interfaces for constants related to the distribution of zeros ($K_0, K_\xi$).
*   **`FactorsWitness.lean`**: Data structures witnessing the existence of factors in Hadamard products, facilitating explicit computations.

#### 3. Local Mathlib Extensions (`Riemann/Mathlib/`)
A comprehensive collection of general-purpose mathematical results developed for this project, filling gaps in Mathlib.
*   **Complex Analysis (`Analysis/Complex/`)**:
    *   **Hardy Spaces (`HardySpace.lean`)**: Theory of $H^p$ spaces on the unit disc, including boundary limits (Fatou's theorem TODO), inner-outer factorization, and the Poisson integral formula.
    *   **de Branges Spaces (`DeBranges/`)**: Hilbert spaces of entire functions, reproducing kernels, and their connection to Nevanlinna theory.
    *   **Nevanlinna Theory**: Cartan, characteristic functions, and proximity functions (`Cartan.lean`, `Nevanlinna.lean`).
    *   **Herglotz Representation**: (WIP) Representation of holomorphic functions with positive real part (`Herglotz.lean`).
*   **Harmonic Analysis (`Analysis/Harmonic/`)**:
    *   **BMO**: Bounded Mean Oscillation spaces and the John-Nirenberg inequality (`BMO/`).
    *   **Carleson Measures**: Definition and properties of Carleson measures (`Measure/Carleson/`), essential for embedding theorems.
*   **Special Functions**: Further development of the Gamma function and Gaussian integrals.
*   **Operator Theory**: Fredholm operators and determinants (`Analysis/Normed/Operator/Fredholm/`).

#### 4. RS Layer (`Riemann/RS/`)
This layer implements the "Boundary Wedge" strategy (or "pinch route"), a harmonic-analytic exploration to RH. It focuses on controlling the zeta function on the critical strip using boundary values and geometry.
*   **`Det2Outer.lean` & `HalfPlaneOuterV2.lean`**: Construction of outer functions on the half-plane to normalize the growth of zeta.
*   **`WhitneyGeometryDefs.lean`**: Whitney decomposition of the half-plane, used to discretize estimates.
*   **`PoissonKernelDyadic.lean`**: Dyadic estimates for the Poisson kernel.
*   **`CRGreenOuter.lean`**: Application of Green's theorem (Cauchy-Riemann identities) to relate bulk integrals to boundary terms.
*   **`BWP/` (Boundary Wedge Proof)**: Infrastructure for the "boundary wedge" argument, including Laplacian calculations (`Laplacian.lean`) and CR calculus (`CRCalculus.lean`).

#### 5. Semiclassical Analysis (`Riemann/Semiclassical/`)
*(Experimental)* Formalization of semiclassical symbol calculus, targeting spectral interpretations of the Riemann zeros.
*   **`Defs.lean`**: Definition of $\lambda$-dependent symbol classes $S^m_\lambda$.
*   **`TwoChart_Weyl*.lean`**: Weyl quantization and operator composition in a two-chart setting.
*   **`TwoChart_Parametrix*.lean`**: Construction of parametrices (approximate inverses) for semiclassical operators, including remainder bounds.

#### 6. Weil Explicit Formula (`Riemann/Weil/`)
*(Experimental)*
*   **`SelbergClass.lean`**: Definition of the Selberg class of L-functions (Dirichlet coefficients, analytic continuation, functional equation, Euler product).
*   **`ExplicitFormula.lean`**: The Weil explicit formula relating sums over zeros of an L-function to sums over primes, via a test function.

#### 7. Spin Glass Bridge (`Riemann/PhysLean/SpinGlass/`)
Formalization of the Sherrington-Kirkpatrick (SK) model and tools for analyzing disordered systems.
*   **`SKModel.lean`**: The Sherrington-Kirkpatrick model from statistical physics.
*   **`GuerraBound.lean`**: Formalization of Guerra's interpolation technique, a key tool for bounding the free energy of spin glasses.
*   **`ComplexIBP.lean`**: Gaussian Integration by Parts (Stein's Lemma) for complex variables.

#### 8. Research Formalizations (`Notes/Papers/`)
Formalization of results from recent research papers, including the connection between the Riemann zeta function and spin glass models (Fyodorov-Keating-Hiary conjectures).
*   **`CW/`** : Formalizations of the **Random Phase Model** for $\zeta(s)$.
    *   **`RandomPhaseModelMoments.lean`**: Analysis of the moments of the random phase model, establishing the connection to log-correlated fields.
    *   **`Lindeberg*.lean`**: Implementation of the Lindeberg exchange method to compare the statistics of the zeta function with the random model.
    *   **`ZetaSpinGlassDefs.lean`**: Definitions bridging number theoretic quantities with spin glass terminology.

### Build configuration

- **Lean version**: pinned by `lean-toolchain`
- **Build system**: Lake (`lakefile.toml`, `lake-manifest.json`)

### Contributing

You can contribute to this project by opening a PR or messaging us on Zulip at this link https://leanprover.zulipchat.com/#narrow/channel/116395-maths/topic/Repository.20for.20formalizations.20related.20.20to.20RH.2Fzeta/with/566242760.


### License

See `LICENSE`.
