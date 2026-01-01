## Riemann: Lean 4 developments around the Riemann Hypothesis

This repository is a **monorepo of Lean 4 libraries**. The main RH-facing library is `Riemann/`
(umbrella import `Riemann.lean`), which develops analytic-number-theory infrastructure
supporting several proof “routes” (Euler products, Hardy/Nevanlinna/de Branges theory,
Carleson/Whitney/Poisson machinery, semiclassical symbol calculus, and an explicit-formula track).

### Getting started

1. Install Lean 4 (version pinned by `lean-toolchain`)
2. Run `lake build Riemann` (build just the `Riemann` library)
3. Optionally run `lake build` (build all libraries in this monorepo)

### Top-level Lean libraries (root files)

- **`Riemann`** (`Riemann/`, `Riemann.lean`): main RH development (see below).
- **`PrimeNumberTheoremAnd`** (`PrimeNumberTheoremAnd/`, `PrimeNumberTheoremAnd.lean`): PNT/Hadamard/complex-analysis toolkit used by some RH routes.
- **`StrongPNT`** (`StrongPNT/`, `StrongPNT.lean`): Strong PNT pipeline (umbrella imports are partially gated/commented).
- **`VD`** (`VD/`, `VD.lean`): value-distribution/Nevanlinna fragments.
- **`Carleson`** (`Carleson/`, `Carleson.lean`): Carleson’s theorem development (includes many “ToMathlib” lemmas).
- **`PhysLean`** (`PhysLean/`, `PhysLean.lean`): physics-oriented math library (independent of RH work).
- **`CReals`** (`CReals/`, `CReals.lean`): computable reals (proof layer + fast executable layer).
- **`DeRhamCohomology`** (`DeRhamCohomology/`, `DeRhamCohomology.lean`): de Rham cohomology.
- **`GibbsMeasure`** (`GibbsMeasure/`, `GibbsMeasure.lean`): Gibbs measures / specification theory.
- **`Notes`** (`Notes/`): research notes and scratch formalizations (not meant as a stable library entry point).

### The `Riemann/` library (main RH-facing code)

- **Entry points**
  - **`Riemann.lean`**: umbrella import for the *maintained* `Riemann.*` modules (it intentionally avoids obvious backups/duplicates).
  - **`Riemann/Aux.lean`**: small shared lemmas/glue used across the library.
  - **`Riemann/Example.lean`**: lightweight examples / sanity checks.

- **Academic framework (`Riemann/academic_framework/`)**: “AF” layer (Euler products, functional equations, determinant/outer scaffolding).
  - **`Compat.lean`**: compatibility/shims for integrating with Mathlib conventions used in this repo.
  - **`Domain.lean`**: standard domains (notably the half-plane `Re > 1/2`) and helper lemmas.
  - **`CompletedXi.lean`**: the completed xi function `riemannXi_ext` and its basic analytic interface.
  - **`CompletedXiSymmetry.lean`**: symmetry/functional-equation packaging for `xi`.
  - **`ZetaFunctionalEquation.lean`**: functional equation for zeta / completed zeta.
  - **`ZetaFiniteOrder.lean`**: finite-order statements needed for Hadamard-style arguments.
  - **`FiniteOrder.lean`**: shared finite-order infrastructure used by multiple AF modules.
  - **`HadamardFactorization.lean`**: Hadamard factorization scaffolding for the RH-facing functions.
  - **`Theta.lean`**: theta-function infrastructure used in completion/functional equations.
  - **`DiskHardy.lean`**: Hardy-space-on-the-disc utilities used in analytic factorization.
  - **`MeasureHelpers.lean`**: small measure-theory helpers used by RS/AF glue.
  - **`StirlingBounds.lean`** / **`StirlingB.lean`** / **`GammaStirlingAux.lean`**: Stirling/Gamma auxiliary bounds used in archimedean estimates.
  - **`GammaBounds.lean`**: archimedean `Γ_ℝ` bounds (Deligne normalization) and strip-level derivative interfaces.
  - **`WeierstrassFactorBound.lean`**: quantitative bounds for Weierstrass factors/products.
  - **Euler products (`Riemann/academic_framework/EulerProduct/`)**
    - **`PrimeSeries.lean`**: prime-indexed series and convergence tools.
    - **`K0Bound.lean`**: the `K0` arithmetic-tail bound on strips (as a Prop-level interface).
  - **Diagonal/Fredholm (`Riemann/academic_framework/DiagonalFredholm/`)**
    - **`WeierstrassProduct.lean`**: infinite-product / Weierstrass-product helpers (Euler-factor expansions).
    - **`Determinant.lean`**: the det₂ Euler product (2-modified determinant) and its basic interface.
    - **`AnalyticInfrastructure.lean`**: analytic lemmas used by the determinant/outer pipeline.
  - **Notes**: files like `GammaBounds'.lean`, `DiagonalFredholm/Determinant-old.lean`, `DiagonalFredholm/Determinant'.lean`,
    and `DiagonalFredholm/Determinant''.lean` are **historical/experimental variants** and are not imported by `Riemann.lean`.

- **Certificates (`Riemann/Cert/`)**: “data + bounds” packaged as propositions for the RS layer.
  - **`K0PPlus.lean`**: exposes availability of the `K0` bound from the AF layer.
  - **`KxiPPlus.lean`**: Prop-level interface for a `Kξ` Carleson-box constant.
  - **`KxiWhitney.lean`**: basic Whitney interval/type infrastructure used throughout RS.
  - **`KxiWhitney_RvM.lean`**: statement-level route from short-interval zero counts (RvM/VK shape) to a `Kξ` bound.
  - **`FactorsWitness.lean`**: witness data used by factorization-style theorems.

- **RS layer (`Riemann/RS/`)**: half-plane Poisson/Whitney/Carleson machinery and glue for the “pinch route”.
  - **`SchurGlobalization.lean`**: RS-specialized Schur-function interface (with notes pointing to consolidated Mathlib-style lemmas).
  - **`Det2Outer.lean`**: RS alias `det2` and Prop-level “outer normalizer” interface on `Ω = {Re > 1/2}`.
  - **`HalfPlaneOuterV2.lean`**: outer-function interface on the half-plane (boundary parametrization, modulus matching, Poisson transport).
  - **`Cayley.lean`**: Cayley transform wrapper building a Schur function `Θ` from a field `J`.
  - **`PoissonKernelAnalysis.lean`**: minimal Poisson-kernel helper lemmas used by dyadic bounds.
  - **`PoissonKernelDyadic.lean`**: dyadic separation lemmas and Schur-type bounds for Poisson kernels.
  - **`PoissonPlateau.lean`**: a concrete plateau/window with a uniform Poisson-smoothing lower bound.
  - **`WhitneyGeometryDefs.lean`**: Whitney boxes/tents definitions in the half-plane and associated “box energy”.
  - **`WhitneyAeCore.lean`**: `(P+)` predicate and an a.e. boundary-positivity façade shared across RS modules.
  - **`CRGreenWhitneyB.lean`**: Prop-level CR–Green pairing interface (numeric Poisson–gradient hypothesis → pairing control).
  - **`CRGreenOuter.lean`**: CR–Green outer “exports” and the analytic steps used to turn identities into bounds.
  - **`GField.lean`**: defines the reciprocal field `G := (O·ξ_ext)/det₂` and its off-zero domain on `Ω`.
  - **`WedgeBasics.lean`**: WhitneyInterval-flavoured wrappers around dyadic separation lemmas.
  - **`PaperWindow.lean`**: a lightweight, axiom-free definition of the “paper window” `ψ`.
  - **`AdmissibleWindows.lean`**: Prop-level definition of admissible windows (with “holes”) used in RS bookkeeping.
  - **`BoundaryAi.lean`**: RS-level wrappers around the AF boundary Poisson approximate-identity (AI) interface.
  - **`OffZerosBridge.lean`**: non-circular “off-zeros” bridge wiring `Θ/N` style identities without assuming zeta nonvanishing on `Ω`.
  - **`VKStandalone.lean`**: algebraic scaffolding for VK-style zero-density hypotheses and locked constants.
  - **`Audit.lean`**: running audit/status note of unresolved analytic placeholders in the boundary-wedge pipeline.
  - **BWP submodule (`Riemann/RS/BWP/`)**: boundary-wedge “proof infrastructure”.
    - **`Constants.lean`**: paper constants and the arithmetic verification `Υ < 1/2`.
    - **`Definitions.lean`**: basic definitions used throughout the boundary-wedge development.
    - **`Laplacian.lean`**: Laplacian/Hessian/harmonic-function API on finite-dimensional real inner product spaces.
    - **`CRCalculus.lean`**: CR-calculus lemmas (mixed partials, Fréchet-derivative form of CR identities).
    - **`DiagonalBounds.lean`**: diagonal/Schur-row control and related bookkeeping for the wedge route.

- **Semiclassical (`Riemann/Semiclassical/`)**: semiclassical symbol calculus (TwoChart Egorov / parametrix pipeline).
  - **`Defs.lean`**: defines the λ-dependent symbol class `SmLambda` (Japanese bracket, mixed derivatives, closure under multiplication).
  - **`TwoChart_Sm.lean`**: additional symbol-class API and bookkeeping layers.
  - **`TwoChart_SmLambda.md`**: documentation for the `SmLambda` layer and how the paper’s hypotheses are encoded.
  - **`TwoChart_Pn.lean`**: Weyl/Moyal bidifferential coefficients `Pₙ` and closure `Pₙ : S^{m₁}×S^{m₂} → S^{m₁+m₂−n}`.
  - **`TwoChart_Parametrix*.lean`**: parametrix recursion, truncation, cancellation, remainder-symbol bounds, and smoothness upgrades.
  - **`TwoChart_NeumannSeries.lean`**: Neumann-series packaging used in invertibility steps.
  - **`TwoChart_Weyl*.lean`**: semiclassical Weyl kernel/operator wrappers and kernel estimates (Schur-test-friendly setup).

- **Weil explicit-formula track (`Riemann/Weil/`)**: Selberg-class scaffolding and explicit-formula definitions.
  - **`SelbergClass.lean`**: definition of the Selberg class (Dirichlet coefficients, continuation, FE, Euler product).
  - **`ExplicitFormula.lean`**: definitions for a Weil test function and the “spectral vs geometric side” structure.
  - **`ResidueSum.lean`**: residue-theorem/rectangle-integral infrastructure for summing over zeros.
  - **Notes**: `ExplicitFormula_new.lean` and `SelbergClass'.lean` are **experimental variants**.

- **Spin-glass bridge (`Riemann/PhysLean/SpinGlass/`)**: SK model and Gaussian IBP infrastructure (used for probabilistic/physics-flavoured routes).
  - **`Defs.lean`**: core SK configuration/energy space and thermodynamic quantities (`Z`, free energy, overlaps).
  - **`SKModel.lean`**: random Hamiltonians/disorder structures compatible with Hilbert-space Gaussian IBP.
  - (Other files in this folder are documentation (`*.md`) and additional lemmas; see the directory.)

- **Extra MeasureTheory (`Riemann/MeasureTheory/`)**
  - **`ParametricDominatedConvergence.lean`**: a parametric dominated-convergence lemma specialised for this development.

- **Local Mathlib extensions (`Riemann/Mathlib/`)**: project-local additions organised in a Mathlib-like directory tree.
  - **Complex analysis**: Hardy spaces (`Analysis/Complex/HardySpace*`), de Branges/Nevanlinna files (`Analysis/Complex/DeBranges/...`), Schur functions, Herglotz kernel.
  - **Harmonic analysis**: BMO and good-λ infrastructure (`Analysis/Harmonic/...`).
  - **Measure theory**: Carleson integration utilities, maximal function, CZ covering (`MeasureTheory/...`).
  - **Probability**: Gaussian integration-by-parts and distribution infrastructure (`Probability/Distributions/...`).
  - **Linear algebra**: Toeplitz matrices and positivity (`LinearAlgebra/Matrix/...`).
  - **Notes**: files named `*Backup.lean`, `*.bak`, or `*'.lean` are typically **snapshots/experiments**.

### Build configuration

- **Lean version**: pinned by `lean-toolchain`
- **Build system**: Lake (`lakefile.toml`, `lake-manifest.json`)

### Contributing

See `CONTRIBUTING.md` and `CODE_OF_CONDUCT.md`.

### Repository tooling

- **CI / workflows**: `.github/`
- **Scripts**: `scripts/`
- **Template tooling**: `customize_template.py`
- **Update script**: `update.sh`

### License

See `LICENSE`.
