# Riemann Hypothesis Formalization in Lean 4

A comprehensive formal verification project working toward a proof of the Riemann Hypothesis using the Lean 4 theorem prover.  This repository contains a substantial body of formalized mathematics spanning complex analysis, measure theory, harmonic analysis, and number theory.

## Project Overview

This project aims to formalize a proof of the Riemann Hypothesis through modern analytical techniques, building on work in de Branges theory, Nevanlinna theory, and harmonic analysis.

## Repository Structure

### Core Riemann Folder

The `Riemann/` directory contains the main formalization work organized into several major components:

#### Academic Framework (`Riemann/academic_framework/`)
The theoretical foundation including:
- **Euler Product Theory**: Prime series analysis and K0 bounds
- **Diagonal Fredholm Theory**: Determinant calculations and Weierstrass products
- **Zeta Function Theory**: Functional equations, completed zeta and xi functions
- **Special Functions**: Gamma function bounds, theta functions, disk Hardy spaces
- **Symmetry Properties**: CompletedXiSymmetry and domain theory
- **Compatibility Layers**: Compat module for integration with Mathlib

#### Certification (`Riemann/Cert/`)
Computational certificates and witness data:
- `KxiWhitney_RvM.lean`: Whitney decomposition certificates for the xi kernel
- `K0PPlus.lean`: Certification for K0 positive parts
- `KxiPPlus.lean`: Certification for Kxi positive parts
- `FactorsWitness.lean`: Witness data for factorization theorems

#### RS Module (`Riemann/RS/`)
Advanced analytic infrastructure for the Riemann-Siegel approach:

**Core Analysis**:
- `Cayley.lean`: Cayley transforms and conformal mappings
- `SchurGlobalization.lean`: Schur's lemma globalizations
- `Det2Outer.lean`: Determinant bounds and outer estimates
- `HalfPlaneOuterV2.lean`: Half-plane analysis (version 2)

**Poisson Kernel Theory**:
- `PoissonKernelAnalysis.lean`: Analytical properties of Poisson kernels
- `PoissonKernelDyadic.lean`: Dyadic decomposition techniques
- `PoissonPlateau.lean`: Plateau construction for Poisson kernels

**Whitney Decomposition**:
- `WhitneyGeometryDefs. lean`: Geometric definitions for Whitney decompositions
- `WhitneyAeCore.lean`: Core almost-everywhere properties
- `CRGreenWhitneyB.lean`: Cauchy-Riemann and Green function Whitney bounds

**Geometric Analysis**:
- `GField.lean`: Geometric field theory
- `WedgeBasics.lean`: Wedge domain fundamentals
- `PaperWindow.lean`: Window function constructions
- `AdmissibleWindows.lean`: Admissibility criteria for windows
- `BoundaryAi.lean`: Boundary analysis and AI techniques

**Bridge Theory**:
- `OffZerosBridge.lean`: Connection between zero-free regions
- `CRGreenOuter.lean`: Cauchy-Riemann Green outer bounds

##### BWP Submodule (`Riemann/RS/BWP/`)
Boundary value problem infrastructure:
- `Constants.lean`: Physical and mathematical constants
- `Definitions.lean`: Core BVP definitions
- `Laplacian.lean`: Laplacian operators and properties
- `CRCalculus.lean`: Cauchy-Riemann calculus
- `DiagonalBounds.lean`: Diagonal estimate bounds (commented)

#### Extended Mathlib (`Riemann/Mathlib/`)
Extensions and additions to Lean's mathematical library:

**Complex Analysis**:
- De Branges theory:
  - `DeBranges/Basic.lean`: Foundational definitions
  - `DeBranges/Space.lean`: De Branges spaces
  - `DeBranges/Zeros.lean`: Zero distribution theory
  - `DeBranges/Measure.lean`: Measure-theoretic aspects
  - `DeBranges/ReproducingKernel/Defs.lean`: Reproducing kernel definitions

**Nevanlinna Theory** :
- `DeBranges/Nevanlinna. lean`: Core Nevanlinna theory
- `DeBranges/NevanlinnaClosure.lean`: Closure properties
- `Nevanlinna/FilterLemmas.lean`: Filter-theoretic lemmas
- `Nevanlinna/MeasurabilityLemmas.lean`: Measurability results
- `Nevanlinna/PosLogLemmas.lean`: Positive logarithm properties
- `Nevanlinna/HarmonicBounds.lean`: Harmonic function bounds
- `Nevanlinna/CircleAverageLemmas.lean`: Circle averaging techniques
- `Nevanlinna/MinimumModulus.lean`: Minimum modulus theorems

**Harmonic Analysis**:
- `Analysis/Harmonic/AtomicDecomposition.lean`: Atomic decomposition theory
- `Analysis/Harmonic/BMO/Defs.lean`: BMO space definitions
- `Analysis/Complex/Cartan.lean`: Cartan theory

**Measure Theory**:
- `MeasureTheory/Covering/CalderonZygmund.lean`: Calderón-Zygmund covering lemmas
- `MeasureTheory/Function/BoundedSupport.lean`: Functions with bounded support
- `MeasureTheory/Function/LpMono.lean`: Lp space monotonicity
- `MeasureTheory/Function/MaximalFunction.lean`: Hardy-Littlewood maximal functions

**Special Functions & Calculus**:
- `Analysis/Calculus/TaylorIntegral.lean`: Taylor series with integral remainder
- `Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean`: Gaussian integration
- `ArctanTwoGtOnePointOne.lean`: Specific bounds for arctangent
- `Analysis/Complex/ConjugateReflection.lean`: Complex conjugation properties

#### Auxiliary (`Riemann/Aux. lean`)

#### Other Subdirectories
- `Riemann/Riemann/`: Nested Riemann-specific modules
- `Riemann/Weil/`: Weil explicit formula infrastructure
- `Riemann/PhysLean/`: Physics-inspired formalization techniques
- `Riemann/MeasureTheory/`: Additional measure theory
- `Riemann/Cert/`: Certification and verification data

### Supporting Projects

The repository also includes related external formalizations:
- **PrimeNumberTheoremAnd**: Prime Number Theorem and variations
- **StrongPNT**: Strong Prime Number Theorem
- **VD**: Value Distribution
- **Carleson**:  Carleson's theorem
- **DeRhamCohomology**: De Rham cohomology theory
- **PhysLean**: Physics-based mathematical structures

## Build Configuration

- **Lean Version**:  Specified in `lean-toolchain`
- **Build System**: Lake (Lean's package manager)
- **Configuration**: `lakefile.toml`
- **Dependencies**: `lake-manifest.json`

## Contributing

See `CONTRIBUTING.md` for contribution guidelines and `CODE_OF_CONDUCT.md` for community standards.

## Technical Infrastructure

- `.github/`: GitHub Actions and workflows
- `scripts/`: Build and utility scripts
- `customize_template.py`: Template customization
- `update. sh`: Update automation

## License

See `LICENSE` file for licensing information.

## Current Status

This is an active research project.  The formalization represents a substantial effort in formalizing advanced complex analysis, harmonic analysis, and number theory. Many components are complete, while some sections remain under development (tracked in the various progress documentation files).


## Getting Started

1. Install Lean 4 (version specified in `lean-toolchain`)
2. Clone this repository
3. Run `lake build` to compile the project
4. Explore the `Riemann/` directory for the main formalization
