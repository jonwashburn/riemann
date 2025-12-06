# Hard Analysis Roadmap: Completing the Analytic Core

This document enumerates the specific "hard analysis" tasks required to replace the remaining placeholders in the Hardy/Schur RH proof. These are non-trivial mathematical results that must be formalized to make the proof unconditional.

## 1. Analytic Number Theory (The VK Hypothesis)

The `VKZeroDensityHypothesis` is currently an input assumption. To discharge it, we need to formalize the classical Vinogradov-Korobov zero-density estimates.

- [ ] **Formalize `Littlewood-Jensen`**: Prove the lemma relating zero counts in a rectangle to the integral of `log|ζ|` on the boundary (Jensen's formula adaptation).
- [ ] **`IntegralLogPlusBoundVK`**: Prove the specific integral bound `∫ log⁺|ζ(σ+it)| dt ≪ T^{1-κ(σ)}` using the VK exponential sum bounds (Ford's version or similar).
- [ ] **Zero-Free Region**: Formalize the specific VK zero-free region `σ ≥ 1 - c / (log t)^{2/3}` to handle the "near" zeros.
- [ ] **Annular Count Derivation**: Prove that the integral bounds imply the discrete `N(σ, T)` bounds required by `Zk_card_from_hyp`, specifically the geometric decay across annuli.

**Target File**: `riemann/analytic_number_theory/VinogradovKorobov.lean` (and new supporting files).

## 2. Geometric Function Theory (CR-Green Pairing)

The `CRGreen_window_bound_real` theorem relies on a stubbed pairing lemma. We need to prove the Green's identity for the specific geometry of Whitney tents.

- [ ] **Green's Identity on Tents**: Prove `∫_I φ (-w') = ∬_Q ∇U · ∇(χV) + boundary_terms` for harmonic functions on the Whitney tent domain.
- [ ] **Test Function Estimates**: Prove that the Poisson extension `V_φ` of an admissible window `φ` satisfies the Dirichlet energy bound `||∇(χV_φ)||_2 ≤ C * sqrt(|I|)` uniformly in `I`.
- [ ] **Boundary Term Control**: Show that the "side" and "top" boundary terms in the Green's identity vanish or are negligible due to the cutoff function `χ`.
- [ ] **Outer Cancellation**: Formalize the argument that `U` can be replaced by `U - Re log O` in the energy integral without changing the pairing (relying on `Re log O` being the harmonic extension of the boundary difference).

**Target File**: `riemann/Riemann/RS/BWP/CRCalculus.lean` (and potentially a new `CRGreenPairing.lean`).

## 3. Harmonic Analysis (Wedge Closure)

The `PPlus_from_Carleson_impl` theorem relies on a "local-to-global" principle. We need to prove that small average phase deviation implies pointwise positivity.

- [ ] **Local-to-Global Wedge Lemma**: Prove that if `∫_I φ (-w') ≤ ε` for all Whitney intervals `I` (normalized by length), then `w(t)` stays within a cone `[-θ, θ]` for almost every `t`, where `θ` depends on `ε`.
- [ ] **Poisson Plateau Lower Bound**: Formalize the bound `∫_I φ (-w') ≥ c₀ * μ(Q(I))` where `μ` is the measure of off-line zeros. This links the phase integral to the existence of zeros.
- [ ] **Contradiction Argument**: Combine the upper bound (from Carleson) and lower bound (from Plateau) to show that if `ε` is small enough, `μ` must be the zero measure.

**Target File**: `riemann/Riemann/RS/BWP/WedgeVerify.lean` (or `riemann/Riemann/RS/PPlusFromCarleson.lean`).

## 4. Mellin/Theta Backend (Archimedean Factors)

The `academic_framework` files contain `sorry`s for standard but messy integral identities.

- [ ] **Gaussian Integrals**: Close the 19 `sorry`s in `MellinThetaZeta.lean` related to Fourier transforms of Gaussians and specific contour shifts.
- [ ] **Theta Transformation**: Complete the proof of the functional equation for `θ` (Jacobi identity) in Lean.
- [ ] **Gamma Factors**: Prove the specific Stirling-formula bounds for `Γ(s)` used to control the "trivial" Archimedean energy contributions.

**Target File**: `riemann/Riemann/academic_framework/MellinThetaZeta.lean` & `GammaBounds.lean`.

## 5. Complex Analysis Glue (Pinned/Removability)

The "pinch" argument relies on extending the Schur function across zeros.

- [ ] **Removability at Zeros**: Prove that if `Θ` is bounded and `Θ → 1` at a point `ρ` (a zero of `ξ`), then `ρ` is a removable singularity and `Θ(ρ) = 1`.
- [ ] **Interior Positivity**: Prove the "Poisson transport" lemma: if `Re F ≥ 0` on the boundary and `F` is sufficiently nice at infinity, then `Re F ≥ 0` in the half-plane.

**Target File**: `riemann/Riemann/RS/SchurGlobalization.lean` (and `OffZerosBridge.lean`).

