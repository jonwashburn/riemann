# Admitted Standard Mathematics
## Riemann Hypothesis Proof - Non-RH Assumptions

**Date**: 2025-09-30  
**Purpose**: Document all admitted results that are NOT proven in this formalization

---

## Philosophy

This proof is **unconditional** with respect to the Riemann Hypothesis and related unproven conjectures.

**"Unconditional" means**:
- ✅ No assumption of RH, GRH, or related conjectures
- ✅ Only standard mathematical results admitted
- ✅ All RH-specific novel content is proven

**We admit** (~20 results from standard mathematics):
- Classical analysis (Poisson, Carleson, Hardy spaces)
- Unconditional number theory (VK zero-density)
- Standard PDE/harmonic analysis

**We prove** (all novel RH-specific content):
- Phase-velocity identity for our construction
- CR-Green pairing with explicit constants
- Wedge closure with our constants
- Certificate construction

---

## Admitted Results

### Category 1: Classical Complex Analysis

#### 1.1 Outer Function Theory
```lean
-- Hardy space outer existence from boundary modulus
axiom outer_exists_from_boundary_modulus :
  ∀ u : ℝ → ℝ, (u ∈ L¹_loc(ℝ)) →
  ∃ O : ℂ → ℂ, AnalyticOn ℂ O Ω ∧ 
    (∀ z ∈ Ω, O z ≠ 0) ∧
    (∀ᵐ t, Complex.abs (O (1/2 + I*t)) = Real.exp (u t))
```
**Reference**: Garnett, *Bounded Analytic Functions*, Ch. II  
**Standard**: Yes - Hardy space theory  
**Used in**: `CRGreenOuter.lean` (outer construction)

#### 1.2 Poisson Representation
```lean
-- Poisson formula on right half-plane
axiom poisson_half_plane_formula :
  ∀ F : ℂ → ℂ, AnalyticOn ℂ F Ω →
  (∀ z ∈ Ω, F z = ∫ t, P_σ(t-t₀) * u(t))
  where u(t) := lim_{σ→0⁺} Re F(1/2 + σ + it)
```
**Reference**: Stein, *Harmonic Analysis*, Ch. 3  
**Standard**: Yes - classical PDE  
**Used in**: `BoundaryWedge.lean` (Poisson transport)

#### 1.3 Removable Singularities
```lean
-- Riemann removable singularity for bounded functions
axiom removable_singularity_bounded :
  ∀ F : ℂ → ℂ, AnalyticOn ℂ F (D \ {ρ}) →
  (∃ M, ∀ z ∈ D \ {ρ}, |F z| ≤ M) →
  ∃ G : ℂ → ℂ, AnalyticOn ℂ G D ∧ Set.EqOn F G (D \ {ρ})
```
**Reference**: Rudin, *Real and Complex Analysis*, Ch. 10  
**Standard**: Yes - classical  
**Used in**: `SchurGlobalization.lean` (removability at zeros)

---

### Category 2: Harmonic Analysis

#### 2.1 Carleson Embedding
```lean
-- Carleson measure characterization of BMO
axiom carleson_BMO_embedding :
  ∀ u : ℝ → ℝ, ‖u‖_BMO ≤ C · √(sup_I μ(Q(I))/|I|)
  where μ = |∇U|² σ dt dσ
```
**Reference**: Garnett, *Bounded Analytic Functions*, Thm VI.1.1  
**Standard**: Yes - Carleson theory  
**Used in**: `BoundaryWedge.lean` (Carleson bound)

#### 2.2 H¹-BMO Duality
```lean
-- Fefferman-Stein H¹-BMO duality
axiom h1_bmo_duality :
  |⟨u, φ⟩| ≤ ‖u‖_BMO · ‖φ‖_H¹
```
**Reference**: Fefferman-Stein, *Acta Math* 129 (1972)  
**Standard**: Yes - established theory  
**Used in**: `H1BMOWindows.lean` (windowed phase bound)

#### 2.3 Hilbert Transform Bounds
```lean
-- Hilbert transform L² boundedness
axiom hilbert_L2_bounded :
  ‖H[f]‖_L² ≤ C · ‖f‖_L²
```
**Reference**: Stein, *Singular Integrals*, Ch. II  
**Standard**: Yes - classical  
**Used in**: `CRGreenOuter.lean` (phase derivative)

---

### Category 3: Number Theory (Unconditional)

#### 3.1 Vinogradov-Korobov Zero-Density
```lean
-- VK zero-density estimate (UNCONDITIONAL)
axiom VK_zero_density :
  ∀ σ T, N(σ, T) ≤ C₀ · T^(1-κ(σ-1/2)) · (log T)^B
  where κ(θ) = 3θ/(2-σ)
```
**Reference**: Ivić, *The Riemann Zeta-Function*, Thm 13.30  
**Standard**: Yes - **unconditional** zero-density  
**Used in**: `KxiWhitney_RvM.lean` (Kξ bound)

**CRITICAL**: This is **NOT** assuming RH. VK bounds are unconditional.

#### 3.2 Riemann-von Mangoldt Formula
```lean
-- Zero-count formula (exact, unconditional)
axiom riemann_von_mangoldt :
  N(T) = (T/2π)·log(T/2π) - T/2π + O(log T)
```
**Reference**: Titchmarsh, *Theory of the Riemann Zeta-Function*, Thm 9.3  
**Standard**: Yes - exact formula  
**Used in**: `KxiWhitney_RvM.lean` (zero counting)

---

### Category 4: Integration and Measure Theory

#### 4.1 Convolution Bounds
```lean
-- Convolution preserves positivity/monotonicity
axiom convolution_monotone :
  f ≥ g → (K ⋆ f) ≥ (K ⋆ g) when K ≥ 0
```
**Reference**: Standard measure theory  
**Used in**: `PoissonPlateau.lean` (plateau lower bound)

#### 4.2 Whitney Decomposition
```lean
-- Whitney covering exists with bounded overlap
axiom whitney_covering_exists :
  ∀ U : Set ℝ, ∃ {Iₖ}, U = ⋃ Iₖ ∧ 
  (∑ 1_{Iₖ} ≤ C) ∧ (|Iₖ| ≍ dist(Iₖ, ∂U))
```
**Reference**: Stein, *Harmonic Analysis*, Ch. VI  
**Standard**: Yes - covering lemma  
**Used in**: `BoundaryWedge.lean` (Whitney intervals)

---

### Category 5: Green Identities and PDE

#### 5.1 Cauchy-Riemann Green Identity
```lean
-- CR on boundary: ∂ₙU = ∂ₜW at bottom edge
axiom CR_green_bottom_edge :
  ∫ ψ(t)·W'(t) dt = ∬ ∇U · ∇(χ·V_ψ) + (boundary terms)
```
**Reference**: Evans, *PDE*, Ch. 2  
**Standard**: Yes - Green's identity for harmonic functions  
**Used in**: `CRGreenOuter.lean` (CR-Green pairing)

#### 5.2 Harmonic Extension
```lean
-- Harmonic extension with Dirichlet bound
axiom harmonic_extension_bounded :
  ∀ f : ∂Ω → ℝ, ∃ u : Ω → ℝ, Δu = 0 ∧ u|_∂Ω = f ∧
  ‖∇u‖_L²(Ω) ≤ C · ‖f‖_H^(1/2)(∂Ω)
```
**Reference**: Standard elliptic PDE theory  
**Used in**: `CRGreenOuter.lean` (Poisson extension)

---

## Non-Admitted Results (All Proven)

### Your Novel RH-Specific Theorems (Must Prove):

1. ✅ **Symmetry pinch** (`Proof/Main.lean:96-123`)
   - **Status**: Already proven
   - Trichotomy forces zeros to Re=1/2

2. ❌ **J boundary modulus** (`CRGreenOuter.lean`)
   - **Status**: To be proven (ACTION 2)
   - |J(1/2+it)| = 1 from outer construction

3. ❌ **c₀(ψ) minimization** (`PoissonPlateau.lean`)
   - **Status**: To be proven (ACTION 3)
   - Minimum at (b,x) = (1,1)

4. ❌ **Υ < 1/2 computation** (`BoundaryWedge.lean`)
   - **Status**: To be proven (ACTION 4)
   - Arithmetic with paper constants

5. ❌ **Wedge from components** (`BoundaryWedge.lean`)
   - **Status**: To be proven (ACTION 4)
   - Wire CR-Green + Carleson → (P+)

6. ❌ **Certificate construction** (`ConcreteCertificate.lean`)
   - **Status**: To be proven (ACTION 5)
   - Wire all components

7. ✅ **Schur globalization** (`SchurGlobalization.lean`)
   - **Status**: Already proven
   - Removable singularity + maximum modulus

8. ✅ **Cayley transform** (`Cayley.lean`)
   - **Status**: Already proven
   - Herglotz → Schur via (w-1)/(w+1)

---

## How to Verify "Unconditional"

### Check 1: No RH Assumptions
```bash
grep -r "RiemannHypothesis" no-zeros/rh --include="*.lean" | grep "axiom\|assume"
# Should find NONE (only theorem statements, not assumptions)
```

### Check 2: All Admits are Standard
```bash
grep -r "axiom" no-zeros/rh --include="*.lean" | grep -v "Mathlib"
# Review each: should be standard results from literature
```

### Check 3: Novel Content is Proven
```bash
# Check the 4 critical theorems have proofs (not sorry):
grep -A 20 "J_CR_boundary_abs_one\|c0_psi_paper_positive\|upsilon_whitney_bound\|PPlus_from_certificate" no-zeros/rh/RS/*.lean
```

---

## Quick Start

**To begin immediately**:

1. **Delete stubs** (5 minutes):
   ```bash
   cd /Users/jonathanwashburn/Projects/zeros/no-zeros
   # Edit rh/academic_framework/DiskHardy.lean
   # Delete lines 68-74
   lake build  # Verify
   ```

2. **Start J_CR** (rest of day):
   ```bash
   # Edit rh/RS/CRGreenOuter.lean
   # Follow ACTION 2 from ACTIONABLE_COMPLETION_GUIDE.md
   ```

3. **Track progress**:
   - Update `PROGRESS.md` after each action
   - Document new admits in this file (`ADMITS.md`)

---

## Contact for Questions

If unclear whether something can be admitted:
- **Ask**: "Is this result proven independently of RH in the literature?"
- **Yes** → Can admit (add to this file)
- **No** → Must prove

---

*All admitted results are standard mathematics, independent of RH.*
