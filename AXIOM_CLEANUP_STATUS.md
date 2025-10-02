# Axiom Cleanup Status - Riemann Hypothesis Proof

**Last Updated**: 2025-10-02  
**Current Commit**: d73580e

## ✅ Completed (Steps 1-3)

### Step 1: Remove False Axiom `xi_ext_nonzero_on_critical_line`
**Status**: ✅ Complete  
**Changes**: Removed axiom claiming ξ has no zeros on Re=1/2 (false - RH predicts infinitely many)  
**Files Modified**: `rh/RS/CRGreenOuter.lean`

### Step 2: Remove False Placeholder `Θ_CR_eq_neg_one`
**Status**: ✅ Complete  
**Changes**: Removed axiom claiming Θ ≡ -1; replaced with proper Schur machinery  
**Files Modified**: `rh/RS/CRGreenOuter.lean`, `rh/Proof/Main.lean`

### Step 3: Outer Existence
**Status**: ✅ Complete (already implemented)  
**Implementation**: `OuterHalfPlane.ofModulus_det2_over_xi_ext_proved` in `rh/RS/Det2Outer.lean`  
**Note**: Provides explicit witness; no axiom needed

## 🚧 In Progress (Step 4: CR-Green + Carleson)

### Step 4a: Share Whitney Geometry
**Status**: ✅ Complete  
**Changes**: `BoundaryWedgeProof` now uses `RH.Cert.WhitneyInterval`

### Step 4b: Define Concrete Windowed Phase/Energy
**Status**: ⏳ Pending  
**Goal**: Replace placeholder `windowed_phase` with actual CRGreen construction  
**Approach**: Use `pairing_whitney_analytic_bound` from `CRGreenOuter.lean` with concrete U=Re log ξ

### Step 4c: Remove `carleson_energy_bound` Axiom
**Status**: ⏳ Pending  
**Goal**: Use `ConcreteHalfPlaneCarleson` budget instead of axiom  
**Approach**: Apply `sqrt_boxEnergy_from_Carleson_on_whitney`

### Step 4d: Update `Kxi_paper` Constant
**Status**: ⏳ Pending  
**Goal**: Reference actual Carleson constant instead of literal 0.16  
**Approach**: Extract from `FunctionalEquationStripFactors.B` or Kξ witness

## 📋 Remaining Major Tasks (Steps 5-7)

### Step 5: Formalize `phase_velocity_identity`
**Current**: Axiom stating `windowed_phase = π·(balayage + atoms)`  
**Goal**: Prove CR-Green decomposition from Green's identity  
**Effort**: Medium (requires IBP + harmonic analysis)

### Step 6: Prove Whitney/Poisson Transport
**Axioms to Remove**:
- `whitney_to_ae_boundary`: Whitney covering → a.e. boundary positivity
- `poisson_transport_interior`: Boundary (P+) → interior positivity

**Goal**: Formalize standard covering theory + Poisson integral formula  
**Effort**: Medium (standard but detailed)

### Step 7: Removability and Outer Transfer
**Axioms to Remove**:
- `removable_extension_at_xi_zeros`: Bounded Schur → removable singularity
- `outer_transfer_preserves_positivity`: Inner factor preserves positivity

**Goal**: Apply mathlib complex analysis removability theorems  
**Effort**: Low (mostly packaging existing mathlib)

## Current Axiom Count

**Total Project Axioms**: ~28 (down from 32)  
**Critical Blockers**: 8 (phase_velocity_identity, CR bounds, Whitney/Poisson, removability)  
**Numerical/Calculus**: ~18 (low priority, verifiable)  
**Build Status**: ✅ Passing with 1 sorry (measure-zero technical gap)

## Next Session Priority

Continue Step 4b: wire concrete windowed phase through CRGreen machinery to enable Steps 4c-4d.

