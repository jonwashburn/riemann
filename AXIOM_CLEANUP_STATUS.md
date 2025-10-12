# Axiom Cleanup Status - Riemann Hypothesis Proof

**Last Updated**: 2025-10-12  
**Current Commit**: 1e66e55

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

### Step 4b–d: Numerical & Energy Wiring
**Status**: ✅ Complete  
- Numeric helpers are proved directly (`arctan_two_gt_one_point_one`, `pi_gt_314`, `upsilon_paper_lt_half`).
- `BoundaryWedgeProof.lean` integrates the concrete constants; `carleson_energy_bound` remains as an analytic axiom pending weighted VK bounds.

## 📋 Remaining Major Tasks (Steps 5-7)

### Step 5: Formalize `phase_velocity_identity`
**Status**: ⏳ Pending (one of two remaining BoundaryWedge axioms).  
**Goal**: Prove the CR-Green decomposition via Green’s identity and residue calculus.

### Step 6: Whitney Boundary Upgrade
**Status**: ⏳ Pending (`whitney_to_ae_boundary` still required).  
**Goal**: Combine constructive Whitney covering with measure-theory argument to conclude boundary positivity a.e.

### Step 7: Route B Packaging
**Status**: 🔴 Open (all remaining Route B axioms)  
**Axioms**: boundary positivity, measurability/analyticity, Poisson pullback, pinned removable data.  
**Goal**: Wire analytic/m measure properties using `Det2Outer`, `CompletedXi`, and Cayley utilities.

## Current Axiom Count

**Total Project Axioms**: 11 (down from 46)  
**Distribution**: `BoundaryWedgeProof.lean` (2), `RouteB_Final.lean` (9)  
**Build Status**: ✅ Lean files build inside `no-zeros/`; root-level build tooling still pending

## Next Session Priority

Focus on Route B analytic packaging and the two remaining boundary axioms.

