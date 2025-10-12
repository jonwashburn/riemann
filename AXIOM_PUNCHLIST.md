# Axiom Elimination Punchlist

**Total Axioms**: 46  
**Current Commit**: 9a71cdd  
**Build Status**: ✅ Passing

---

## Tier 1: Critical Blockers (Must Eliminate for "Unconditional" Claim)

### 1.1 Interior Positivity — Resolved
**Now**: Proven in `rh/RS/BoundaryWedgeProof.lean` (Section 7)
```lean
theorem interior_positive_J_canonical : ∀ z ∈ Ω, 0 ≤ ((2 : ℂ) * J_canonical z).re
```
is derived by:
- `PPlus_from_constants` (Whitney → a.e. boundary positivity), and
- `poisson_transport_interior_off_zeros` (HalfPlaneOuterV2 transport on Ω \ {ξ = 0}),
closing zeros by direct evaluation of `J_canonical`.

**Status**: ✅ **Derived (no axiom)**  
**References**: `BoundaryWedgeProof.lean:616–685`  
**Action**: Remove from axiom list

---

### 1.2 Phase-Velocity Identity  
**File**: `rh/RS/BoundaryWedgeProof.lean:213`
```lean
axiom phase_velocity_identity :
  ∀ I : WhitneyInterval,
    windowed_phase I = Real.pi * poisson_balayage I + Real.pi * critical_atoms I
```
**Status**: 🔴 **Load-bearing** - needed for wedge closure  
**Real Fix**: Prove CR-Green decomposition from Green's identity + boundary traces  
**Requires**:
- Actual implementation of `windowed_phase` (not placeholder)
- Actual implementation of `poisson_balayage` (harmonic measure integral)
- Actual implementation of `critical_atoms` (sum over zeros)
- Green's identity on Whitney rectangles
- Boundary trace formulas

**Effort**: 1-2 weeks of focused work  
**Priority**: **CRITICAL**

---

### 1.3 Whitney Covering → A.E. Boundary
**File**: `rh/RS/BoundaryWedgeProof.lean:271`
```lean
axiom whitney_to_ae_boundary :
  (∀ I : WhitneyInterval, c0_paper * poisson_balayage I ≤ C_psi_H1 * sqrt (Kxi_paper * (2 * I.len))) →
  (∀ᵐ t : ℝ, 0 ≤ ((2 : ℂ) * J_CR outer_exists (boundary t)).re)
```
**Status**: 🔴 **Load-bearing** - final wedge step  
**Real Fix**: Formalize Whitney decomposition + a.e. upgrade  
**Reference**: Stein, Harmonic Analysis Ch. VI  
**Effort**: 3-5 days  
**Priority**: **CRITICAL**

---

### 1.4 Poisson Transport to Interior — Resolved
**Now**: Implemented via `RH.AcademicFramework.HalfPlaneOuterV2.poissonTransport` and `poissonTransportOn`.

`BoundaryWedgeProof.lean` uses the Route B witness
`RH.RS.RouteB.F_pinch_has_poisson_rep` to obtain subset transport and derive
interior positivity off zeros, then closes at zeros.

**Status**: ✅ **Implemented (no axiom in project)**  
**References**: `BoundaryWedgeProof.lean:616–656`

---

### 1.5 Removable Singularities
**File**: `rh/RS/CertificateConstruction.lean:69`
```lean
axiom removable_extension_at_xi_zeros :
  ∀ (O_witness : ∃ O, OuterHalfPlane O ∧ BoundaryModulusEq O ...),
  ∀ ρ ∈ Ω → riemannXi_ext ρ = 0 →
    ∃ (U : Set ℂ), ... ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ ...
```
**Status**: 🟡 **Standard** - Riemann removable singularity theorem  
**Real Fix**: Apply mathlib's `AnalyticOn` removability lemmas  
**Effort**: 2-3 days  
**Priority**: **MEDIUM** (cleanest to start with)

---

### 1.6 Outer Transfer Preserves Positivity
**File**: `rh/RS/CertificateConstruction.lean:88`
```lean
axiom outer_transfer_preserves_positivity :
  ∀ (F O1 O2 : ℂ → ℂ),
  (∀ z ∈ Ω, 0 ≤ (F z / O1 z).re) →
  (∀ᵐ t, |O1 (boundary t)| = |O2 (boundary t)|) →
  (∀ z ∈ Ω, 0 ≤ (F z / O2 z).re)
```
**Status**: 🟡 **Standard** - Hardy space inner/outer factorization  
**Real Fix**: Prove from Hardy theory (outer unique up to inner factor with |·|=1)  
**Effort**: 2-4 days  
**Priority**: **MEDIUM**

---

## Tier 2: Analytic Infrastructure (Standard but Not in Mathlib)

### 2.1 CR-Green Upper Bound
**File**: `rh/RS/BoundaryWedgeProof.lean:171`
```lean
axiom CR_green_upper_bound :
  ∀ I : WhitneyInterval,
    |windowed_phase I| ≤ C_psi_H1 * sqrt (carleson_energy I)
```
**Status**: 🟡 **Standard** - Cauchy-Schwarz on CR-Green pairing  
**Real Fix**: Prove from Green's identity + Hölder inequality  
**Effort**: 3-5 days (after `windowed_phase` is real)  
**Priority**: **MEDIUM**

### 2.2 Carleson Energy Bound
**File**: `rh/RS/BoundaryWedgeProof.lean:151`
```lean
axiom carleson_energy_bound :
  ∀ I : WhitneyInterval,
    carleson_energy I ≤ Kxi_paper * (2 * I.len)
```
**Status**: 🟡 **Standard** - from Vinogradov-Korobov zero density  
**Real Fix**: Bind VK zero-density estimates explicitly  
**Effort**: 2-3 days  
**Priority**: **MEDIUM**

### 2.3 Poisson Balayage (Definition)
**File**: `rh/RS/BoundaryWedgeProof.lean:141`
```lean
axiom poisson_balayage : WhitneyInterval → ℝ
```
**Status**: 🟠 **Needs Implementation**  
**Real Fix**: Define as `∫_I ψ(t) · (harmonic_measure at t) dt`  
**Effort**: 2-3 days  
**Priority**: **MEDIUM**

### 2.4 Critical Atoms  
**File**: `rh/RS/BoundaryWedgeProof.lean:207`  
**Status**: 🟠 **Needs Implementation**  
**Real Fix**: Sum over zeros with residue weights  
**Effort**: 3-5 days  
**Priority**: **MEDIUM**

### 2.5 Outer Existence
**File**: `rh/RS/CRGreenOuter.lean:110`
```lean
axiom outer_exists : OuterOnOmega
```
**Status**: ✅ **Already implemented** in `rh/RS/Det2Outer.lean`!  
**Real Fix**: Just need to wire it (replace axiom with the theorem)  
**Effort**: 30 minutes  
**Priority**: **HIGH** (easy win)

---

## Tier 3: Numerical/Calculus (Verifiable/Computable)

### 3.1 Numerical Constants (3 axioms)
- `arctan_two_gt_one_point_one` 
- `arctan_le_pi_div_two`
- `pi_gt_314`

**Status**: 🟢 **Trivial** - can prove with `norm_num` or interval arithmetic  
**Effort**: 1-2 hours total  
**Priority**: **LOW** (but easy wins)

### 3.2 Upsilon Computation
**File**: `rh/RS/BoundaryWedgeProof.lean:89`
```lean
axiom upsilon_paper_lt_half : Upsilon_paper < 1 / 2
```
**Status**: 🟢 **Computable** - pure arithmetic  
**Effort**: 2-4 hours (needs careful interval arithmetic)  
**Priority**: **LOW**

### 3.3 Window Calculus (27 axioms in PoissonPlateauNew.lean)
- Beta smoothness, integrals
- S_step properties  
- psi_paper smoothness/evenness
- Poisson formulas
- Arctan derivative identities
- Monotonicity results

**Status**: 🟢 **Standard calculus** - provable from mathlib  
**Effort**: 1-2 weeks total  
**Priority**: **LOW** (polish work)

---

## Recommended Attack Order (Realistic)

### Phase 1: Easy Wins (1 week)
1. ✅ Wire `outer_exists` (30 min)
2. ✅ Prove numerical constants (2 hours)
3. ✅ `removable_extension_at_xi_zeros` (2-3 days)
4. ✅ `outer_transfer_preserves_positivity` (2-3 days)

**Impact**: Eliminate 5-6 axioms with real work

### Phase 2: Transport Layer (2 weeks)
5. ✅ `poisson_transport_interior` (connect existing Poisson machinery)
6. ✅ `whitney_to_ae_boundary` (formalize covering lemma)

**Impact**: Eliminate 2 critical axioms

### Phase 3: CR-Green Core (3-4 weeks)
7. ✅ Implement real `poisson_balayage` 
8. ✅ Implement real `critical_atoms`
9. ✅ Prove `phase_velocity_identity` from Green's identity
10. ✅ Prove Carleson bounds from VK

**Impact**: Eliminate the phase-velocity axiom

### Phase 4: Derive Interior Positivity (1 week)
11. ✅ With all above done, derive `interior_positive_J_canonical` from the pipeline

**Impact**: **Proof becomes truly unconditional!**

### Phase 5: Polish (1-2 weeks)
12. ✅ Formalize window calculus axioms
13. ✅ Computational verification of constants

**Impact**: Zero axioms (fully within mathlib)

---

## Total Realistic Estimate

**Minimum**: 8-10 weeks focused work  
**Conservative**: 3-6 months  

Each axiom needs **real mathematical content**, not shortcuts.

---

## Starting Point for Next Session

**Easiest real win**: Wire `outer_exists` (it's already implemented, just needs connection)

```lean
-- In rh/RS/CRGreenOuter.lean, replace:
axiom outer_exists : OuterOnOmega

-- With:
def outer_exists : OuterOnOmega := 
  let h := OuterHalfPlane.ofModulus_det2_over_xi_ext_proved
  { outer := OuterHalfPlane.choose_outer h
  , analytic := (OuterHalfPlane.choose_outer_spec h).1.analytic
  , nonzero := (OuterHalfPlane.choose_outer_spec h).1.nonzero
  , boundary_modulus := (OuterHalfPlane.choose_outer_spec h).2 }
```

This is **real progress** - actually eliminating an axiom by connecting to existing code.

