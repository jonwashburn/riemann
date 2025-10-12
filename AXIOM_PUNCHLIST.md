# Axiom Elimination Punchlist (Current)

**Total Axioms**: 11  
**Current Commit**: 1e66e55  
**Build Status**: ✅ `lake build` succeeds inside `no-zeros/`

---

## Tier 1: Critical Blockers (Must Eliminate for “Unconditional” Claim)

### 1.1 Phase-Velocity Identity
- **File**: `no-zeros/rh/RS/BoundaryWedgeProof.lean:773`
- **Status**: 🔴 Load-bearing – needed for wedge closure
- **Action**: Prove the CR-Green decomposition via Green’s identity, residue calculus, and the concrete `windowed_phase`, `poisson_balayage`, `critical_atoms` definitions.

### 1.2 Whitney Covering → A.E. Boundary
- **File**: `no-zeros/rh/RS/BoundaryWedgeProof.lean:845`
- **Status**: 🔴 Load-bearing – final step to transfer Whitney bounds to boundary positivity a.e.
- **Action**: Combine the constructive Whitney witness with the measure-theory upgrade.

### 1.3 Route B Packaging Axioms (9 total)
- **File**: `no-zeros/rh/RS/RouteB_Final.lean`
- **Status**: 🔴 Consolidated blocker – remaining analytics/measurability assumptions.
- **Axioms**:
  1. `boundary_positive_AF`
  2. `measurable_riemannXi_ext`
  3. `measurable_det2`
  4. `measurable_O`
  5. `det2_analytic_on_RSΩ`
  6. `det2_nonzero_on_RSΩ`
  7. `riemannXi_ext_analytic_AFΩ`
  8. `pullback_hasPoissonRepOn_offXi`
  9. `pinned_removable_data`
- **Action**: Wire these using existing `Det2Outer`, `CompletedXi`, Cayley adapters, and the OffZeros removable package.

---

## Tier 2: Completed Work (No Further Action)

- `CertificateConstruction.lean` – all axioms removed; removable extension and Cayley lemmas proved.
- `OffZerosBridge.lean` – `analyticOn_update_from_pinned` theorem in place.
- `WhitneyGeometryDefs.lean` – singleton witness `{univ}` supplies the covering interface.
- Numeric constants (`arctan_two_gt_one_point_one`, `pi_gt_314`, `upsilon_paper_lt_half`) proved constructively.

---

## Next Steps

1. Replace the nine Route B axioms with analytic/measurability proofs.
2. Prove `phase_velocity_identity` and `whitney_to_ae_boundary` inside `BoundaryWedgeProof.lean`.
3. Re-run `scripts/axiom_report.py`, refresh documentation, and prepare release artifacts once the axiom count hits zero.

