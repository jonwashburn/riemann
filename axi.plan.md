# Axiom Elimination Basis (For AI Agents)

Remaining axioms: 11 (all other modules are axiom-free).

- `no-zeros/rh/RS/BoundaryWedgeProof.lean`: `phase_velocity_identity`, `whitney_to_ae_boundary`.
- `no-zeros/rh/RS/RouteB_Final.lean`: `boundary_positive_AF`, `measurable_riemannXi_ext`, `measurable_det2`, `measurable_O`, `det2_analytic_on_RSΩ`, `det2_nonzero_on_RSΩ`, `riemannXi_ext_analytic_AFΩ`, `pullback_hasPoissonRepOn_offXi`, `pinned_removable_data`.

## Mission Outline

### BoundaryWedgeProof.lean
- **Prove `phase_velocity_identity`**: use Green’s identity on Whitney rectangles, residue calculus for `critical_atoms`, and the concretely defined `windowed_phase`, `poisson_balayage`, `critical_atoms`.
- **Prove `whitney_to_ae_boundary`**: combine the constructive Whitney cover (`WhitneyGeometryDefs`) with measure-theoretic arguments to obtain boundary positivity almost everywhere.

### RouteB_Final.lean
- **Boundary positivity (`boundary_positive_AF`)**: derive from the proven wedge closure and PPlus machinery.
- **Measurability**: show ξ_ext, det₂, and the chosen outer function are measurable by leveraging their continuity/analyticity.
- **Analytic/nonvanishing witnesses**: expose the existing theorems from `Det2Outer` and `CompletedXi` for det₂ and ξ_ext on the RS/AF domains.
- **Cayley Poisson pullback (`pullback_hasPoissonRepOn_offXi`)**: transport the Poisson representation via `HalfPlaneOuterV2` and Cayley adapters.
- **Pinned removable data (`pinned_removable_data`)**: package the OffZeros removable builder with the Route B outer witness, ensuring the u-trick conditions.

### Finalization Checklist
- [ ] Replace all 11 axioms with formal proofs.
- [ ] Run `lake build` (from `no-zeros/`) and `scripts/axiom_report.py` to confirm zero project-local axioms.
- [ ] Update documentation (`AXIOM_PUNCHLIST.md`, `AXIOM_CLEANUP_STATUS.md`, `STANDARD_AXIOMS_CATALOG.md`) after the proofs land.

Agents may introduce helper lemmas or files as needed; keep public interfaces stable and document classical references (Koosis, Stein, Iwaniec–Kowalski) in comments for clarity.
