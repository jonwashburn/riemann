<!-- 026aed4d-daad-47ce-adf4-57d3b1bf6e45 9cd79fa8-7a96-4980-9bc7-c16576a40a05 -->
# Axiom Elimination Status (Current)

- `no-zeros/rh/RS/CertificateConstruction.lean` and `no-zeros/rh/RS/OffZerosBridge.lean` are axiom-free; outer witnesses, removable extensions, and Cayley helpers are fully wired.
- Numeric lemmas (`arctan_two_gt_one_point_one`, `pi_gt_314`, `upsilon_paper_lt_half`) are proved in `BoundaryWedgeProof.lean`.
- `whitney_decomposition_exists` now has a constructive witness `{univ}`.
- Remaining axioms (11 total) live only in:
  - `no-zeros/rh/RS/RouteB_Final.lean` (9) – boundary positivity, measurability/analyticity, Poisson pullback, pinned data.
  - `no-zeros/rh/RS/BoundaryWedgeProof.lean` (2) – `phase_velocity_identity`, `whitney_to_ae_boundary`.

## Next Actions

1. Replace Route B packaging axioms with proofs (measurability, Poisson pullback, pinned removable data, boundary positivity).
2. Formalize `phase_velocity_identity` and `whitney_to_ae_boundary` inside `BoundaryWedgeProof.lean`.
3. Run `lake build` from `no-zeros/`, regenerate `scripts/axiom_report.py`, and update status docs.
4. Prepare final release artifacts once the axiom count hits zero.

## Checklist

- [x] Packaging and numeric axioms eliminated in CertificateConstruction / OffZerosBridge.
- [x] Removability and Hardy infrastructure wired where needed.
- [x] Whitney decomposition witness supplied.
- [ ] Route B transport and measurability axioms discharged.
- [ ] CR-Green phase/Whitney boundary proofs formalized.
- [ ] Final documentation refresh and release prep.

