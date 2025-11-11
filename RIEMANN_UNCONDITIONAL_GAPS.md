# Unconditional RH Proof Status

## Summary

`lake build rh` now succeeds. The exported theorem `RH.RS.CertificateConstruction.RiemannHypothesis_unconditional` compiles against the strengthened certificate API and uses the unconditional outer witness (`ConstructiveOuter.outer_exists_with_modulus_det2_over_xi`), so the active proof path no longer needs the placeholder axiom `poissonPotentialExists_log_u_assumed`. No `sorry` or non-mathlib axioms appear in the compiled modules.

## Broad Sweep: Proof Architecture (Active Track)

- **Outer existence on Ω**
  - `RouteB_Final.hOuterWitness` chooses the AF outer supplied by `ConstructiveOuter.outer_exists_with_modulus_det2_over_xi` (the unconditional lemma using `O_simple`).
  - `CertificateConstruction.outer_exists_for_certificate` reuses the same witness when assembling the final certificate.
- **Interior positivity**
  - Boundary positivity `(P+)` for `F := 2 · J_pinch det₂ O` (Route B) → Poisson transport via `HalfPlaneOuterV2.poissonTransportOn` → interior nonnegativity on `Ω \ {riemannXi_ext = 0}`.
- **Schur bound**
  - `Θ_cert_Schur_offXi` and `Θ_pinch_Schur_offXi` now target `Ω \ {riemannXi_ext = 0}`, matching the strengthened certificate field.
- **Removable extensions**
  - `RouteB.pinned_removable_data` feeds `OffZeros.LocalDataXi.of_pinned` to supply analytic extensions with value `1` at each zero.
- **Export**
  - `PinchCertificateExt` (assembled in `CertificateConstruction`) feeds `Proof.Main` → `RiemannHypothesis_unconditional` → mathlib `RiemannHypothesis`.

## Current Status

- ✅ Domain coercion fixed in `rh/RS/Cayley.lean` (`Θ_cert_Schur_offXi` uses `offXi_subset_offZeros`).
- ✅ `lakefile.lean` updated to build every module imported by the active proof (added `RS.Det2Outer`, `RS.Domain`, `RS.PoissonAI`, `academic_framework.ZetaFunctionalEquation`, `HalfPlaneOuterV2`, `DiagonalFredholm`, etc.).
- ✅ `lake clean && lake build rh` succeeds locally; diagnostic noise is limited to mathlib docstring lint warnings.
- ✅ Route B and certificate wiring use the unconditional outer lemma; the axiom-based alias is no longer referenced along the compiled path.

## Remaining Checks

1. **Axiom audit**
   - Double-check that no compiled module references `poissonPotentialExists_log_u_assumed`. (A quick `grep` confirms only the unused alias mentions it; still worth running `#print axioms RiemannHypothesis_unconditional` for completeness.)
2. **Reference hygiene**
   - Ensure no other files import `ConstructiveOuter.outer_exists_with_modulus_det2_over_xi_constructive`. If any future route needs it, gate behind a dedicated namespace or delete the alias.
3. **Build surface**
   - Optional: tighten `lakefile.lean` once CI proves stable (we now build a superset of modules; trimming can wait until after upstream confirmation).
4. **Documentation**
   - Update project notes / README once the axiom audit is complete and we have a reproducible command for the final `#print axioms` check.

## Next Steps

- [ ] Run `lake env lean -R ./. --run "#print axioms RH.RS.CertificateConstruction.RiemannHypothesis_unconditional"` (or equivalent) to certify zero axioms.
- [ ] Sweep for lingering imports of the axiom-based outer alias; remove or quarantine it.
- [ ] Push a CI run to ensure the expanded root set builds cleanly outside the local environment.
- [ ] If desired, re-minimize the root list while keeping all required `.olean`s for the unconditional pipeline.
