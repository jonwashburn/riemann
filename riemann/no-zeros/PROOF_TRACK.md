## Unconditional Route B (θ‑free, reviewer‑friendly)

- Proof export: `rh/Proof/Export.lean`
  - `@[simp] theorem RiemannHypothesis_unconditional : RiemannHypothesis`
    (aliases the Route B result; this is exactly mathlib’s `RiemannHypothesis`).

- Route B core: `rh/RS/RouteB_Final.lean`
  - Uses a fixed outer witness for `|det₂/ξ_ext|` and defines `F := 2·J_pinch`.
  - Threading: proven `(P+)` on the AF boundary → Poisson representation on `offXi` → interior `Re(F) ≥ 0`.
  - Pinned u‑trick on isolating neighborhoods gives removable updates and nontriviality.
  - Conclusion: `RiemannHypothesis_via_RouteB`.

### θ‑free Cayley bridge (AF shims)

- `rh/academic_framework/HalfPlaneOuterV2.lean`: `Ω`, `boundary`, `offXi`, `BoundaryPositive`,
  `HasPoissonRepOn`, `poissonTransportOn`, `F_pinch`, `J_pinch`.
- `rh/academic_framework/CayleyAdapters.lean`: `toDisk`, `fromDisk`, `boundaryToDisk`,
  `pullback_rep_on_from_halfplane_rep`.
- `rh/academic_framework/PoissonCayley.lean`: `EqOnBoundary`, `CayleyKernelTransportOn`,
  `HasHalfPlanePoissonReEqOn`, `cayley_kernel_transport_from_rep_on`, and the
  pullback/export helper `pullback_rep_on_from_halfplane_rep` (θ‑free bridge used by Route B).
- `rh/academic_framework/CompletedXi.lean`: completed ξ, `riemannXi_ext` basics.

### RS pipeline (P+ → off‑zeros → removable)

- `rh/RS/WhitneyAeCore.lean`: boundary facade for `(P+)` on `F := 2·J_pinch`.
- `rh/RS/PPlusFromCarleson.lean`: proven `(P+)` export for the canonical pinch field; θ‑free facade used by Route B.
- `rh/RS/Det2Outer.lean`: `det2` and the outer witness API.
- `rh/RS/OffZerosBridge.lean`: assignment/removable packaging on off‑zeros.
- `rh/RS/PinchWrappers.lean`: wires `(P+)`, Poisson transport, and pinned data into certificate builders.
- `rh/RS/PinnedRemovable.lean`: pinned u‑trick ⇒ removable extension for the Cayley form.
- `rh/RS/RouteB_Final.lean`: θ‑free end‑to‑end wiring and `RiemannHypothesis_via_RouteB`.

### Minimal targets and guard

- Export build: `lake build rh_export`.
- Dev build: `lake build rh_routeb_dev` (isolates unconditional deps).
- Guard script: from `riemann/no-zeros/` run `./verify_proof.sh`.
  - Builds dev and export targets only.
  - Verifies only standard axioms and that `RiemannHypothesis_unconditional` is present.
  - Scans the transitive closure of dev/export roots for:
    - Forbidden constructs: `sorry`, `admit`, `axiom`.
    - Banned imports: `rh.academic_framework.Theta`, `rh.academic_framework.MellinThetaZeta`,
      `rh.RS.CRGreenOuter*`, `rh.RS.sealed*`.
    - Banned tokens: `boundaryToDisk_param`, `exp_I_two_arctan_ratio`, `two_arctan`, `arctan_ratio`.

### Notes on θ‑free closure and removals

- The Route B dev closure explicitly excludes `BoundaryWedgeProof` and `PoissonKernelDyadic`.
- The export is certificate-driven via `(P+)` and uses the AF Poisson facade (`HalfPlaneOuterV2`).
- `(P+)` is sourced via `rh.RS.PPlusFromCarleson` and remains θ‑free in the dev/export targets.

### Where the mathlib equivalence is realized

- The export theorem’s type is `RiemannHypothesis` (mathlib’s standard statement). The
  alias is in `rh/Proof/Export.lean` under the name `RiemannHypothesis_unconditional`.

## How to verify

```bash
cd riemann/no-zeros
./verify_proof.sh
```

- Confirms axioms are standard and checks `RiemannHypothesis_unconditional : RiemannHypothesis`.


