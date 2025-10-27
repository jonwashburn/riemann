## Proof Track (Active)

- Entry: `rh/Proof/Active.lean`
  - Final export: `RH.Proof.Final.RiemannHypothesis_mathlib_from_pinch_ext_assign`
  - Core steps:
    - `RH_core` symmetry
    - `GlobalizeAcrossRemovable` (Schur pinch)
    - `RiemannHypothesis_from_pinch_ext_assign`

## Unconditional Export (Route B)

- Route: `rh/RS/RouteB_Final.lean`
  - Poisson rep on off-zeros; boundary positivity (P+)
  - Isolating neighborhoods; pinned u-trick; removable update
  - Certificate build: `buildPinchCertificate`
  - Conclusion: `RiemannHypothesis_via_RouteB`

- Export: `rh/Proof/Export.lean`
  - `@[simp] theorem RiemannHypothesis_unconditional : RiemannHypothesis`

### θ‑free Route B (Dev Target)

- Goal: keep the bridge θ‑free in the AF layer and wire Route B without any Greek-`Θ` identifiers in dev modules.

- Owning modules (by layer):
  - RS layer (pinch pipeline)
    - `rh/RS/WhitneyAeCore.lean`: `(P+)` facade and canonical outer choice.
    - `rh/RS/PinchWrappers.lean`: package (P+), Poisson transport, pinned‑removable into certificate builders.
    - `rh/RS/Det2Outer.lean`: `det2`, outer witness typeclass/utilities.
    - `rh/RS/OffZerosBridge.lean`: off‑zeros helpers.
    - `rh/RS/PinchCertificate.lean`: `PinchCertificateExt` and final glue.
    - `rh/RS/RouteB_Final.lean`: θ‑free wiring; imports AF bridge only.
  - AF layer (θ‑free bridge)
    - `rh/academic_framework/HalfPlaneOuterV2.lean`: domain `Ω`, `boundary`, `F_pinch`, `J_pinch`,
      `BoundaryPositive`, `HasPoissonRepOn`, `poissonIntegral`, `poissonTransportOn`,
      `ExistsOuterWithModulus` (and basic bounds/measurability).
    - `rh/academic_framework/CayleyAdapters.lean`: `toDisk`, `fromDisk`, `boundaryToDisk`,
      pullback lemma `pullback_rep_on_from_halfplane_rep` (AF-only, θ‑free).
    - `rh/academic_framework/PoissonCayley.lean`: θ‑free Cayley bridge API:
      `EqOnBoundary`, `CayleyKernelTransportOn`, `reEq_on_from_disk_via_cayley`,
      `cayley_kernel_transport_from_rep_on`, `pinch_halfplane_ReEqOn_from_cayley`,
      `pinch_ReEqOn_from_pullback`, `pullback_rep_on_from_halfplane_rep`.
    - `rh/academic_framework/CompletedXi.lean`: completed ξ function `riemannXi_ext`.
    - `rh/academic_framework/ConstructiveOuter.lean`: axioms‑free outer existence witness
      (may use a Greek name internally; not part of dev θ‑free scan roots).

- Minimal AF API consumed by `RouteB_Final.lean`:
  - From `HalfPlaneOuterV2`: `Ω`, `boundary`, `offXi`, `F_pinch`, `J_pinch`,
    `BoundaryPositive`, `HasPoissonRepOn`, `poissonTransportOn`,
    `ExistsOuterWithModulus`, `boundary_abs_J_pinch_eq_one`.
  - From `CayleyAdapters`: `toDisk`, `fromDisk`, `boundaryToDisk`,
    `pullback_rep_on_from_halfplane_rep` (bridge helper).
  - From `PoissonCayley`: `EqOnBoundary`, `pinch_halfplane_ReEqOn_from_cayley`,
    `pinch_ReEqOn_from_pullback` (subset Poisson → half‑plane Re‑identity).
  - From `CompletedXi`: `riemannXi_ext` and basic measurability/differentiability facts.

- Import DAG (dev target focus)

```
rh/academic_framework/CompletedXi.lean      ┐
                                            ├→ rh/academic_framework/HalfPlaneOuterV2.lean
rh/RS/Det2Outer.lean                        ┘            ↑
                                                         │
rh/academic_framework/DiskHardy.lean  → rh/academic_framework/CayleyAdapters.lean
                                                         │
                        rh/academic_framework/PoissonCayley.lean
                                                         │
                 {RS layer: WhitneyAeCore, PinchWrappers, PinchCertificate}
                                                         │
                                rh/RS/RouteB_Final.lean
```

Dev scan roots (θ‑free):
- `rh/academic_framework/PoissonCayley.lean`
- `rh/academic_framework/HalfPlaneOuterV2.lean`
- `rh/academic_framework/CayleyAdapters.lean`

#### Dev guard and how to run it

The θ‑free dev guard ensures the AF bridge and everything it transitively imports are free of the following tokens: `sorry`, `admit`, `axiom`, `theta` (case‑insensitive).

- Build target: if present, `rh_routeb_dev` is built first; otherwise the guard proceeds without it.
- Scan scope: starts at the θ‑free AF roots above and follows `import rh.*` lines to collect all transitive Lean files, then scans them.
- Failure mode: emits offending `file:line:content` entries and exits non‑zero.

Run:

```bash
cd riemann/no-zeros
./verify_proof.sh
```

What it does in addition to the main proof checks:
- Builds `rh_routeb_dev` if available.
- Scans the transitive closure from the θ‑free AF roots for `sorry|admit|axiom|theta`.
- Fails with clear diagnostics if any are found.

## How to verify

```bash
cd riemann/no-zeros
./verify_proof.sh
```

- What it does:
  - Builds the active track and checks axioms on the active theorem.
  - Best‑effort checks the unconditional export.
  - Scans the active modules for `sorry`/`admit`/`axiom`.
  - Scans θ‑free dev roots above for `sorry`/`admit`/`axiom` and for any Greek `Θ` identifiers; fails if found.


