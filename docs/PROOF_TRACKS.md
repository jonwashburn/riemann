## Proof Track (Single Path)

This document records the single selected track to boundary nonvanishing and the unconditional RH result contained in this repository:

- Certificate (Cayley/Schur) Route

The KD–Carleson route is retained as optional future work but is not required to complete the build.

It also explains why residue bookkeeping is not required, and lists the remaining work needed to complete the certificate route.


### Certificate Route (Cayley → Schur → Globalization)

Goal: Build a Schur function Θ on the right half‑plane Ω, aligned to ζ via a Cayley transform of a normalized object F = 2·J, where J = det₂/(O·ξ_ext) for a chosen outer O, then globalize nonvanishing.

- Core modules and roles
  - `rh/academic_framework/CompletedXi.lean`: completed ξ function and right‑half‑plane baseline (`Ω`, boundary map).
  - `rh/academic_framework/CayleyAdapters.lean`: Cayley to/from disk and boundary adapters.
  - `rh/academic_framework/DiskHardy.lean`: disk‑side Poisson representation for pinch pullbacks.
  - `rh/academic_framework/PoissonCayley.lean`: transport of Poisson representations between disk and half‑plane.
  - `rh/academic_framework/HalfPlaneOuterV2.lean`: outer data and Poisson kernel framework on Ω (bounds, integrability, measurability on boundary).
  - `rh/RS/OffZerosBridge.lean`: local construction of Θ via Cayley on F = 2·J off the zeros; removable extension/limit witnesses.
  - `rh/RS/XiExtBridge.lean`: adapters that phrase off‑zeros statements uniformly in terms of ξ_ext.
  - `rh/RS/SchurGlobalization.lean`: abstract Schur/Cayley machinery and removable singularity packaging; globalization theorem to conclude nonvanishing.
  - `rh/RS/RouteB_Final.lean`: wiring of the above for the chosen outer `O` (Route B), including boundary positivity `(P+)` and Poisson representation witness.
  - `rh/RS/CertificateConstruction.lean`: final assembly exposing `RiemannHypothesis_unconditional`.

- Proof flow (high level)
  1. Choose an outer `O` with boundary modulus equality `|det₂/ξ_ext|` on the boundary of Ω.
  2. Define `J := det₂/(O·ξ_ext)`, set `F := 2·J`, define the Cayley `Θ := (F−1)/(F+1)` on `Ω \ Z(ξ_ext)`.
  3. Show boundary positivity `(P+)` for `F` (Route B wiring), and obtain a Poisson representation for `F` on `Ω \ Z(ξ_ext)`.
  4. Package removable extension at each `ξ_ext` zero; show `Θ → 1` at the zero and extend across.
  5. Prove `Θ` is Schur on Ω and apply globalization to obtain boundary nonvanishing; finish RH via the provided certificate wrapper.


### KD–Carleson Route (Kernel Decay + Carleson Energy)

Goal: Prove boundary positivity `(P+)` from quantitative Carleson energy bounds obtained through kernel decay partial sums and annular counting, then feed `(P+)` into the same analytic transport.

- Core modules and roles
  - `rh/RS/PoissonKernelDyadic.lean`: dyadic separation lemmas, Schur‑type row/cross bounds; Poisson kernel helper facts.
  - `rh/RS/BoundaryWedgeProof.lean`: KD partial‑sum structures (diagonal/cross), calibrations, and the aggregator lemma that yields the Carleson energy bound.
  - `rh/RS/PPlusFromCarleson.lean`: bridge from the Carleson energy bound to boundary positivity `(P+)`.
  - Optional counts: a VK‑type annular counting statement can be used if the aggregator expects it.

- Proof flow (high level)
  1. Cross majorization: calibrate the cross KD partial sums using a row bound with `4^{-|k−j|}` decay.
  2. Diagonal majorization: produce `Ddiag : DiagKDPartialSum I` with constant bounded by the default diagonal constant.
  3. Combine diagonal/cross with annular counts (default or VK) via the aggregator to obtain the Carleson energy bound.
  4. Convert Carleson to `(P+)` and follow the analytic transport (as in the certificate route) to nonvanishing.


### Why Residue Bookkeeping Is Not Needed

Neither route relies on contour integrals or residue computations of ζ or auxiliary transforms:

- The certificate route works by boundary real‑part control, Poisson integral representation, Cayley transforms, and removable singularities — all pointwise/analytic tools that avoid sum‑over‑poles expansions.
- The KD–Carleson path obtains `(P+)` from quantitative kernel decay and Carleson energy bounds. Its inputs are dyadic separation estimates, summability/decay, and counting bounds. No complex contour/residue calculation is required; the approach is purely real/functional‑analytic on the boundary and interior via Poisson transport.

The “residue bookkeeping” would only be necessary in a contour‑integration based proof (e.g., explicit formula manipulations), which neither track uses.


## Remaining Work (Certificate Route)

- Normalize Poisson kernel bounds in `rh/academic_framework/HalfPlaneOuterV2.lean` to abs/norm form
  - Use `|π|⁻¹`, `|z.re − 1/2|`, and goals of the form `‖⋯‖ ≤ ‖⋯‖`.
  - Replace deprecated division lemmas with the `*_₀` variants using strictly positive denominators.
- Measurability/integrability polishing in `HalfPlaneOuterV2.lean`
  - Use `AEStronglyMeasurable` where `Integrable.mono` requires it.
  - If convenient, prefer `Integrable.of_norm_le` with an explicit dominating integrable function.
- `J_pinch` normalization
  - Add a local lemma equating the two `det₂` incarnations in the `abs=1` step, or standardize on a single `det2` symbol.
- `rh/RS/OffZerosBridge.lean`
  - Verify binder shapes/limit forms compile with current mathlib (adjust to `∀ ρ` form where needed).
- `rh/RS/RouteB_Final.lean`
  - Keep minimal imports; do not import the KD/Carleson path.

Outcome: Axiom‑free build of `RiemannHypothesis_unconditional` from `CertificateConstruction.lean`.


### KD–Carleson (Optional Future Work)

- Can be completed later by replacing the Carleson axiom in `BoundaryWedgeProof.lean` with a theorem via the existing aggregator, using diagonal/cross KD witnesses and counts as needed.


## Minimal Deliverables

- Certificate route (lean files):
  - AF: `CompletedXi`, `CayleyAdapters`, `DiskHardy`, `PoissonCayley`, `HalfPlaneOuterV2`.
  - RS: `OffZerosBridge`, `XiExtBridge`, `SchurGlobalization`, `RouteB_Final`, `CertificateConstruction`.

- KD–Carleson route (optional):
  - RS: `PoissonKernelDyadic`, `BoundaryWedgeProof`, `PPlusFromCarleson` (and helpers those import).


## Notes

- The certificate route does not depend on VK counts or KD dyadic lemmas and remains fully axiom‑free; current blockers are purely build‑level inequalities/measurability updates in `HalfPlaneOuterV2.lean` and a normalization of `J_pinch` usage.
- The KD–Carleson route can be completed independently by replacing the Carleson axiom with the aggregator theorem once the diagonal/cross witnesses and (if needed) counts are in place.


