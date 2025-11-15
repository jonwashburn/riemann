d## Finishing Plan for Route B + Boundary Wedge Stack

This document captures the remaining work needed to restore a green build and complete the unconditional export of the Riemann Hypothesis proof. Tasks are ordered by dependency; each section lists prerequisites, success criteria, and verification steps.

---

### 1. Stabilize `RouteBPinnedRemovable.lean`

**Goal:** Rebuild the helper block and the isolating lemma so the file compiles end‑to‑end.

- **Geometry / Path Helpers**
  - Reintroduce `linePath_apply`, `linePath_re`, `linePath_im`, `linePath_mem_Ω`, `linePath_mem_XiDomain`, and the avoidance lemmas with the current ℝ-smul `linePath`.
  - Prove `joinedIn_to_two`, define `pathToTwo`, and show `XiDomain_isPathConnected`.
  - Verify all helper lemmas compile by running `lake build rh.RS.RouteBPinnedRemovable` up to the helper section.

- **`exists_isolating_preconnected_open` Rewrite**
  - Use the new path-connectivity fact plus `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`.
  - Hypotheses should be `(ρ ∈ Ω)` rather than `(ρ ∈ XiDomain)` and automatically exclude `ρ = 1` via `riemannZeta_one_ne_zero`.
  - Ensure the lemma produces an open, preconnected neighborhood avoiding `{1}` and isolating the zero.

- **Downstream Local Lemmas**
  - Update `Theta_pinch_analytic_on_Uminus`, `exists_u_trick_on_punctured`, and `pinned_removable_data` to match the new isolating lemma signature.
  - Confirm `pinned_removable_data` still only assumes the abstract `hRe` hypothesis (no hidden `(P+)`).

**Verification:** `lake build rh.RS.RouteBPinnedRemovable` succeeds with no warnings beyond existing Mathlib lint noise.

---

### 2. Re-run Route B Targets and Downstream Consumers

**Goal:** Ensure the Route B façade, certificate wrappers, and Proof export compile against the repaired pinned/removable layer.

- **Route B Final + Poisson AI**
  - Rebuild `rh.RS.RouteB_Final`, `rh.RS.PoissonAI`, and `rh.RS.PinchWrappers`. Fix any fallout from the new isolating lemma API.
  - Confirm `interior_positive_offXi` pulls the positivity hypothesis from `(P+)` rather than embedding it.

- **Certificate Construction**
  - Re-run `lake build rh.RS.CertificateConstruction` after Route B targets pass.
  - Ensure `xi_ext_zero_isolated_on_Ω` and `removable_extension_at_xi_zeros` consume the new isolating lemma helpers.

**Verification:** `lake build rh.RS.RouteB_Final`, `lake build rh.RS.CertificateConstruction`, and `lake build rh.Proof.Export` succeed.

---

### 3. Finish `BoundaryWedgeProof.lean`

**Goal:** Trim or reorder the remaining placeholder proofs so the wedge module compiles cleanly.

- Remove obsolete comments/axioms once the CR–Green and Poisson transport lemmas rest on the repaired Route B stack.
- Replace any surviving sorrys with proven lemmas or move the assumptions into clearly labeled theorems.
- Ensure imports align with the canonical `O` witness and no duplicate modules remain.

**Verification:** `lake build rh.RS.BoundaryWedgeProof` succeeds standalone, then re-run `lake build rh` for the full project.

---

### 4. Full Build & Final Checks

**Goal:** Demonstrate the entire proof path compiles from Lake, and record the toolchain.

- Run `lake clean; lake build rh`.
- Specifically build:
  - `rh.RS.RouteBPinnedRemovable`
  - `rh.RS.RouteB_Final`
  - `rh.RS.CertificateConstruction`
  - `rh.Proof.Export`
- Capture `elan show` and `git rev-parse HEAD` for reproducibility.

**Verification:** All targets succeed; document the command outputs (or CI logs) alongside this plan.

---

### 5. Optional Hardening

- Add regression tests or lint targets to ensure `RouteBPinnedRemovable` helpers stay intact (e.g., a small Lean test importing the geometry lemmas).
- Script CI checks that run the critical Lake targets before merging.
- Consider trimming `BoundaryWedgeProof` further to only export the minimum theorems needed upstream, reducing future merge pain.

---

**Status Tracking:** Use the existing TODO entries (`routeb-clean`, `convex-half`, `build`, etc.) to mark each phase:
1. Route B helper rebuild (`routeb-clean`, `convex-half`)
2. Downstream rebuild (`build`)
3. Boundary wedge trim
4. Full project build/tag

Update the TODO list after each phase completes so progress is clear for the next session.

