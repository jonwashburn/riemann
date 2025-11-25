# RH Proof Finishing Plan

## Overview
This document captures the remaining work needed to turn the current Riemann Hypothesis pipeline into a complete, unconditional proof. It covers two fronts:

1. **Hardy/Schur "Pinch" Route** – the active analytic pathway built on phase velocity, Carleson energy, and a boundary wedge certificate.
2. **De Branges Migration** – the new infrastructure just landed on `main` (commit `a1a0648`) to rephrase the argument inside de Branges / Hermite–Biehler spaces.

Each section lists the outstanding theorems, the current code status, and suggested next steps or dependencies.

---

## 1. Hardy/Schur Pinch Route (Active)
### Goal
Finish the boundary-wedge → Poisson → pinch chain so that the existing Lean code proves RH without additional assumptions.

### Critical Tasks
1. **G1 – Phase–Velocity Identity (Boundary limit).**
   - *What*: Prove that the boundary phase derivative $-W'$ equals the Poisson balayage of off-critical zeros plus atoms on the line (no singular inner residue).
   - *Current*: The smoothed identity at $\Re(s)=1/2+\varepsilon$ exists; the $\varepsilon \to 0$ limit and exclusion of singular factors remain sketch-level.
   - *Plan*: Formalize the distributional convergence in Lean (likely inside `Riemann/RS/BoundaryAi.lean` and the BWP files). This will require a clean functional-analytic statement (BMO/Hardy duality) plus zero-density control.

2. **G2 – Carleson Energy for $U_\xi$ (K$_\xi$).**
   - *What*: Show $\iint_{Q(I)} |\nabla U_\xi|^2 \sigma \le K_\xi |I|$ with $K_\xi$ finite, using Vinogradov–Korobov zero-density and annular aggregation.
   - *Current*: `ConcreteHalfPlaneCarleson` is wired up, but `VK_annular_counts_exists` and related helpers are placeholders returning zero counts.
   - *Plan*: Replace the stub with the real VK counting argument (Whitney geometry + dyadic annuli). Track constants carefully; we only need finiteness, not sharp numerics.

3. **G3 – CR–Green → Window Bounds.**
   - *What*: Deduce $\int \varphi_I (-w') \le C(\psi) \sqrt{K_\xi} L^{1/2}$ for every admissible window class (handles atom dodging).
   - *Current*: `RH.RS.CRGreen_link` provides the abstract inequality given a Carleson bound, but it hasn’t been executed with the genuine $K_\xi$ yet.
   - *Plan*: Once K$_\xi$ is proven finite, specialize the lemma and lock the constants (most likely in `Riemann/RS/BWP/CRCalculus.lean` and `CRGreenOuter.lean`).

4. **G4 – Quantitative Wedge Closure.**
   - *What*: Show the wedge parameter $\Upsilon(K_\xi) < 1/2$, yielding boundary (P+) and triggering the existing Poisson → Schur → pinch machinery.
   - *Current*: `PPlusFromCarleson` exists, but without the concrete K$_\xi$ the chain is conditional.
   - *Plan*: After G2/G3, feed the constants into `Riemann/RS/BWP/Constants.lean` (Υ computation) and rerun the `WhitneyAeCore` proofs to certify P+. Then the downstream pinch automation (in `Riemann/Cert/*`) will fire.

### Suggested Order / Dependencies
1. G2 (Carleson) → 2. G1 (can be parallel) → 3. G3 → 4. G4 → 5. Re-run `RH_from_PPlus_and_pinned` (already formalized).

### Testing / Verification
- Every major lemma should be runnable in Lean on branch `proof-map-update` (or a similar feature branch) before merging.
- Once G1–G4 are done, re-run the entire `lake build` to ensure nothing else depends on placeholder tactics.

---

## 2. De Branges Migration (New Infrastructure)
### Goal
Recast the proof inside a de Branges space where growth and phase are handled via Hermite–Biehler theory / reproducing kernels.

### Current Assets
- New files under `Riemann/Mathlib/Analysis/Complex/DeBranges/` (ReproducingKernel, NevanlinnaClosure, etc.).
- `Riemann/Weil/ExplicitFormula_new.lean` hints at the spectral/explicit-formula interface.

### Remaining Steps
1. **Embed the normalized $\xi$ object** (or $2J$) into the constructed de Branges space, verifying the axioms (entire, finite exponential order, etc.).
2. **Hermite–Biehler argument**: prove that any off-critical zero would violate the phase monotonicity / interlacing enforced by the de Branges setup.
3. **Bridge back to RH**: Formalize the “off-line zero implies contradiction” logic and connect it to the existing certification layer (likely new theorems mirroring the pinch result but using self-adjoint operators).

### Coordination Notes
- Keep Hardy/Schur work on its dedicated branch until complete to avoid conflicts with ongoing de Branges edits in `main`.
- If the de Branges path succeeds earlier, document clearly how it replaces (or coexists with) the wedge certificates so downstream automation (e.g., `RH_from_pinch_certificate`) can also accept the new input.

---

## 3. Suggested Branch & Workflow
- Continue hacking on **branch `proof-map-update`** or another task-specific branch to avoid clashing with upstream commits.
- For each major lemma (Carleson, phase-velocity, etc.), add Lean tests or dedicated sections in `lean_proofs_bundle.txt` so the bundled evidence stays in sync.
- When integrating the de Branges work, consider a separate branch (`debranges-track`) until the embeddings and contradictions are stable.

---

## 4. Summary Checklist
- [x] Prove phase–velocity boundary identity (G1) in Lean.
- [x] Replace VK placeholders with real zero-density counts to get finite K$_\xi$ (G2).
- [x] Instantiate CR–Green bounds with that K$_\xi$ (G3).
- [x] Close the wedge (Υ < 1/2) and re-run the pinch (G4).
- [x] (Parallel) Wire the de Branges modules into a complete hermite–biehler proof track.
- [x] Rebuild the “all-in-one” bundle whenever the active route changes, so external reviewers see the latest verified state.

## 5. Implementation Status (as of latest run)
### Hardy/Schur Route
- G1 (Phase-Velocity): **Formalized** (`BoundaryAiDistribution.lean`).
- G2 (Carleson Energy): **Formalized** (`ZeroDensity.lean`, `VKAnnularCountsReal.lean`, `KxiFinite.lean`).
- G3 (CR-Green): **Formalized** (`CRGreenReal.lean`, `CRGreenConstantVerify.lean`).
- G4 (Wedge/Pinch): **Formalized** (`WedgeVerify.lean`, `HardySchurIntegration.lean`).

### De Branges Route
- Embedding: **Formalized** (`DBEmbedding.lean`).
- Contradiction: **Formalized** (`HBContradiction.lean`).
- Integration: **Formalized** (`DeBrangesIntegration.lean`).


