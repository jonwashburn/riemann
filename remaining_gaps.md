# Remaining Work for an Unconditional RH Proof

This document enumerates every outstanding task required to turn the current Lean development into a complete, unconditional proof of the Riemann Hypothesis.  It synthesizes the state of the `riemann` workspace (commit matching this checkout) and highlights the dependencies between modules.

---

## 0. Road‑map Overview

| Track | Goal | Status | Key Files |
| --- | --- | --- | --- |
| Hardy/Schur (Boundary Wedge) | From VK zero density → Carleson energy → CR–Green window bound → P⁺ → RH | **Blocked** at VK counts, CR–Green bound, HardySchur glue | `Riemann/RS/BWP/ZeroDensity.lean`, `CRGreenReal.lean`, `HardySchurIntegration.lean`, `Riemann/Cert/KxiPPlus.lean` |
| De Branges / Weil | Alternative self‑adjoint route via HB spaces and explicit formula | **Partially scaffolded**; many `sorry`s | `Riemann/RS/DeBranges/*.lean`, `Riemann/Mathlib/Analysis/Complex/DeBranges/*.lean`, `Riemann/Weil/ExplicitFormula_new.lean` |
| Mellin / Theta / Euler backend | Needed by both tracks to control Archimedean factors and ξ | **Blocked** | `Riemann/academic_framework/MellinThetaZeta*.lean`, `EulerProduct/K0Bound.lean` |
| Fredholm / det₂ infrastructure | Analytic operator backbone for `J_pinch` | **Blocked** | `Riemann/Mathlib/Analysis/Normed/Operator/Fredholm/*.lean` |
| Cert layer & classical PNT inputs | Provide concrete constants, Möbius PNT, Wiener bounds | **Blocked** | `PrimeNumberTheoremAnd/*.lean`, `StrongPNT/*.lean`, `Riemann/Cert/KxiWhitney_RvM.lean` |

Each section below drills into the missing pieces.

---

## 1. Hardy/Schur Boundary‑Wedge Pipeline

### 1.1 Vinogradov–Korobov (VK) Zero‑Density to Carleson Energy

- **Current state:** `Riemann/RS/BWP/ZeroDensity.lean` defines `zeros_in_strip_count` to be identically zero, so `vk_partial_sum_bound_real` is trivial. `VKAnnularCountsReal.lean` merely wraps that placeholder.
- **Needed work:**
  1. Formalize an explicit zero‑density bound (e.g. Vinogradov–Korobov / Ford) as described in `Riemann/RS/VK.txt`.
  2. Implement a non‑trivial `zeros_in_strip_count` using the formal bound, prove `vk_partial_sum_bound_real`, and feed it into `VK_annular_counts_exists_real`.
  3. Re‑derive `Kxi_finite_real` in `Riemann/RS/BWP/KxiFinite.lean` with the genuine counts.
- **Dependencies:** the VK plan sketched in `Riemann/RS/VK.txt` plus number‑theoretic estimates from `PrimeNumberTheoremAnd`/`StrongPNT`.

### 1.2 CR–Green Window Bound

- **Current state:** `CRGreen_window_bound_real` (in `Riemann/RS/BWP/CRGreenReal.lean`) stops after recalling `Kxi_finite_real` and ends with `sorry`.
- **Needed work:**
  1. Use `CRCalculus.lean` to build the Green pairing: translate finite Carleson energy ⇒ `L²` bound on the window integral.
  2. Combine with the constant check in `CRGreenConstantVerify.lean` (which also has a pending inequality) to derive the numeric factor `C_ψ`.

### 1.3 Wedge Closure and Hardy/Schur Integration

- **Current state:** `Riemann/RS/HardySchurIntegration.lean` contains two unresolved steps:
  - Proving the `PPlusFromCarleson` implication (wedge closure).
  - Packaging `Kxi_finite_real` into a `ConcreteHalfPlaneCarleson` witness required by the certificate API.
- **Needed work:**
  1. Formalize the wedge closure theorem in Lean (linking `Upsilon_paper < 1/2` from `WedgeVerify.lean` to the predicate `PPlus`).
  2. Wire the Carleson witness from the CR–Green bound into the certificate layer `Riemann/Cert/KxiPPlus.lean`.
  3. Conclude `hardy_schur_pinch_route_complete`.

---

## 2. De Branges / Weil Track

Even if the Hardy/Schur path is completed, the de Branges route is still desirable as an independent verification.

| File | Missing pieces |
| --- | --- |
| `Riemann/RS/DeBranges/DeBrangesIntegration.lean` | Ends in `sorry`; bridge from HB contradiction to `RH`. |
| `Riemann/Mathlib/Analysis/Complex/DeBranges/Measure.lean` | Needs the non‑vanishing lemma “HB functions have no real zeros.” |
| `Riemann/Mathlib/Analysis/Complex/DeBranges/ReproducingKernel/Basic.lean` | 4 `sorry`s around the reproducing property. |
| `Riemann/Mathlib/Analysis/Complex/DeBranges/NevanlinnaGrowth.lean` | Growth bounds unsolved. |
| `Riemann/Weil/ExplicitFormula_new.lean` | Log‑decay and explicit formula assembly missing. |

All of these must be completed before the De Branges approach can certify RH, even assuming the rest of the infrastructure is in place.

---

## 3. Mellin / Theta / Euler Infrastructure

These files feed both proof tracks (they supply Archimedean constants, control ξ, etc.).

| File | Status | Notes |
| --- | --- | --- |
| `Riemann/academic_framework/MellinThetaZeta.lean` | 19 `sorry`s | Gaussian integrals, change of variables, summability lemmas. |
| `MellinThetaZeta'.lean` | 13 `sorry`s | Refined Mellin identity. |
| `MellinThetaZeta''.lean` | 7 `sorry`s | Final bridge to ξ identities. |
| `EulerProduct/K0Bound.lean` | 5 `sorry`s | Needs interval‑arithmetic proofs for prime‑power tails. |

Without these, even the constant `K0_paper` lacks a Lean justification.

---

## 4. Fredholm / det₂ Backbone

The operator theory required for the determinant `det₂` and the analytic framework is still axiomatic:

| File | `sorry` count | Missing content |
| --- | ---: | --- |
| `Riemann/Mathlib/Analysis/Normed/Operator/Fredholm/Defs.lean` | 7 | Closed range theorem, index lemmas, inverse constructions. |
| `…/Compact.lean` | 6 | Riesz theory for compact perturbations. |
| `…/QuotientProd.lean` | 3 | Quotient constructions and projections. |

These must be filled to avoid relying on unproven analytic facts about `det₂`.

---

## 5. Certificate Layer & Classical Inputs

### 5.1 Kξ from RvM (`Riemann/Cert/KxiWhitney_RvM.lean`)

This file is currently *statement-only*.  Sections C.1 and C.2 contain partial proofs, but the key lemmas end with `sorry`, and the final theorem `kxi_whitney_carleson` returns the trivial constant `Kξ = 0`.  A real implementation must:

1. Finish the Poisson energy lemmas (annular diagonal bounds, Cauchy–Schwarz lift).
2. Instantiate the abstract RvM short‑interval hypothesis with the VK counts derived in §1.
3. Produce an explicit `Kξ` matching or improving `Kxi_paper = 0.16`.

### 5.2 PPlusFromCarleson Bridge (`Riemann/Cert/KxiPPlus.lean`)

`PPlusFromCarleson` is recorded purely as a `Prop`; there is no proof anywhere in the repo.  To finish the proof pipeline we need a Lean file (likely in `Riemann/RS`) that proves this implication using the CR–Green machinery and the wedge constant `Upsilon_paper`.

### 5.3 Prime Number Theorem components

| File | Outstanding work |
| --- | --- |
| `PrimeNumberTheoremAnd/DerivativeBound.lean` | Proof of the derivative inequality is `sorry`. |
| `PrimeNumberTheoremAnd/Wiener.lean` | Two key Fourier bounds at the end are `sorry`. |
| `PrimeNumberTheoremAnd/Consequences.lean` | Möbius PNT theorem still commented with `by sorry`. |
| `PrimeNumberTheoremAnd/GeneralMeromorphic.lean` | Rectangle integral and residue theorems commented out. |

These gaps block any attempt to instantiate VK counts or other analytic bounds from the PNT side.

---

## 6. Additional Notes & Suggested Order of Attack

1. **Zero Density First:** Without a genuine `vk_partial_sum_bound_real`, every downstream Carleson estimate is vacuous.  Prioritize formalizing the VK theorem described in `Riemann/RS/VK.txt`.
2. **CR–Green Pairing:** Once Kξ is meaningful, finish `CRGreenReal.lean` and `CRGreenConstantVerify.lean` so the analytic bound matches the numerical constants.
3. **Wedge Closure Proof:** With the CR bound ready, implement the wedge implication in `HardySchurIntegration.lean`.
4. **Backend Analytic Files:** In parallel, clear the Mellin/Euler and Fredholm `sorry`s so no auxiliary lemmas rely on axioms.
5. **De Branges Track:** After the main route is complete, fill the De Branges files to provide an independent verification path.

Completing all items above will yield a fully formal, unconditional proof pipeline.

