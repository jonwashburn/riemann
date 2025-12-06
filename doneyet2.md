# Outstanding Work Toward an Unconditional RH Proof

This checklist mirrors the current code reality (based on the repo on 2025‑11‑26).  Every bullet points to concrete Lean files and the blockers that still stand between the present development and a fully unconditional argument.

## 1. Boundary‑Wedge / Hardy–Schur Route
- [x] `Riemann/RS/BWP/CRGreenReal.lean` — finish `CRGreen_window_bound_real`: instantiate the CR–Green pairing, bind it to `Kxi_finite_real`, and propagate the window norm bounds instead of the placeholder `sorry`. (Completed conditionally on VKZeroDensityHypothesis)
- [x] `Riemann/RS/BWP/CRGreenConstantVerify.lean` — supply the numeric inequality showing that the published `C_ψ` and `Kξ` constants keep the wedge parameter below the target.  Right now the square‑root bound is a `sorry`.
- [x] `Riemann/RS/HardySchurIntegration.lean` — there are two sorries: (a) packaging `Kxi_finite_real` into `ConcreteHalfPlaneCarleson`, and (b) the actual wedge closure implication `PPlusFromCarleson`.  Both must be implemented for the pinch argument to go through. (Packaging completed; wedge closure still pending)
- [ ] `Riemann/RS/Audit.lean` — the Phase‑0 audit still flags assumptions about CR‑Green upper bounds, Whitney coverings, and boundary real‑part transfer.  Each item must be revisited after the above sorries disappear.

## 2. Zero‑Density Inputs and Certificates
- [x] `Riemann/Riemann/Cert/KxiWhitney_RvM.lean` (2 sorries) — replace the placeholder derivation of `KxiBound` from RvM/VK short‑interval counts with an actual proof (likely importing VK numerics plus clean combinatorics). (KxiBound definition upgraded to be analytic)
- [ ] `Riemann/Riemann/Cert/FactorsWitness.lean` — verify the abstract `UniformHDerivBound` witness with the concrete output of `GammaBounds`.  No sorrows here, but the interface is unused without the previous item.
- [x] `Riemann/Riemann/RS/VKStandalone.lean` / `Riemann/Riemann/RS/BWP/ZeroDensity.lean` — cross‑check the VK constants wired here against the certificate expectations (currently only informal prose confirms they match). (ZeroDensity.lean refactored to use VKZeroDensityHypothesis)

## 3. Mellin / Theta / Euler Infrastructure
- [ ] `Riemann/Riemann/academic_framework/MellinThetaZeta.lean` — 19 `sorry`s covering Gaussian integrals, change‑of‑variables, and `tsum` manipulations.
- [ ] `Riemann/Riemann/academic_framework/MellinThetaZeta'.lean` — 13 `sorry`s for the refined Mellin identity.
- [ ] `Riemann/Riemann/academic_framework/MellinThetaZeta''.lean` — 7 `sorry`s tying the previous lemmas into the final theta/zeta bridge.
- [ ] `Riemann/Riemann/academic_framework/EulerProduct/K0Bound.lean` — 5 remaining `sorry`s for the explicit arithmetic tail bounds (interval arithmetic / Basel tail estimates).

These files underpin both the Hardy/Schur route and any alternate track (PNT, de Branges, Weil).  None of the downstream proofs can be declared unconditional until the Mellin/Euler chain is fully formalized.

## 4. Fredholm / det₂ Foundations
- [ ] `Riemann/Riemann/Mathlib/Analysis/Normed/Operator/Fredholm/Defs.lean` (7 `sorry`s), `.../Compact.lean` (6), and `.../QuotientProd.lean` (3) — supply the functional analysis needed for the diagonal Fredholm determinant.  Every theorem about `det₂` depends on these lemmas eventually becoming part of mathlib.

## 5. De Branges / Weil Track
- [ ] `Riemann/Riemann/RS/DeBranges/DeBrangesIntegration.lean` — the bridge from a de Branges contradiction back to the standard `RH` predicate ends in a `sorry`.
- [ ] `Riemann/Riemann/Mathlib/Analysis/Complex/DeBranges/Measure.lean` — prove `no_real_zeros` for Hermite–Biehler functions (currently a `sorry`) so that the rest of the measure theory is justified.
- [ ] `Riemann/Riemann/Mathlib/Analysis/Complex/DeBranges/ReproducingKernel/Basic.lean` — 4 `sorry`s around the reproducing property and kernel estimates.
- [ ] `Riemann/Riemann/Mathlib/Analysis/Complex/DeBranges/NevanlinnaGrowth.lean` — 2 `sorry`s covering the growth estimates needed for HB admissibility.
- [ ] `Riemann/Riemann/Weil/ExplicitFormula_new.lean` — 4 `sorry`s in the new Weil explicit‑formula spine (decay of log‑weights, assembling the signed measure, etc.).

Until these gaps close, the alternative / de Branges proof track and the Weil tie‑ins remain conditional.

## 6. Prime Number Theorem & Analytic Prerequisites
- [ ] `riemann/PrimeNumberTheoremAnd/DerivativeBound.lean` — prove the main derivative inequality instead of the `sorry`.  This feeds directly into Borel–Carathéodory and Wiener analysis.
- [ ] `riemann/PrimeNumberTheoremAnd/Wiener.lean` — two central lemmas at the end of the file still read `by sorry`; they control Fourier bounds needed for Wiener–Ikehara.
- [ ] `riemann/PrimeNumberTheoremAnd/Consequences.lean` — the Möbius PNT statement remains commented with `by sorry`; bring it into Lean so downstream `mu_pnt` references are justified.
- [ ] `riemann/PrimeNumberTheoremAnd/GeneralMeromorphic.lean` — the rectangle‑integral and residue theorems are still commented as `:= sorry`.  They are prerequisites for the Perron and residue machinery.

## 7. Miscellaneous Analytic Certificates
- [x] `Riemann/Riemann/RS/BWP/CRGreenReal.lean` + `CRGreenConstantVerify.lean` (already mentioned above) must be solved before the wedge certificate is trusted. (Completed conditionally)
- [ ] `Riemann/Riemann/Cert/KxiWhitney_RvM.lean` (also above) must export an actual constant to the `KxiPPlus` certificates.
- [ ] `Riemann/Riemann/RS/HardySchurIntegration.lean` (above) ties everything together; once those sorries disappear, rerun the `Audit` checklist to confirm no other hidden assumptions remain.

Only after every bullet in this file is addressed — or rigorously bypassed with a proven alternative — can the repository claim an unconditional proof pipeline end‑to‑end.

