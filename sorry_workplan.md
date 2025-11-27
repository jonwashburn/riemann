# Sorry Workplan: Complete Proof Formalization

This document provides a comprehensive plan to eliminate all `sorry` placeholders in the Riemann Hypothesis formalization. The plan is organized by priority and dependency order.

---

## Executive Summary

**Total sorries found:** ~83 across 20+ files
**Critical path sorries:** ~25 (blocks main theorem via Hardy-Schur route)
**Infrastructure sorries:** ~12 (Fredholm theory - not on critical path)
**Alternative route sorries:** ~7 (De Branges - NOT needed for main proof)
**Deprecated/WIP sorries:** ~20 (MellinThetaZeta'.lean, MellinThetaZeta''.lean)
**Cleanup sorries:** ~19 (numeric bounds, old interfaces)

---

## Phase 1: Critical Path (Blocks `hardy_schur_pinch_route_complete`)

### 1.1 CR-Green Calculus (`riemann/Riemann/RS/BWP/CRCalculus.lean`)

| Lemma | Description | Approach | Difficulty |
|-------|-------------|----------|------------|
| `greens_identity_on_tent` | Green's identity on Whitney tents | Use Mathlib's `integral_boundary_eq_interior_div` or construct via Stokes | Medium |
| `test_function_energy_bound` | Energy estimate for test functions | Apply Poincaré inequality from Mathlib | Easy |
| `boundary_term_vanishes` | Boundary terms vanish at infinity | Use compact support + dominated convergence | Easy |
| `outer_cancellation_in_energy` | Outer function cancels in Dirichlet energy | Holomorphicity of outer function implies ∂̄O = 0 | Medium |

**Strategy:** Start with `test_function_energy_bound` and `boundary_term_vanishes` (easier), then build to `greens_identity_on_tent`.

### 1.2 Wedge Verification (`riemann/Riemann/RS/BWP/WedgeVerify.lean`)

| Lemma | Description | Approach | Difficulty |
|-------|-------------|----------|------------|
| `local_to_global_wedge_lemma` | Local phase bounds → global positivity | Lebesgue differentiation theorem + Poisson kernel | Hard |
| `poisson_plateau_lower_bound` | Poisson kernel plateau estimate | Explicit computation with kernel formula | Medium |
| `wedge_contradiction_argument` | Contradiction via measure scaling | Borel-Cantelli type argument | Medium |

**Strategy:** The wedge lemma is the core. First prove `poisson_plateau_lower_bound`, then use it in the main argument.

### 1.3 Poisson Transport (`riemann/Riemann/RS/PoissonTransport.lean`)

| Lemma | Description | Approach | Difficulty |
|-------|-------------|----------|------------|
| `poisson_transport_lemma` | Boundary positivity → interior positivity | Maximum principle for harmonic functions | Medium |

**Strategy:** Use Mathlib's `IsMaxOn` API for harmonic functions. May need to construct Poisson representation formula.

### 1.4 Hardy-Schur Integration (`riemann/Riemann/RS/HardySchurIntegration.lean`)

| Lemma | Description | Approach | Difficulty |
|-------|-------------|----------|------------|
| `hyp.C_VK >= 0` (2 instances) | VK constant is non-negative | Should be part of hypothesis structure | Trivial |

**Strategy:** Add `hC_VK_nonneg` field to `VKZeroDensityHypothesis` if not present, then use it.

### 1.5 PPlusFromCarleson (`riemann/Riemann/RS/PPlusFromCarleson.lean`)

| Lemma | Description | Approach | Difficulty |
|-------|-------------|----------|------------|
| Main `sorry` | Local-to-global wedge argument | Combines WedgeVerify + PoissonTransport | Hard |

**Strategy:** This is the final assembly. Complete 1.1-1.4 first.

---

## Phase 2: Analytic Number Theory Backend

### 2.1 Vinogradov-Korobov (`riemann/Riemann/AnalyticNumberTheory/VinogradovKorobov.lean`)

| Lemma | Description | Approach | Difficulty |
|-------|-------------|----------|------------|
| `littlewood_jensen_rectangle` | Jensen's formula on rectangles | Adapt Mathlib's `Complex.jensen_formula` | Hard |
| `integral_log_plus_zeta_bound` | log⁺|ζ| integral bound | Use exponential sum estimates | Very Hard |
| `vk_zero_density_estimate` | Main VK density theorem | Combine above two | Very Hard |

**Strategy:** This is deep analytic number theory. Consider:
1. Accept as axiom (via `VKZeroDensityHypothesis` structure)
2. Or formalize incrementally starting from existing Mathlib zeta bounds

### 2.2 Zero-Free Region (`riemann/Riemann/AnalyticNumberTheory/VKZeroFreeRegion.lean`)

| Lemma | Description | Approach | Difficulty |
|-------|-------------|----------|------------|
| `vk_zero_free_region` | VK zero-free region | Exponential sum → log-free region | Very Hard |

**Strategy:** Same as above. The existing `PrimeNumberTheoremAnd/` folder has related infrastructure.

### 2.3 Zero Density (`riemann/Riemann/RS/BWP/ZeroDensity.lean`)

| Lemma | Description | Approach | Difficulty |
|-------|-------------|----------|------------|
| `vk_partial_sum_bound_real` | Partial sum bound from VK | Use `VKZeroDensityHypothesis.zero_density` | Medium |

**Strategy:** The structure is in place; need to wire through the hypothesis properly.

---

## Phase 3: Mellin-Theta-Zeta Infrastructure

### 3.1 Core Identities (`riemann/Riemann/academic_framework/MellinThetaZeta.lean`)

| Lemma | Description | Approach | Difficulty |
|-------|-------------|----------|------------|
| `tsum_int_split` | Split ℤ-sum into ℕ-sums | Use `summable_int_iff_summable_nat_and_neg` | Easy |
| `tsum_int_eq_tsum_nat_add_tsum_nat_neg` | Same as above | Direct application | Easy |
| `exp_neg_mul_dominates_rpow` | t^α exp(-at) → 0 | L'Hôpital / standard analysis | Easy |
| `integrable_exp_neg_mul_rpow_Ioi` | Integrability on [1,∞) | Dominated convergence | Easy |
| `sum_exp_neg_pi_sq_le` | π(n+1)² ≥ π + πn | Arithmetic inequality | Trivial |
| `fourier_transform_gaussian` | Gaussian Fourier transform | Contour integration or cite Mathlib | Medium |
| `poisson_sum_gaussian_explicit` | Poisson summation | Use Mathlib's `Real.tsum_exp_neg_mul_sq` | Medium |
| `mellin_exp` | Mellin of exp(-at) = Γ(s)/a^s | Gamma function definition | Medium |
| `mellin_theta_sum_exchange` | Exchange sum and integral | Fubini + absolute convergence | Medium |
| `jacobiTheta'_abs_le` | Theta tail bound | Geometric series comparison | Easy |
| `integral_comp_inv_Ioi` | Change of variables u=1/t | Measure theory substitution | Medium |
| `mellin_right_integrable` | Right Mellin integrable | Use theta decay bounds | Medium |
| `mellin_left_integrable` | Left Mellin integrable | Use theta decay bounds | Medium |
| `mellin_theta_zeta_identity` | Main Mellin-theta identity | Combine above | Hard |
| `completedZeta_functional_equation` | ξ(s) = ξ(1-s) | Use theta modular transformation | Hard |

**Strategy:** Work bottom-up. Start with trivial arithmetic (`sum_exp_neg_pi_sq_le`, `tsum_int_split`), then integrability, then main identities.

### 3.2 Alternate Files (`MellinThetaZeta'.lean`, `MellinThetaZeta''.lean`)

These appear to be work-in-progress variants. **Strategy:** Consolidate into main file or mark as deprecated.

---

## Phase 4: Fredholm Operator Theory

### 4.1 Definitions (`riemann/Riemann/Mathlib/Analysis/Normed/Operator/Fredholm/Defs.lean`)

| Lemma | Description | Approach | Difficulty |
|-------|-------------|----------|------------|
| `IsFredholm.closedRange` | Fredholm → closed range | Open mapping theorem | Hard |
| Various `sorry` in equiv construction | Equivalence proofs | Linear algebra | Medium |

### 4.2 Compact Perturbations (`riemann/Riemann/Mathlib/Analysis/Normed/Operator/Fredholm/Compact.lean`)

| Lemma | Description | Approach | Difficulty |
|-------|-------------|----------|------------|
| Riesz theory lemmas | Compact operator spectral theory | Deep functional analysis | Very Hard |
| Homotopy invariance | Index is locally constant | Requires perturbation theory | Very Hard |

### 4.3 Quotient/Product (`riemann/Riemann/Mathlib/Analysis/Normed/Operator/Fredholm/QuotientProd.lean`)

| Lemma | Description | Approach | Difficulty |
|-------|-------------|----------|------------|
| Projection existence | Continuous projections | Hahn-Banach | Hard |

**Strategy:** Fredholm theory is a large project. Consider:
1. Check if Mathlib has added Fredholm operators recently
2. Or accept key properties as axioms if not on critical path

---

## Phase 5: De Branges Track (OPTIONAL - Alternative Route)

> ⚠️ **NOT REQUIRED FOR MAIN PROOF** - The Hardy-Schur route (Phase 1) is the primary proof track.
> De Branges is an independent alternative that could be pursued if Hardy-Schur is blocked.

### 5.1 Measure Theory (`riemann/Riemann/Mathlib/Analysis/Complex/DeBranges/Measure.lean`)

| Lemma | Description | Approach | Difficulty |
|-------|-------------|----------|------------|
| HB functions have no real zeros | Key de Branges property | Complex analysis | Hard |

### 5.2 Reproducing Kernel (`riemann/Riemann/Mathlib/Analysis/Complex/DeBranges/ReproducingKernel/Basic.lean`)

| Lemma | Description | Approach | Difficulty |
|-------|-------------|----------|------------|
| Kernel properties (4 sorries) | RKHS theory | Functional analysis | Hard |

### 5.3 Nevanlinna Growth (`riemann/Riemann/Mathlib/Analysis/Complex/DeBranges/NevanlinnaGrowth.lean`)

| Lemma | Description | Approach | Difficulty |
|-------|-------------|----------|------------|
| Growth estimates (2 sorries) | Nevanlinna theory | Complex analysis | Hard |

**Strategy:** De Branges is an **alternative** proof route, NOT required for the main Hardy-Schur proof.
Skip entirely unless Hardy-Schur path is blocked. The ~7 sorries here do NOT block `hardy_schur_pinch_route_complete`.

---

## Phase 6: Cleanup & Numeric Bounds

### 6.1 K0 Bounds (`riemann/Riemann/academic_framework/EulerProduct/K0Bound.lean`)

| Lemma | Description | Approach | Difficulty |
|-------|-------------|----------|------------|
| Numeric certificates | Interval arithmetic | Use `norm_num` / `native_decide` | Medium |
| Basel tail bounds | ζ(2) - partial sums | Explicit computation | Easy |

### 6.2 Weil Explicit Formula (`riemann/Riemann/Weil/ExplicitFormula_new.lean`)

| Lemma | Description | Approach | Difficulty |
|-------|-------------|----------|------------|
| Decay proofs | log n vs power decay | Standard analysis | Easy |

### 6.3 Old Interfaces (`riemann/Riemann/Cert/KxiWhitney_RvM.lean`)

| Lemma | Description | Approach | Difficulty |
|-------|-------------|----------|------------|
| 2 sorries | Legacy code | Deprecate or update | Easy |

---

## Recommended Execution Order

```
Week 1: Phase 1.1-1.4 (CR-Green, Wedge basics)
Week 2: Phase 1.5 + Phase 3.1 (PPlusFromCarleson + Mellin basics)
Week 3: Phase 2 (Analytic number theory - may need axiomatization)
Week 4: Phase 6 (Cleanup, numeric bounds)
Week 5+: Phase 4-5 (Fredholm, de Branges - if needed)
```

---

## Quick Wins (Can be done immediately)

1. `sum_exp_neg_pi_sq_le` - trivial arithmetic
2. `tsum_int_split` - use existing Mathlib lemma
3. `hyp.C_VK >= 0` - add field to hypothesis structure
4. `test_function_energy_bound` - Poincaré inequality
5. `boundary_term_vanishes` - dominated convergence

---

## Dependencies Graph

```
VKZeroDensityHypothesis
        │
        ▼
  Kxi_finite_real
        │
        ▼
CRGreen_window_bound_real ◄── CRCalculus lemmas
        │
        ▼
ConcreteHalfPlaneCarleson
        │
        ▼
  PPlusFromCarleson ◄── WedgeVerify + PoissonTransport
        │
        ▼
hardy_schur_pinch_route_complete
        │
        ▼
       RH
```

---

## Files to Create/Modify

| Action | File | Purpose |
|--------|------|---------|
| Modify | `VKStandalone.lean` | Add `hC_VK_nonneg` field |
| Modify | `CRCalculus.lean` | Complete 4 lemmas |
| Modify | `WedgeVerify.lean` | Complete 3 lemmas |
| Modify | `PoissonTransport.lean` | Complete 1 lemma |
| Modify | `MellinThetaZeta.lean` | Complete ~15 lemmas |
| Modify | `HardySchurIntegration.lean` | Wire through non-negativity |
| Modify | `PPlusFromCarleson.lean` | Complete main theorem |

---

## Risk Assessment

| Risk | Mitigation |
|------|------------|
| VK estimates too hard to formalize | Accept as hypothesis (already structured) |
| Fredholm theory blocks proof | Not on critical path for Hardy-Schur |
| Mellin convergence issues | Use existing Mathlib infrastructure |
| Wedge argument subtle | Follow Kapustin paper closely |

---

## Success Criteria

The proof is complete when:
1. `lake build` succeeds with no errors
2. `grep -r "sorry" riemann/Riemann` returns only:
   - Comments explaining deliberate axioms
   - Deprecated/unused files
3. `hardy_schur_pinch_route_complete` has no `sorry` in its proof tree
