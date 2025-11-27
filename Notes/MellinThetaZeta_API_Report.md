# Relevant API from PrimeNumberTheoremAnd and StrongPNT for MellinThetaZeta'.lean

This document identifies relevant API from the PrimeNumberTheoremAnd and StrongPNT folders that can be used to complete the proofs in `MellinThetaZeta'.lean`.

## 1. Theta Function Related API

### From `Riemann/Mathlib/Theta.lean`:
- **`RH.AcademicFramework.Theta.theta`**: Real parameterization of Jacobi theta function
  - Definition: `θ(t) = ∑_{n ∈ ℤ} exp(-π t n²)` for `t > 0`
- **`summable_theta_term`**: Proves the theta series terms are summable for `t > 0`
  - **Use for**: `jacobiTheta_summable` proof
- **`theta_modularity`**: Functional equation `θ(t) = t^(-1/2) · θ(1/t)`
  - **Use for**: `jacobiTheta_modular` and `poisson_sum_gaussian` proofs
- **`continuous_theta`**: Continuity of theta function on `(0, ∞)`
  - **Use for**: `jacobiTheta_continuous` proof
- **`one_le_theta`** and **`theta_pos`**: Basic bounds on theta function

**Note**: The file uses `Real.tsum_exp_neg_mul_int_sq` from mathlib for Poisson summation, which is directly relevant to `poisson_sum_gaussian`.

## 2. Mellin Transform API

### From `PrimeNumberTheoremAnd/MellinCalculus.lean`:

#### Mellin Transform Definition:
- **`mellin`**: The Mellin transform `𝓜(f)(s) = ∫₀^∞ f(x) x^(s-1) dx`
  - Already in mathlib (imported via `Mathlib.Analysis.MellinTransform`)

#### Integration Tools on `Ioi 0`:
- **`PartialIntegration`**: Integration by parts on `Ioi 0` with support constraints
- **`PartialIntegration_of_support_in_Icc`**: Specialized version for functions with compact support
- **`MeasureTheory.setIntegral_integral_swap`**: Fubini's theorem for swapping integrals
  - **Use for**: `mellin_theta_sum_exchange` (for series ↔ integral exchange)

#### Change of Variables:
- **`integral_comp_mul_right_Ioi`**: Change of variables `x ↦ x * a` on `Ioi 0`
- **`integral_comp_inv_I0i_haar`**: Change of variables `x ↦ 1/x` on `Ioi 0`
  - **Use for**: `mellin_left_integrable` (substitution `u = 1/t`)

#### Mellin Transform Calculations:
- **`MellinOfPsi_aux`**: Integration by parts formula for Mellin transforms
- **`MellinConvolutionTransform`**: Mellin transform of convolution is product
  - Shows how to use Fubini's theorem for Mellin transforms

## 3. Exponential Decay and Integrability

### From `PrimeNumberTheoremAnd/Wiener.lean`:
- **`exp_neg_integrableOn_Ioi`**: Integrability of `exp(-c * x)` on `Ioi 0` for `c > 0`
  - **Use for**: `mellin_right_integrable` (bounding `θ(t) - 1` by `exp(-πt)`)

### From `PrimeNumberTheoremAnd/ZetaBounds.lean`:
- **`integrableOn_Ioi_cpow_iff`**: Criteria for integrability of `x^s` on `Ioi N`
- **`integrableOn_Ioi_rpow_iff`**: Criteria for integrability of `x^r` on `Ioi N`
  - **Use for**: Convergence proofs when combining exponentials with powers

## 4. Series-Integral Exchange

### From `PrimeNumberTheoremAnd/Wiener.lean`:
- **`first_fourier`**: Example of exchanging sum and integral using `integral_tsum`
  - Uses dominated convergence for series
  - **Use for**: `mellin_theta_sum_exchange` proof

### From `PrimeNumberTheoremAnd/MediumPNT.lean`:
- **`SmoothedChebyshevDirichlet_aux_tsum_integral`**: Another example of exchanging sum and integral
  - Shows pattern: `∫ (∑' n, f n) = ∑' n, ∫ f n` under appropriate conditions

### General Pattern:
The key is to use:
- `integral_tsum` from MeasureTheory for dominated convergence
- Need to show: (1) measurability of each term, (2) integrability of the sum of norms

## 5. Gamma Function and Mellin Transforms

### From `PrimeNumberTheoremAnd/MellinCalculus.lean`:
The file shows integration by parts techniques that could help with `mellin_gaussian_term`, but the specific Mellin transform of `exp(-at)` is likely in mathlib's Gamma function API.

### Expected API (check mathlib):
- **`Complex.Gamma_integral`**: `Γ(z) = ∫₀^∞ t^(z-1) exp(-t) dt`
- **`mellin_exp`** or similar: Mellin transform of exponential functions
  - Should give: `∫₀^∞ exp(-at) t^(z-1) dt = Γ(z) / a^z`

## 6. Riemann Zeta Function API

### From `PrimeNumberTheoremAnd/ZetaBounds.lean`:
- **`riemannZeta`**: The Riemann zeta function (from mathlib)
- **`riemannZeta_ne_zero_of_one_lt_re`**: Zeta is nonzero for `Re(s) > 1`
- **`differentiableAt_riemannZeta`**: Differentiability away from `s = 1`

### From `Riemann/Mathlib/ZetaFunctionalEquation.lean`:
- **`completedRiemannZeta`**: The completed zeta function from mathlib
- **`completedRiemannZeta_one_sub`**: Functional equation `Λ(s) = Λ(1-s)`
  - **Note**: This is already proven! The functional equation is available in mathlib.

### From `Riemann/Mathlib/MellinThetaZeta.lean`:
- **`RH.AcademicFramework.completedZeta`**: Similar definition to `MellinThetaZeta'.completedZeta`
  - Shows the pattern: `π^(-s/2) * Γ(s/2) * ζ(s)`

## 7. Integration Techniques

### From `PrimeNumberTheoremAnd/MellinCalculus.lean`:
- **`SetIntegral.integral_eq_integral_inter_of_support_subset_Icc`**: Restricting integrals to support
- **`intervalIntegral.norm_integral_le_of_norm_le_const'`**: Bounding integrals by constants

### Support and Continuity:
- **`Function.support_deriv_subset_Icc`**: Support of derivative
- **`Function.support_mul_subset_of_subset`**: Support of product
- **`TendstoAtZero_of_support_in_Icc`**: Limits at zero for compactly supported functions
- **`TendstoAtTop_of_support_in_Icc`**: Limits at infinity

## 8. Summary: Which APIs to Use for Each Proof

### `jacobiTheta_summable`:
- Use: `RH.AcademicFramework.Theta.summable_theta_term` (or adapt its proof technique)

### `jacobiTheta_continuous`:
- Use: `RH.AcademicFramework.Theta.continuous_theta` (or adapt its proof)

### `jacobiTheta'_decay`:
- Need: Bounds on `∑_{n≥1} exp(-π n² t)` for `t ≥ 1`
- Technique: Geometric series bounds

### `poisson_sum_gaussian`:
- Use: `Real.tsum_exp_neg_mul_int_sq` from mathlib (Poisson summation for Gaussian)
- Or: `RH.AcademicFramework.Theta.theta_modularity` which proves this

### `mellin_right_integrable`:
- Use: `exp_neg_integrableOn_Ioi` + comparison with `θ(t) - 1 = O(exp(-πt))`
- Combine with: `integrableOn_Ioi_cpow_iff` or similar for the power factor

### `mellin_left_integrable`:
- Use: `integral_comp_inv_I0i_haar` or `integral_comp_mul_right_Ioi` for substitution `u = 1/t`
- Apply modular transformation: `θ(t) - 1 ≈ t^(-1/2)(θ(1/t) - 1)`

### `mellin_theta_integrable`:
- Use: `IntegrableOn.union` or similar to combine `∫₀^1` and `∫₁^∞`
- Apply: `mellin_left_integrable` and `mellin_right_integrable`

### `mellin_gaussian_term`:
- Need: Mathlib's Mellin transform of exponential (check `Mathlib.Analysis.SpecialFunctions.Gamma`)
- Should be: `∫₀^∞ exp(-at) t^(z-1) dt = Γ(z) / a^z`

### `mellin_theta_sum_exchange`:
- Use: `integral_tsum` from MeasureTheory
- Need to show:
  1. Measurability: `AEMeasurable.aestronglyMeasurable` for each term
  2. Integrability: Sum of norms is integrable (dominated convergence)

### `sum_nonzero_eq_twice_zeta`:
- Use: Definition of `riemannZeta` as `∑_{n≥1} n^(-s)`
- Split: `∑_{n∈ℤ\{0}} n^(-s) = ∑_{n≥1} n^(-s) + ∑_{n≥1} (-n)^(-s)`
- Note: `(-n)^(-s) = n^(-s)` for the appropriate branch

### `mellin_theta_eq_completed_zeta`:
- Combine: `mellin_theta_sum_exchange` + `mellin_gaussian_term` + `sum_nonzero_eq_twice_zeta`
- Algebra: `Γ(s/2) (π n²)^(-s/2) = Γ(s/2) π^(-s/2) n^(-s)`

### `completedZeta_functional_equation`:
- **Note**: Mathlib already has `completedRiemannZeta_one_sub` proving this!
- Can use: `Riemann.Mathlib.ZetaFunctionalEquation.zeta_functional_equation`

## 9. Missing API to Check in Mathlib

1. **Mellin transform of exponential**:
   - `Mathlib.Analysis.SpecialFunctions.Gamma.Basic` or `.Integral`
   - Should have: `∫₀^∞ exp(-at) t^(z-1) dt = Γ(z) / a^z`

2. **Poisson summation for Gaussian**:
   - `Mathlib.Analysis.Fourier.PoissonSummation`
   - `Real.tsum_exp_neg_mul_int_sq` (mentioned in Theta.lean)

3. **Series-integral exchange**:
   - `MeasureTheory.integral_tsum` (for dominated convergence)
   - `MeasureTheory.integral_tsum_of_summable` (if available)

4. **Exponential integrability**:
   - `Mathlib.MeasureTheory.Integral.ExpDecay` (already imported)

## 10. Recommendations

1. **Reuse existing theta API**: The `Riemann/Mathlib/Theta.lean` file already has most of what's needed for theta function properties.

2. **Check mathlib first**: Before implementing from scratch, check:
   - `Mathlib.Analysis.SpecialFunctions.Gamma.Integral` for Mellin transforms
   - `Mathlib.NumberTheory.LSeries.RiemannZeta` for zeta properties
   - `Mathlib.Analysis.MellinTransform` for general Mellin theory

3. **Functional equation**: Already proven in mathlib! Use `completedRiemannZeta_one_sub`.

4. **Pattern matching**: Follow the patterns in:
   - `PrimeNumberTheoremAnd/MellinCalculus.lean` for Mellin calculations
   - `PrimeNumberTheoremAnd/Wiener.lean` for series-integral exchanges
