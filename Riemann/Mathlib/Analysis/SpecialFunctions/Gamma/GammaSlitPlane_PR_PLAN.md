# Mathlib PR Plan: Gamma Maps Right Half-Plane to SlitPlane

This document outlines the proposed Mathlib PRs to prove `Gamma_mem_slitPlane_of_re_pos`:
for all `z : ℂ` with `0 < z.re`, we have `Gamma z ∈ slitPlane`.

## Current Status

The theorem `Gamma_mem_slitPlane_of_re_pos` in `GammaLogDeriv.lean` has:
- ✅ Case `z.im = 0` (z is a positive real): Proven using `Gamma_pos_of_pos`
- ⏳ Case `z.im ≠ 0` (z is not real): Requires infrastructure below

## Mathematical Overview

The proof for the non-real case requires showing that `Gamma z` cannot be a negative real.

**Key Insight**: On the simply connected right half-plane, `log Γ` has a holomorphic
branch with `Im(log Γ) = 0` on the positive real axis. By the open mapping theorem
and properties of harmonic functions on simply connected domains, `Im(log Γ z) ∈ (-π, π)`
for all `z` in the domain. This precludes `Gamma z` from being a negative real
(which would require `Im(log Γ z) = π`).

---

## Proposed PR Series

### PR 1: Right Half-Plane Topology (Ready to Port)

**File location**: `Mathlib.Analysis.Complex.RightHalfPlane`

**New definitions and lemmas**:
```lean
/-- The open right half-plane {z : ℂ | 0 < z.re} -/
def rightHalfPlane : Set ℂ := {z | 0 < z.re}

/-- The closed right half-plane {z : ℂ | 0 ≤ z.re} -/
def closedRightHalfPlane : Set ℂ := {z | 0 ≤ z.re}

/-- The right half-plane is open. -/
lemma isOpen_rightHalfPlane : IsOpen rightHalfPlane

/-- The right half-plane is connected. -/
lemma isConnected_rightHalfPlane : IsConnected rightHalfPlane

/-- The right half-plane is path-connected. -/
lemma isPathConnected_rightHalfPlane : IsPathConnected rightHalfPlane

/-- The right half-plane is star-convex at any point with positive real part. -/
lemma starConvex_rightHalfPlane {w : ℂ} (hw : 0 < w.re) :
    StarConvex ℝ w rightHalfPlane

/-- The right half-plane is convex. -/
lemma convex_rightHalfPlane : Convex ℝ rightHalfPlane

/-- The right half-plane is simply connected (has trivial fundamental group). -/
theorem simplyConnected_rightHalfPlane : SimplyConnectedSpace rightHalfPlane
```

**Proof strategy**:
- Use `isOpen_lt continuous_const continuous_re`
- Convexity follows from `convex_halfspace_lt` or direct construction
- Star-convexity follows from convexity
- Simply connected follows from contractibility (star-shaped domains are contractible)

**Dependencies**: `Mathlib.Topology.Homotopy.Contractible`, `Mathlib.Analysis.Convex.Star`

**Status**: ⏳ Needs implementation (straightforward from existing lemmas)

---

### PR 2: Holomorphic Logarithm on Simply Connected Domains

**File location**: `Mathlib.Analysis.Complex.HolomorphicLog`

**New lemmas**:
```lean
/-- On a simply connected open set U, if f : U → ℂ \ {0} is holomorphic,
    then f has a holomorphic logarithm. -/
theorem exists_holomorphic_log_of_simplyConnected {U : Set ℂ} (hU_open : IsOpen U)
    (hU_sc : SimplyConnectedSpace U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hf_ne : ∀ z ∈ U, f z ≠ 0) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ ∀ z ∈ U, exp (g z) = f z

/-- The holomorphic logarithm is unique up to 2πi. -/
theorem holomorphic_log_unique {U : Set ℂ} (hU_open : IsOpen U) (hU_conn : IsConnected U)
    {f g₁ g₂ : ℂ → ℂ} (hg₁ : DifferentiableOn ℂ g₁ U) (hg₂ : DifferentiableOn ℂ g₂ U)
    (h₁ : ∀ z ∈ U, exp (g₁ z) = f z) (h₂ : ∀ z ∈ U, exp (g₂ z) = f z) :
    ∃ n : ℤ, ∀ z ∈ U, g₁ z = g₂ z + 2 * π * I * n

/-- On the right half-plane, id has a holomorphic logarithm (the principal branch). -/
theorem exists_holomorphic_log_id_rightHalfPlane :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g rightHalfPlane ∧
      (∀ z ∈ rightHalfPlane, exp (g z) = z) ∧
      (∀ x : ℝ, 0 < x → g x = Real.log x)
```

**Proof strategy**:
- Use the theory of covering spaces: exp : ℂ → ℂ* is a covering map
- On simply connected domains, every covering map has a section
- Alternatively, use the integral formula: g(z) = g(z₀) + ∫_{z₀}^z f'/f dw

**Dependencies**:
- `Mathlib.Topology.Homotopy.Lifting` (covering space theory)
- `Mathlib.Analysis.Complex.CauchyIntegral` (for integral approach)

**Status**: ⏳ Requires significant development

**Notes**: This is the most substantial PR. It may be split into:
- PR 2a: Covering space approach to holomorphic logarithm
- PR 2b: Integral formula approach (may be easier for our application)

---

### PR 3: Schwarz Reflection for Functions Real on Real Axis

**File location**: `Mathlib.Analysis.Complex.SchwarzReflection`

**New lemmas**:
```lean
/-- If f is holomorphic on the upper half-plane, continuous on its closure,
    and real on the real axis, then f(conj z) = conj(f(z)). -/
theorem conj_eq_of_real_on_real {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z | 0 < z.im})
    (hf_cont : ContinuousOn f {z | 0 ≤ z.im})
    (hf_real : ∀ x : ℝ, (f x).im = 0) :
    ∀ z, 0 < z.im → f (conj z) = conj (f z)

/-- Symmetric version for domains symmetric about the real axis. -/
theorem conj_eq_of_symmetric_domain {U : Set ℂ} {f : ℂ → ℂ}
    (hU_sym : ∀ z, z ∈ U ↔ conj z ∈ U)
    (hf : DifferentiableOn ℂ f U)
    (hf_real : ∀ x : ℝ, ↑x ∈ U → (f x).im = 0) :
    ∀ z ∈ U, f (conj z) = conj (f z)
```

**Proof strategy**:
- Use the identity theorem: g(z) = f(conj z) - conj(f(z)) is holomorphic
- g vanishes on the real axis (a set with accumulation points)
- Therefore g ≡ 0 on the connected component

**Dependencies**: `Mathlib.Analysis.Complex.IdentityTheorem`

**Existing**: Mathlib has `Complex.Gamma_conj` which is the Schwarz reflection for Gamma!
This PR generalizes the principle.

**Status**: ⏳ Moderate work

---

### PR 4: Imaginary Part of Holomorphic Log is Bounded Away from ±π

**File location**: `Mathlib.Analysis.Complex.LogArgBound`

**Key theorem**:
```lean
/-- On the right half-plane, the imaginary part of any holomorphic logarithm
    of a nonzero holomorphic function is in (-π, π), provided the log is real
    on the positive real axis where the function is positive. -/
theorem im_holomorphic_log_mem_Ioo_neg_pi_pi {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f rightHalfPlane)
    (hf_ne : ∀ z ∈ rightHalfPlane, f z ≠ 0)
    (hf_pos : ∀ x : ℝ, 0 < x → 0 < (f x).re ∧ (f x).im = 0)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g rightHalfPlane)
    (hg_log : ∀ z ∈ rightHalfPlane, exp (g z) = f z)
    (hg_real : ∀ x : ℝ, 0 < x → (g x).im = 0) :
    ∀ z ∈ rightHalfPlane, (g z).im ∈ Set.Ioo (-π) π
```

**Proof strategy**:
- Im(g) is a harmonic function on the right half-plane
- Im(g) = 0 on the positive real axis
- The right half-plane is simply connected
- exp(g z) = f z ≠ 0 implies Im(g z) ≢ kπ for any integer k ≠ 0
- By continuity from the real axis where Im(g) = 0, we get Im(g) ∈ (-π, π)

**Alternative approach**:
- Use that exp is a local homeomorphism away from its critical values
- The image under exp of {g : Im(g) = π} is the negative reals
- But f maps the right half-plane to ℂ \ {0}, so we can't hit negative reals
  without hitting 0 first (by intermediate value / connectedness)

**Dependencies**: PRs 1, 2, 3

**Status**: ⏳ Requires careful argument

---

### PR 5: Gamma Maps Right Half-Plane to SlitPlane (Final Goal)

**File location**: `Mathlib.Analysis.SpecialFunctions.Gamma.SlitPlane`

**Main theorem**:
```lean
/-- For z with Re z > 0, Γ(z) ∈ slitPlane.
    Equivalently, Γ(z) is not a non-positive real for Re z > 0. -/
theorem Gamma_mem_slitPlane_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    Gamma z ∈ slitPlane := by
  by_cases hreal : z.im = 0
  · -- z is a positive real: Γ(z) > 0
    have hz_real : z = (z.re : ℂ) := Complex.ext rfl hreal
    rw [hz_real, Gamma_ofReal]
    exact ofReal_mem_slitPlane.mpr (Gamma_pos_of_pos hz)
  · -- z is not real: use holomorphic log argument
    -- Key: On the right half-plane, log Γ exists holomorphically with
    -- Im(log Γ) = 0 on positive reals. By PR 4, Im(log Γ z) ∈ (-π, π).
    -- If Γ(z) < 0 (negative real), then Im(log Γ z) = π ∉ (-π, π). Contradiction.
    rw [mem_slitPlane_iff]
    by_contra h_not
    push_neg at h_not
    obtain ⟨hre_le, him_eq⟩ := h_not
    -- Γ(z) is a non-positive real, but Γ(z) ≠ 0
    have hGamma_ne_zero : Gamma z ≠ 0 := Gamma_ne_zero_of_re_pos hz
    have hGamma_neg : (Gamma z).re < 0 := ... -- from hre_le and hGamma_ne_zero
    -- Apply PR 4 to log Γ
    have hlog := im_holomorphic_log_Gamma z hz
    -- But Γ(z) < 0 implies Im(log Γ z) = π
    have harg : (log (Gamma z)).im = π := ...
    -- Contradiction: π ∉ (-π, π)
    linarith [hlog]
```

**Dependencies**: PRs 1-4, `Gamma_conj`, `Gamma_ne_zero_of_re_pos`, `Gamma_pos_of_pos`

**Status**: ⏳ Depends on earlier PRs

---

## Existing Infrastructure to Leverage

### Already in Mathlib
- `Complex.Gamma_conj`: Γ(conj z) = conj(Γ(z)) — Schwarz reflection for Gamma
- `Complex.Gamma_ne_zero_of_re_pos`: Γ(z) ≠ 0 for Re z > 0
- `Real.Gamma_pos_of_pos`: Γ(x) > 0 for x > 0
- `starConvex_one_slitPlane`: slitPlane is star-convex at 1
- `Complex.isOpen_slitPlane`: slitPlane is open
- `DifferentiableAt.clog`: log is holomorphic on slitPlane
- `Complex.log_ofReal_re`: log of positive real has Im = 0
- `SimplyConnectedSpace`: definition of simply connected spaces
- `Mathlib.Analysis.Complex.PhragmenLindelof`: tools for right half-plane

### In Riemann Folder (Portable)
- `BinetKernel.lean`: Binet integral infrastructure
- `BinetFormula.lean`: log Γ integral representation (partial)
- `GammaLogDeriv.lean`: digamma function and related

---

## Alternative Simpler Approach

If the full infrastructure above is too heavy, a simpler approach uses:

### PR Alt-1: Direct Proof Using Path Connectivity

```lean
/-- If f is continuous, nonzero on a path-connected domain, and positive
    on a nonempty subset S, then f cannot be negative anywhere. -/
theorem pos_of_continuous_nonzero_pos_somewhere {U : Set ℂ}
    (hU : IsPathConnected U) {f : ℂ → ℂ}
    (hf_cont : ContinuousOn f U) (hf_ne : ∀ z ∈ U, f z ≠ 0)
    {S : Set ℂ} (hS : S ⊆ U) (hS_ne : S.Nonempty)
    (hf_pos : ∀ z ∈ S, (f z).im = 0 ∧ 0 < (f z).re) :
    ∀ z ∈ U, (f z).im = 0 → 0 < (f z).re
```

This avoids logarithms entirely and uses only:
- Path connectivity of right half-plane
- Continuity of Gamma
- Gamma ≠ 0 on right half-plane
- Gamma > 0 on positive reals

**Proof sketch**:
- Suppose Γ(z₀) < 0 for some z₀ with z₀.re > 0
- Take a path γ from some positive real x to z₀
- Along γ, Γ is continuous and nonzero
- The function t ↦ (Γ(γ(t))).re changes from positive to negative
- By intermediate value, it must pass through 0
- But (Γ(w)).re = 0 and (Γ(w)).im = 0 implies Γ(w) = 0, contradiction

This approach requires showing that for z on the right half-plane:
- If Γ(z) is real and Γ(z) ≠ 0, then Γ(z) > 0

---

## Summary Table

| PR # | Content | Complexity | Dependencies |
|------|---------|------------|--------------|
| 1 | Right half-plane topology | Low | Standard topology |
| 2 | Holomorphic log on SC domains | High | Covering spaces or integrals |
| 3 | Schwarz reflection (general) | Medium | Identity theorem |
| 4 | Im(log f) bounds | Medium | PRs 1-3 |
| 5 | Gamma ∈ slitPlane | Low | PRs 1-4 |
| Alt-1 | Direct path approach | Medium | Path connectivity |

---

## Recommended Path

1. **Immediate**: Try the Alt-1 approach first — it's simpler and self-contained
2. **Medium term**: If Alt-1 is insufficient, develop PR 1-3
3. **Long term**: Full infrastructure (PR 2) is valuable for other applications

---

## Next Steps

1. Attempt Alt-1 direct proof in `GammaLogDeriv.lean`
2. If needed, start PR 1 (straightforward)
3. Evaluate whether PR 2-4 are worth the investment vs. sorrying the result

---

## Notes on Riemann Folder Leverage

The `BinetKernel.lean` and `BinetFormula.lean` files develop the Binet integral:
```
log Γ(z) = (z - 1/2) log z - z + log(2π)/2 + J(z)
```
where J(z) is real and positive for positive real z. This gives another approach:
if we can show J(z) has bounded imaginary part, then log Γ(z) has controlled
imaginary part, which implies Γ(z) ∈ slitPlane.

This is essentially the "explicit" version of the abstract logarithm argument.
