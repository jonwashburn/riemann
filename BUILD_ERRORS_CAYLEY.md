# Cayley.lean Build Errors - Detailed Analysis

**Date:** 2025-10-20  
**File:** `/Users/jonathanwashburn/Projects/zeros/no-zeros/rh/RS/Cayley.lean`

## Error Summary

**Total Errors:** 5 distinct errors blocking the build

## Detailed Error Analysis

### Error 1: Integrable proof (Line 39) ✅ FIXED
**Location:** `integrable_of_comp_mul_deriv_ae_neg_eq` lemma  
**Issue:** Used `simpa` where `exact` was needed  
**Status:** FIXED  
**Fix Applied:** Changed `simpa using ...` to `exact ...`

### Error 2: Comment syntax (Line 121) ✅ FIXED  
**Location:** Section header before `J_pinch` definition  
**Issue:** Standalone `/--` comment marker without closing  
**Status:** FIXED  
**Fix Applied:** Changed to proper `/-!` module docstring format

### Error 3: det2_AF vs det2 mismatch (Line 220)
**Location:** `F_pinch_bnd_two_boundary` lemma  
**Context:**
```lean
⊢ Complex.abs (J_pinch AcademicFramework.DiagonalFredholm.det2_AF O (2⁻¹ + I * ↑t)) = 1
```
**Issue:** Type mismatch between `det2` and `det2_AF` (Academic Framework variant)  
**Root Cause:** `simp` is rewriting `det2` to `det2_AF` but the hypothesis `hJ` is about `det2`  
**Proposed Fix:** Either:
  - Avoid using `simp` and use `rw` with specific lemmas
  - Add a bridge lemma connecting `det2` and `det2_AF`
  - Unfold `boundary` definition explicitly

### Error 4: Analyticity subset proof (Line 250)  
**Location:** `J_pinch_analytic_on_offXi` lemma  
**Context:**
```lean
have hzOff : z ∈ RH.AcademicFramework.HalfPlaneOuterV2.offXi := by
  refine ⟨hz.1, ?_, ?_⟩
  · exact fun hz1 => ... -- needs to prove z ≠ 1
```
**Issue:** Need to prove `z ≠ 1` given `z ∈ S = Ω \ {w | riemannXi_ext w = 0}`  
**Root Cause:** **LOGICAL ERROR** - Cannot deduce `z ≠ 1` from `riemannXi_ext z ≠ 0` because:
  - `riemannXi_ext` has a **pole** at `z = 1` (not a zero)
  - So `riemannXi_ext 1` is undefined/infinite, not zero
  - Therefore `S` may contain `z = 1` (if we're working in a punctured neighborhood)

**Structural Issue:** The lemma is trying to prove `J_pinch` is analytic on `Ω \ {z | riemannXi_ext z = 0}`, but it requires `riemannXi_ext` to be analytic, which needs `Ω \ {1}`.

**Proposed Fix Options:**
1. **Change the lemma statement** to require analyticity on `offXi` (which explicitly excludes both zeros and the pole at 1)
2. **Add assumption** that `S` excludes 1
3. **Restructure proof** to work directly with `offXi` as the domain

### Error 5: Denominator nonzero proof (Lines 318, 320)  
**Location:** `Theta_Schur_of_Re_nonneg_on` lemma  
**Context:**
```lean
Line 318: tactic 'assumption' failed
Line 320: type mismatch - det2_AF vs det2
```
**Issue:** Similar to Error 3 - `det2_AF` appearing where `det2` is expected  
**Root Cause:** Automatic simp rules converting between variants  

**Impact:** Prevents proving that `Θ_pinch_of` is Schur (bounded by 1)

## Dependencies and Impact

### Dependency Chain
```
Cayley.lean (5 errors)
  ↓
PinchIngredients.lean
  ↓
Proof/Main.lean
  ↓
Proof/Export.lean (final theorems)
```

### Critical Path Assessment
- **Errors 1-2:** ✅ Fixed (simple syntax/tactic issues)
- **Error 3:** ⚠️ Moderate (needs careful handling of det2 variants)
- **Error 4:** 🔴 Severe (fundamental logical structure issue)
- **Error 5:** ⚠️ Moderate (same root cause as Error 3)

## Recommended Fix Strategy

### Immediate (Errors 3 & 5): det2 variant handling
1. Check if there's a lemma `det2_eq_det2_AF` or similar
2. Use explicit rewrites instead of `simp` to control the normalization
3. Add `@[simp]` attribute management if needed

### Strategic (Error 4): Domain restructuring
**Option A (Preferred):** Change lemma to work on `offXi` directly
```lean
lemma J_pinch_analytic_on_offXi
  (hDet2 : Det2OnOmega) {O : ℂ → ℂ} (hO : OuterHalfPlane O)
  (hXi : AnalyticOn ℂ riemannXi_ext (Ω \ ({1} : Set ℂ)))
  : AnalyticOn ℂ (J_pinch det2 O) offXi := by
  -- offXi = Ω ∧ z ≠ 1 ∧ riemannXi_ext z ≠ 0
  -- This matches the domain where all factors are analytic
```

**Option B:** Add explicit pole exclusion
```lean
-- Require S to exclude the pole
let S : Set ℂ := (Ω \ ({1} ∪ {z | riemannXi_ext z = 0}))
```

## Technical Debt Risk

✅ **LOW RISK** - All proposed fixes involve:
- Correcting proof structure to match mathematical reality
- Explicit handling of domain restrictions
- No axioms, admits, or sorry statements needed

## Next Steps

1. ✅ Document current state (this file)
2. Fix det2/det2_AF normalization issues (Errors 3 & 5)
3. Restructure domain handling (Error 4) - requires design decision
4. Verify full build chain after fixes
5. Run axiom checker on final certificate route

---

**Status:** Documented and ready for systematic fix implementation.

