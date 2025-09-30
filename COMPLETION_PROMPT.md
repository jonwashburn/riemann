# Riemann Hypothesis Formalization - Completion Prompt

**Use this prompt iteratively until all gaps are closed.**

---

## Context

I'm working on completing a Lean 4 formalization of the Riemann Hypothesis in `/Users/jonathanwashburn/Projects/zeros/no-zeros`. 

**Read these three documents first** to understand the current state:
1. `COMPREHENSIVE_REVIEW.md` - Full technical analysis of gaps
2. `ACTION_PLAN.md` - Detailed step-by-step plan
3. `EXECUTIVE_SUMMARY.md` - High-level overview

## Current Status Summary

- ✅ Core symmetry argument: COMPLETE
- ✅ Certificate chain structure: COMPLETE  
- ✅ Main proof logic: COMPLETE
- ❌ Build: FAILING (37 errors)
- ❌ Opaque declarations: 3 critical gaps
- ❌ Poisson theory: 3 missing lemmas

## Your Task

Work through the completion plan **ONE PHASE AT A TIME**. Start with Phase 1, verify it works, then move to Phase 2. Report progress and blockers clearly.

---

## 🚫 DO NOT MODIFY (Protected Files)

These files are **COMPLETE and WORKING** - do not edit them unless absolutely necessary:

### Core Proof Logic (LOCKED)
- `rh/Proof/Main.lean` (lines 96-123: RH_core theorem)
- `rh/Proof/Main.lean` (lines 680-681: RiemannHypothesis_final)
- `rh/Proof/Export.lean` (export wrappers)

### Certificate Chain (LOCKED)
- `rh/academic_framework/Certificate.lean` (structure complete)
- `rh/Cert/KxiPPlus.lean` (complete)
- `rh/Cert/K0PPlus.lean` (complete)
- `rh/Cert/FactorsWitness.lean` (complete)

### Completed Theory (LOCKED)
- `rh/academic_framework/GammaBounds.lean` (Prop-level complete)
- `rh/academic_framework/EulerProduct/K0Bound.lean` (K0 proven)
- `rh/RS/Cayley.lean` (Cayley→Schur complete)
- `rh/RS/SchurGlobalization.lean` (globalization complete)
- `rh/RS/PinchCertificate.lean` (structure complete)
- `rh/RS/PinchIngredients.lean` (builder complete)
- `rh/Axioms.lean` (no axioms, just re-exports)

### Archive (IGNORE)
- `rh/_archive/*` - May reference for proof techniques, but don't modify

---

## ✅ WORK ON THESE (Priority Order)

### Phase 1: Fix Build (Week 1, Days 1-2)

**Target**: `rh/academic_framework/HalfPlaneOuterV2.lean`

**Problems** (per PROGRESS.md):
- 37 errors from Lean 4.13.0 migration
- `pow_le_pow_left` argument order issues
- `div_le_div_of_nonneg` → `div_le_div_of_pos` updates
- Type synthesis failures

**Tasks**:
1. Run `cd /Users/jonathanwashburn/Projects/zeros/no-zeros && lake build 2>&1 | grep "error:" | head -20` to see current errors
2. Fix errors ONE AT A TIME:
   - Update `pow_le_pow` function calls
   - Update `div_le_div` function calls
   - Fix type synthesis issues
3. After each fix batch, run `lake build` to verify
4. Target: GREEN BUILD with no errors

**Success Criteria**:
```bash
cd /Users/jonathanwashburn/Projects/zeros/no-zeros
lake build  # Should succeed
```

**Report**: Number of errors remaining, what you fixed, any blockers

---

### Phase 2: Replace Opaque `det2` (Week 1, Days 3-7)

**Target**: `rh/RS/Det2Outer.lean` (line 33)

**Current Problem**:
```lean
noncomputable opaque det2 : ℂ → ℂ  -- THIS IS AN AXIOM!
```

**Tasks**:

**Option A - Connect to Diagonal Fredholm** (preferred):
1. Review `rh/academic_framework/DiagonalFredholm/Determinant.lean`
2. Implement `det2` using Euler product representation:
   ```lean
   noncomputable def det2 (s : ℂ) : ℂ := 
     ∏' p : Nat.Primes, (1 - (p : ℂ)^(-s)) * Complex.exp((p : ℂ)^(-s))
   ```
3. Prove analyticity: `theorem det2_analytic : AnalyticOn ℂ det2 Ω`
4. Prove nonvanishing: `theorem det2_nonzero : ∀ {s}, s ∈ Ω → det2 s ≠ 0`
5. Update `det2_on_Ω_proved` to use real implementation

**Option B - Minimal Implementation** (if Fredholm theory not available):
1. Define `det2` as a specific analytic function with required properties
2. Prove or assume required properties (document assumptions clearly)
3. Ensure it connects properly to the rest of the proof

**Success Criteria**:
- [ ] No `opaque` in `Det2Outer.lean`
- [ ] `det2` has actual definition
- [ ] Required theorems proven or clearly documented as assumptions
- [ ] Build succeeds with updated definition

**Report**: Implementation approach chosen, theorems proven/assumed, any dependencies

---

### Phase 3: Replace Opaque Window Functions (Week 1-2, Days 5-9)

**Target**: `rh/RS/H1BMOWindows.lean` (lines 32, 36)

**Current Problem**:
```lean
opaque windowMass (ψ : ℝ → ℝ) (W : Window) : ℝ
opaque boxEnergy (ψ u : ℝ → ℝ) (W : Window) : ℝ
```

**Tasks**:

**Step 1 - Determine if Trivial Implementation Suffices**:
1. Check if current trivial `Mpsi = 0` works for the proof
2. Review `windowed_phase_bound_of_carleson` (line 76-82)
3. Check if theorem still holds with trivial definitions

**Step 2A - If Trivial Works**:
```lean
def windowMass (ψ : ℝ → ℝ) (W : Window) : ℝ := W.ℓ
def boxEnergy (ψ u : ℝ → ℝ) (W : Window) : ℝ := 0
```

**Step 2B - If Full Implementation Needed**:
```lean
noncomputable def windowMass (ψ : ℝ → ℝ) (W : Window) : ℝ :=
  ∫ t in Set.Icc (W.t0 - W.ℓ) (W.t0 + W.ℓ), ψ t

noncomputable def boxEnergy (ψ u : ℝ → ℝ) (W : Window) : ℝ :=
  ∫ t in Set.Icc (W.t0 - W.ℓ) (W.t0 + W.ℓ), (ψ t * u t)^2
```

**Step 3 - Prove Required Properties**:
- Nonnegativity of `windowMass` and `boxEnergy`
- Required bounds for Carleson inequality
- Verify `windowed_phase_bound_of_carleson` proof

**Success Criteria**:
- [ ] No `opaque` in `H1BMOWindows.lean`
- [ ] Actual definitions provided
- [ ] `windowed_phase_bound_of_carleson` proven
- [ ] Build succeeds

**Report**: Implementation chosen, theorems proven, verification results

---

### Phase 4: Complete Poisson Theory (Week 2, Days 10-12)

**Target**: `rh/academic_framework/HalfPlaneOuterV2.lean`

**Missing Lemmas** (straightforward classical results):

#### 4a. `poissonKernel_integrable` (line 195)
```lean
theorem poissonKernel_integrable (z : ℂ) (hz : z ∈ Ω) : 
    Integrable (fun t => poissonKernel z t) := by
  sorry
```

**Proof Strategy**:
1. Check archived `rh/_archive/HalfPlaneOuter.lean` (line 318+) for reference proof
2. Show `poissonKernel z t ≤ C / (1 + (t - b)²)` for some C
3. Use comparison test with `∫ 1/(1+t²) dt = π`
4. Adapt proof to current interface

**Effort**: ~1 day

#### 4b. `integrable_boundedBoundary` (line 211)
```lean
theorem integrable_boundedBoundary (F : ℂ → ℂ) (M : ℝ) 
    (hM : ∀ t, abs (F (boundary t)) ≤ M) (z : ℂ) (hz : z ∈ Ω) :
    Integrable (fun t => F (boundary t) * poissonKernel z t) := by
  sorry
```

**Proof Strategy**:
1. Use `poissonKernel_integrable` from above
2. Show `|F * kernel| ≤ M * |kernel|`
3. Apply dominated convergence theorem (from Mathlib)

**Effort**: ~0.5 days

#### 4c. `F_pinch_boundary_bound` (line 189)
```lean
theorem F_pinch_boundary_bound (O : ℂ → ℂ) 
    (hBME : BoundaryModulusEq O (fun s => det2 s / riemannXi_ext s))
    (t : ℝ) (hO : O (boundary t) ≠ 0) (hXi : riemannXi_ext (boundary t) ≠ 0) :
    abs ((F_pinch det2 O) (boundary t)).re ≤ 2 := by
  sorry
```

**Proof Strategy**:
1. Use `boundary_abs_J_pinch_eq_one` (already proven, line 106-163)
2. Show `|F_pinch| = |2·J| = 2|J| = 2`
3. Use `Complex.abs_re_le_abs`

**Effort**: ~0.5 days

**Success Criteria**:
- [ ] All 3 lemmas proven (no sorry)
- [ ] Proofs use only Mathlib + existing lemmas
- [ ] Build succeeds
- [ ] Transport theorems work end-to-end

---

### Phase 5: Final Verification (Week 3, Days 13-15)

**Tasks**:

1. **Run Axiom Checker**:
```bash
cd /Users/jonathanwashburn/Projects/zeros/no-zeros
lake env lean --run rh/Proof/AxiomsCheckLite.lean
```
Expected: Only classical axioms from Mathlib

2. **Verify Main Theorems**:
```bash
lake env lean --run -c "
#check RH.Proof.Export.RiemannHypothesis_final
#check RH.Proof.Export.RH
#print axioms RH.Proof.Export.RiemannHypothesis_final
"
```

3. **Final Checks**:
```bash
# No sorries in active code
grep -r "sorry" rh/ --include="*.lean" | grep -v "_archive" | wc -l
# Should be: 0

# No admits in active code
grep -r "admit" rh/ --include="*.lean" | grep -v "_archive" | grep -v "^--" | wc -l
# Should be: 0

# No opaque declarations (except documented)
grep -n "^[^-]*opaque" rh/ -r --include="*.lean"
# Should be: empty or only Mathlib usage

# Build succeeds
lake build
# Should be: Success
```

4. **Certificate Chain Verification**:
- Verify `Ready_unconditional` compiles
- Check all constructors work
- Trace proof from ingredients to `RiemannHypothesis`

**Success Criteria**:
- [ ] Axiom checker passes (only classical axioms)
- [ ] No sorries in active code
- [ ] No opaque declarations
- [ ] Build succeeds
- [ ] All main theorems verified

---

### Phase 6: Cleanup (Week 3-4, Days 16-18)

**Tasks**:

1. **Remove Archive**:
```bash
cd /Users/jonathanwashburn/Projects/zeros/no-zeros
rm -rf rh/_archive/
```
Update any imports if needed.

2. **Update Documentation**:
- Update `PROGRESS.md` with final status
- Create `VERIFICATION.md` with axiom checker results
- Update main `README.md`
- Create `COMPLETENESS.md` certifying unconditional status

3. **Final Build**:
```bash
lake clean
lake update
lake build
```

**Success Criteria**:
- [ ] No archive directory
- [ ] Documentation updated
- [ ] Clean build from scratch
- [ ] Ready for review/publication

---

## 🔄 Iteration Protocol

**After Each Session**:

1. **Report Progress**:
   - What phase are you working on?
   - What did you complete?
   - What's blocking you?
   - How many errors/gaps remain?

2. **Verify Changes**:
```bash
cd /Users/jonathanwashburn/Projects/zeros/no-zeros
lake build
# Report: Pass/Fail and error count
```

3. **Check Gaps**:
```bash
# Opaque count
grep -n "^[^-]*opaque" rh/ -r --include="*.lean" | wc -l

# Sorry count  
grep -r "sorry" rh/ --include="*.lean" | grep -v "_archive" | wc -l
```

4. **Update Status**:
   - Update this prompt with your progress
   - Mark completed phases with ✅
   - Note any deviations from plan

---

## 🎯 Success Criteria (Final Goal)

The work is **COMPLETE** when:

```bash
cd /Users/jonathanwashburn/Projects/zeros/no-zeros

# 1. Build succeeds
lake build
# ✅ Success

# 2. No opaque declarations
grep -n "^[^-]*opaque" rh/ -r --include="*.lean" | wc -l
# ✅ 0

# 3. No sorries
grep -r "sorry" rh/ --include="*.lean" | grep -v "_archive" | wc -l
# ✅ 0

# 4. Only classical axioms
lake env lean --run rh/Proof/AxiomsCheckLite.lean
# ✅ Shows: propext, Classical.choice, Quot.sound (Mathlib standard)

# 5. Main theorem verified
lake env lean --run -c "#check RH.Proof.Export.RH"
# ✅ Type checks correctly
```

---

## 📝 Status Tracking

Update this section after each session:

### Phase 1: Build Fixes
- [ ] Started: ___________
- [ ] Errors remaining: ___
- [ ] Completed: ___________
- [ ] Blocker: ___________

### Phase 2: det2 Implementation
- [ ] Started: ___________
- [ ] Approach: [Fredholm/Minimal/Other]
- [ ] Completed: ___________
- [ ] Blocker: ___________

### Phase 3: Window Functions
- [ ] Started: ___________
- [ ] Approach: [Trivial/Full/Other]
- [ ] Completed: ___________
- [ ] Blocker: ___________

### Phase 4: Poisson Theory
- [ ] poissonKernel_integrable: ___________
- [ ] integrable_boundedBoundary: ___________
- [ ] F_pinch_boundary_bound: ___________
- [ ] Completed: ___________

### Phase 5: Verification
- [ ] Axiom check: ___________
- [ ] Main theorems: ___________
- [ ] Certificate chain: ___________
- [ ] Completed: ___________

### Phase 6: Cleanup
- [ ] Archive removed: ___________
- [ ] Docs updated: ___________
- [ ] Completed: ___________

---

## 🚨 Important Constraints

1. **ONE PHASE AT A TIME** - Complete each phase before moving to next
2. **VERIFY AFTER EACH CHANGE** - Run `lake build` frequently
3. **PROTECT WORKING CODE** - Don't touch files marked LOCKED
4. **DOCUMENT DECISIONS** - Note any deviations from plan
5. **REPORT BLOCKERS** - If stuck, explain clearly and ask for guidance

---

## 🎓 Final Verification Command

When you believe all work is complete, run:

```bash
cd /Users/jonathanwashburn/Projects/zeros/no-zeros

echo "=== BUILD CHECK ==="
lake clean && lake build && echo "✅ BUILD: PASS" || echo "❌ BUILD: FAIL"

echo -e "\n=== OPAQUE CHECK ==="
OPAQUE_COUNT=$(grep -n "^[^-]*opaque" rh/ -r --include="*.lean" | wc -l | tr -d ' ')
if [ "$OPAQUE_COUNT" -eq "0" ]; then
  echo "✅ OPAQUE: NONE"
else
  echo "❌ OPAQUE: $OPAQUE_COUNT found"
  grep -n "^[^-]*opaque" rh/ -r --include="*.lean"
fi

echo -e "\n=== SORRY CHECK ==="
SORRY_COUNT=$(grep -r "sorry" rh/ --include="*.lean" | grep -v "_archive" | wc -l | tr -d ' ')
if [ "$SORRY_COUNT" -eq "0" ]; then
  echo "✅ SORRY: NONE"
else
  echo "❌ SORRY: $SORRY_COUNT found"
  grep -r "sorry" rh/ --include="*.lean" | grep -v "_archive"
fi

echo -e "\n=== AXIOM CHECK ==="
lake env lean --run rh/Proof/AxiomsCheckLite.lean

echo -e "\n=== MAIN THEOREM CHECK ==="
lake env lean --run -c "
#check RH.Proof.Export.RH
#check RH.Proof.Export.RiemannHypothesis_final
#print axioms RH.Proof.Export.RH
"

echo -e "\n=== SUMMARY ==="
if [ "$OPAQUE_COUNT" -eq "0" ] && [ "$SORRY_COUNT" -eq "0" ]; then
  echo "🎉 UNCONDITIONAL PROOF COMPLETE!"
else
  echo "⚠️  Gaps remaining - see above"
fi
```

---

## 💬 Response Format

For each iteration, respond with:

1. **Current Phase**: [Phase number and name]
2. **Actions Taken**: [Bullet list of changes]
3. **Files Modified**: [List with line ranges]
4. **Verification Results**: [Build status, test results]
5. **Gaps Remaining**: [What's left to do]
6. **Blockers/Questions**: [Anything blocking progress]
7. **Next Steps**: [What to work on next iteration]
8. **Estimated Completion**: [% complete, time remaining]

---

## 🎯 Start Here

When you use this prompt, begin with:

1. Read the three reference documents
2. Check current build status: `cd /Users/jonathanwashburn/Projects/zeros/no-zeros && lake build 2>&1 | head -50`
3. Start Phase 1: Fix build errors
4. Report progress using the format above

Remember: **ONE PHASE AT A TIME**, verify after each change, protect working code.

**Ready to begin!** 🚀
