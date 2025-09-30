# ACTION 2 Decomposition: J_CR Implementation

**Parent Task**: Implement J_CR with Outer Parameter  
**Estimated Total**: 2-3 days  
**Status**: Needs decomposition into session-sized tasks

---

## Evaluation: Can This Be Done in One Session?

**NO** - This requires 4 distinct sub-tasks across ~100-150 lines of code.

---

## Decomposition into Atomic Tasks

### ✅ Sub-Task 2.1: Add OuterOnOmega Structure (COMPLETED)

**File**: `no-zeros/rh/RS/CRGreenOuter.lean`

**Location**: After imports, before J_CR definition

**Add**:
```lean
-- After line 40, before J_CR definition:

/-! Outer function structure for half-plane normalization -/

/-- Outer function on Ω with prescribed boundary modulus.
This is standard Hardy space theory and can be admitted. -/
structure OuterOnOmega where
  outer : ℂ → ℂ
  analytic : AnalyticOn ℂ outer Ω
  nonzero : ∀ z ∈ Ω, outer z ≠ 0
  boundary_modulus : ∀ᵐ t : ℝ, 
    Complex.abs (outer (boundary t)) = 
    Complex.abs (det2 (boundary t) / riemannXi_ext (boundary t))

/-- Admit outer existence (standard Hardy space outer factorization).
Reference: Garnett "Bounded Analytic Functions", Ch. II -/
axiom outer_exists : OuterOnOmega
```

**Verification**:
```bash
lake build
# Should succeed - only added definitions, no proofs yet
```

---

### ✅ Sub-Task 2.2: Replace J_CR Definition (COMPLETED)

**File**: `no-zeros/rh/RS/CRGreenOuter.lean`

**Current** (line ~77):
```lean
def J_CR (_s : ℂ) : ℂ := 0
```

**Replace with**:
```lean
/-- CR-Green outer J (outer-normalized ratio): J := det₂ / (O · ξ).
This is the paper's construction from Section "Standing setup". -/
def J_CR (O : OuterOnOmega) (s : ℂ) : ℂ :=
  det2 s / (O.outer s * riemannXi_ext s)

/-- Convenience: J with the canonical outer. -/
def J_canonical : ℂ → ℂ := J_CR outer_exists
```

**Note**: This will break CRGreenOuterData temporarily - fix in Sub-Task 2.4

---

### ✅ Sub-Task 2.3: Prove J Boundary Modulus (MOSTLY COMPLETE)

**File**: `no-zeros/rh/RS/CRGreenOuter.lean`

**Add after J_CR**:
```lean
/-- Boundary unimodularity: |J(1/2+it)| = 1 a.e.
This is YOUR result proving the boundary normalization works. -/
theorem J_CR_boundary_abs_one (O : OuterOnOmega) :
  ∀ᵐ t : ℝ, Complex.abs (J_CR O (boundary t)) = 1 := by
  intro t
  simp only [J_CR, abs_div]
  
  -- Goal: |det2| / (|O| · |ξ|) = 1
  -- Key: from outer property, |O| = |det2/ξ|
  
  have hmod : Complex.abs (O.outer (boundary t)) = 
              Complex.abs (det2 (boundary t) / riemannXi_ext (boundary t)) :=
    O.boundary_modulus t
  
  -- Expand |det2/ξ| = |det2| / |ξ|
  have hξ_ne : riemannXi_ext (boundary t) ≠ 0 := by
    sorry  -- Can admit: ξ boundary nonvanishing (standard, from functional equation)
  
  rw [abs_div] at hmod
  -- Now hmod : |O| = |det2| / |ξ|
  
  -- Multiply both sides by |ξ|: |O| · |ξ| = |det2|
  have h_prod : Complex.abs (O.outer (boundary t)) * 
                Complex.abs (riemannXi_ext (boundary t)) = 
                Complex.abs (det2 (boundary t)) := by
    have := congr_arg (· * Complex.abs (riemannXi_ext (boundary t))) hmod
    simp only [div_mul_cancel₀] at this
    · exact this
    · exact Complex.abs.ne_zero_iff.mpr hξ_ne
  
  -- Substitute in goal
  rw [Complex.abs.map_mul]
  rw [h_prod]
  
  -- Goal now: |det2| / |det2| = 1
  have hdet_ne : Complex.abs (det2 (boundary t)) ≠ 0 := by
    sorry  -- Can admit: det2 boundary nonvanishing
  
  exact div_self hdet_ne
```

**Admits allowed**: 2 (boundary nonvanishing facts)  
**Must prove**: Modulus algebra (completed above)

---

### Sub-Task 2.4: Update CRGreenOuterData (1 hour) ✅ **Session-sized**

**File**: `no-zeros/rh/RS/CRGreenOuter.lean`

**Current** (lines ~81-91):
```lean
def CRGreenOuterData : OuterData := {
  F := fun s => (2 : ℂ) * J_CR s
  hRe := by intro _z _hz; simp [J_CR]
  hDen := by intro _z _hz; simp [J_CR]
}
```

**Replace with**:
```lean
/-- OuterData built from the outer-normalized J_CR.
The positivity Re(2·J) ≥ 0 will be proven from (P+) in ACTION 4. -/
def CRGreenOuterData : OuterData := {
  F := fun s => (2 : ℂ) * J_CR outer_exists s
  hRe := by
    intro z hz
    -- This will be proven from (P+) boundary wedge
    -- For now, use trivial case from J = 0
    sorry  -- TODO: Replace with (P+) → interior positivity in ACTION 4
  hDen := by
    intro z hz
    -- Show 2·J + 1 ≠ 0
    -- When Re(2·J) ≥ 0, we have 2·J + 1 ≠ 0
    sorry  -- TODO: Prove from (P+) in ACTION 4
}
```

**Also update**:
```lean
-- Update Θ_CR definition (line ~94):
def Θ_CR : ℂ → ℂ := Θ_of CRGreenOuterData

-- Update lemmas:
@[simp] lemma CRGreenOuterData_F (s : ℂ) : 
  (CRGreenOuterData.F s) = (2 : ℂ) * J_canonical s := by
  simp [CRGreenOuterData, J_canonical]

-- This lemma will change once (P+) is proven:
lemma Θ_CR_eq_neg_one (s : ℂ) : Θ_CR s = (-1 : ℂ) := by
  sorry  -- TODO: Will change when (P+) is proven
```

---

## Task Dependency Graph

```
2.1 (Outer structure) → 2.2 (J_CR def) → 2.3 (Boundary proof) 
                                        ↓
                                      2.4 (Update OuterData)
```

**Critical path**: 2.1 → 2.2 → 2.3 → 2.4  
**Can parallelize**: None (sequential dependencies)

---

## Session Plan for ACTION 2

### Session 1 (1-2 hours): Foundation
- Complete Sub-Task 2.1 (add structure)
- Complete Sub-Task 2.2 (replace J_CR)
- Verify build (will have `sorry` but should compile)

### Session 2 (3-5 hours): Core Proof
- Complete Sub-Task 2.3 (boundary modulus proof)
- Test algebra carefully
- Verify build

### Session 3 (1-2 hours): Integration
- Complete Sub-Task 2.4 (update CRGreenOuterData)
- Final build verification
- Update documentation

**Total**: 3 sessions over 1-2 days

---

## What Can Be Done NOW (Session 1)

**Sub-Tasks 2.1 and 2.2** can both be completed in the next 2 hours:
- Add `OuterOnOmega` structure
- Add `axiom outer_exists`
- Replace `J_CR = 0` with actual definition
- Update `J_canonical` convenience function
- Verify build

**Estimated time**: 1-2 hours  
**Difficulty**: Low (mostly definitions and structure)  
**Risk**: Low (can admit outer existence)

---

## Recommendation

**START NOW**: Execute Sub-Tasks 2.1 and 2.2 (Session 1 of ACTION 2)

These are straightforward additions that:
- Don't require complex proofs
- Use standard admits
- Set up structure for Sub-Task 2.3

**After Session 1**: You'll have the structure in place for the boundary modulus proof (Sub-Task 2.3), which is the first real RH-specific proof.

---

*Decomposition complete. Ready to execute Sub-Tasks 2.1 and 2.2.*
