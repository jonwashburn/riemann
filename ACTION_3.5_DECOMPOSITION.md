# ACTION 3.5 Decomposition: Minimization Calculus

**Parent Task**: Prove arctan_sum minimized at (b,x) = (1,1)  
**Estimated Total**: 1-2 days  
**Status**: Requires decomposition into sub-proofs

---

## Evaluation: Can This Be Done in One Session?

**NO** - This requires proving 4 distinct calculus lemmas, each needing careful derivative work.

---

## Mathematical Overview

**Goal**: Prove `arctan_sum b x ≥ arctan 2` for all (b,x) ∈ (0,1] × [-1,1]

**Where**: `arctan_sum b x := arctan((1-x)/b) + arctan((1+x)/b)`

**Strategy**: 
1. Show ∂/∂x ≤ 0 (decreasing in x)
2. Show ∂/∂b ≤ 0 (decreasing in b)
3. Therefore minimum at corner (b,x) = (1,1)
4. Compute: arctan_sum 1 1 = arctan(0) + arctan(2) = arctan(2)

---

## Decomposition into Atomic Tasks

### Sub-Task 3.5.1: Add Derivative Helpers (1 hour) ✅ **Session-sized**

**File**: `no-zeros/rh/RS/PoissonPlateauNew.lean`

**Add**:
```lean
/-! ### Derivative calculations for minimization -/

/-- Derivative of arctan(f(x)) where f is differentiable. -/
axiom deriv_arctan_comp : ∀ f : ℝ → ℝ, ∀ x : ℝ,
  DifferentiableAt ℝ f x →
  deriv (fun x => arctan (f x)) x = (deriv f x) / (1 + (f x)^2)

/-- arctan(0) = 0 (standard). -/
axiom arctan_zero : arctan 0 = 0

/-- arctan is increasing (standard). -/
axiom arctan_strictMono : StrictMono arctan
```

---

### Sub-Task 3.5.2: Prove ∂ₓ(arctan_sum) ≤ 0 (3-4 hours) ⚠️ **Core calculus**

**File**: `no-zeros/rh/RS/PoissonPlateauNew.lean`

**Add**:
```lean
/-- Partial derivative of arctan_sum with respect to x.
Computation:
  ∂/∂x [arctan((1-x)/b) + arctan((1+x)/b)]
  = ∂/∂x arctan((1-x)/b) + ∂/∂x arctan((1+x)/b)
  = (-1/b) / (1 + ((1-x)/b)²) + (1/b) / (1 + ((1+x)/b)²)
  = ... ≤ 0 for x ∈ [-1,1], b > 0
-/
theorem arctan_sum_deriv_x_nonpos (b : ℝ) (hb : 0 < b) :
  ∀ x ∈ Set.Icc (-1) 1, 
    deriv (fun x => arctan_sum b x) x ≤ 0 := by
  intro x hx
  simp only [arctan_sum]
  
  -- Apply chain rule to each arctan
  have d1 : deriv (fun x => arctan ((1 - x) / b)) x = 
            (-1/b) / (1 + ((1 - x) / b)^2) := by
    sorry  -- MUST PROVE: chain rule application
  
  have d2 : deriv (fun x => arctan ((1 + x) / b)) x = 
            (1/b) / (1 + ((1 + x) / b)^2) := by
    sorry  -- MUST PROVE: chain rule application
  
  -- Sum of derivatives
  have d_sum : deriv (fun x => arctan_sum b x) x = 
               (-1/b) / (1 + ((1 - x) / b)^2) + 
               (1/b) / (1 + ((1 + x) / b)^2) := by
    sorry  -- Can admit: deriv addition rule
  
  -- Show this is ≤ 0
  rw [d_sum]
  sorry  -- MUST PROVE: algebraic inequality
```

**Admits allowed**: Chain rule, deriv linearity  
**Must prove**: Derivative formulas, sign analysis

---

### Sub-Task 3.5.3: Prove ∂ᵦ(arctan_sum) ≤ 0 (3-4 hours) ⚠️ **Core calculus**

**File**: `no-zeros/rh/RS/PoissonPlateauNew.lean`

**Add**:
```lean
/-- Partial derivative of arctan_sum with respect to b is non-positive. -/
theorem arctan_sum_deriv_b_nonpos (x : ℝ) (hx : |x| ≤ 1) :
  ∀ b ∈ Set.Ioc 0 1, 
    deriv (fun b => arctan_sum b x) b ≤ 0 := by
  intro b hb
  simp only [arctan_sum]
  
  -- Similar chain rule computation for b
  sorry  -- MUST PROVE: similar to Sub-Task 3.5.2
```

---

### Sub-Task 3.5.4: Prove Minimum at (1,1) (2-3 hours) ⚠️ **Composition**

**File**: `no-zeros/rh/RS/PoissonPlateauNew.lean`

**Add**:
```lean
/-- The minimum of arctan_sum over (b,x) ∈ (0,1] × [-1,1] occurs at (1,1). -/
theorem arctan_sum_minimum_at_one_one :
  ∀ b x, 0 < b → b ≤ 1 → |x| ≤ 1 →
    arctan_sum b x ≥ arctan_sum 1 1 := by
  intro b x hb_pos hb_le hx
  
  -- From monotonicity, minimum at corner
  have mono_x : arctan_sum b x ≥ arctan_sum b 1 := by
    sorry  -- MUST PROVE: use Sub-Task 3.5.2
  
  have mono_b : arctan_sum b 1 ≥ arctan_sum 1 1 := by
    sorry  -- MUST PROVE: use Sub-Task 3.5.3
  
  linarith

/-- Value at (1,1): arctan_sum 1 1 = arctan(2). -/
theorem arctan_sum_at_one_one : arctan_sum 1 1 = arctan 2 := by
  simp [arctan_sum]
  -- arctan((1-1)/1) + arctan((1+1)/1) = arctan(0) + arctan(2)
  rw [arctan_zero]
  simp

/-- Main minimization result. -/
theorem arctan_sum_ge_arctan_two :
  ∀ b x, 0 < b → b ≤ 1 → |x| ≤ 1 →
    arctan_sum b x ≥ arctan 2 := by
  intro b x hb hb1 hx
  calc arctan_sum b x
      ≥ arctan_sum 1 1 := arctan_sum_minimum_at_one_one b x hb hb1 hx
    _ = arctan 2 := arctan_sum_at_one_one
```

**Must prove**: Use monotonicity results from 3.5.2 and 3.5.3

---

## Task Dependency Graph

```
3.5.1 (Helpers) → 3.5.2 (∂ₓ ≤ 0) → 3.5.4 (Minimum)
                → 3.5.3 (∂ᵦ ≤ 0) → 3.5.4 (Minimum)
```

**Critical path**: 3.5.1 → {3.5.2, 3.5.3} → 3.5.4  
**Can parallelize**: 3.5.2 and 3.5.3 can be done independently

---

## Session Plan for ACTION 3.5

### Session 1 (1 hour): Setup
- Complete Sub-Task 3.5.1 (add helpers)
- Add theorem structures for 3.5.2, 3.5.3, 3.5.4
- Verify build

### Session 2 (Half day): Derivative Proofs
- Work on Sub-Task 3.5.2 (∂ₓ ≤ 0)
- Chain rule, algebra

### Session 3 (Half day): Second Derivative
- Work on Sub-Task 3.5.3 (∂ᵦ ≤ 0)
- Similar to 3.5.2

### Session 4 (2-3 hours): Assembly
- Complete Sub-Task 3.5.4 (minimum at corner)
- Final theorem composition

**Total**: 4 sessions over 1-2 days

---

## What Can Be Done NOW (Sub-Task 3.5.1)

**Add derivative helpers and theorem structures** - can complete in next hour:
- Add standard derivative lemmas (axioms)
- Add theorem shells for 3.5.2, 3.5.3, 3.5.4
- Document proof strategy
- Verify build

**Estimated time**: 1 hour  
**Difficulty**: Low (mostly structure)  
**Risk**: Low (admits are standard)

---

## Recommendation

**CONTINUE NOW**: Execute Sub-Task 3.5.1 to set up the minimization proof structure.

This completes the scaffolding for ACTION 3, leaving only the calculus proofs for a future focused session.

---

*Decomposition complete. Ready to execute Sub-Task 3.5.1.*
