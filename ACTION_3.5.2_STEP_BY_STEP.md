# ACTION 3.5.2 Step-by-Step: Prove ∂ₓ(arctan_sum) ≤ 0

**Goal**: Prove the derivative wrt x is non-positive  
**Broken into**: 5 bite-sized steps (each 30-60 min)

---

## Mathematical Goal

Prove: `∂/∂x [arctan((1-x)/b) + arctan((1+x)/b)] ≤ 0` for x ∈ [-1,1], b ∈ (0,1]

**Strategy**: 
1. Compute derivative of each arctan term
2. Combine them
3. Show the sum is ≤ 0

---

## Step 1: Derivative of arctan((1-x)/b) (30 min)

**Add to PoissonPlateauNew.lean**:

```lean
/-- Derivative of first term: arctan((1-x)/b) -/
lemma deriv_arctan_first (b x : ℝ) (hb : 0 < b) :
  deriv (fun x => arctan ((1 - x) / b)) x = 
  (-1/b) / (1 + ((1 - x) / b)^2) := by
  -- Use chain rule: d/dx arctan(f(x)) = f'(x) / (1 + f(x)²)
  -- where f(x) = (1-x)/b, so f'(x) = -1/b
  sorry  -- Chain rule application
```

---

## Step 2: Derivative of arctan((1+x)/b) (30 min)

```lean
/-- Derivative of second term: arctan((1+x)/b) -/
lemma deriv_arctan_second (b x : ℝ) (hb : 0 < b) :
  deriv (fun x => arctan ((1 + x) / b)) x = 
  (1/b) / (1 + ((1 + x) / b)^2) := by
  -- Similar: f(x) = (1+x)/b, so f'(x) = 1/b
  sorry  -- Chain rule application
```

---

## Step 3: Sum of derivatives (30 min)

```lean
/-- Combined derivative of arctan_sum -/
lemma deriv_arctan_sum_formula (b x : ℝ) (hb : 0 < b) (b_le : b ≤ 1) :
  deriv (fun x => arctan_sum b x) x = 
  (-1/b) / (1 + ((1 - x) / b)^2) + (1/b) / (1 + ((1 + x) / b)^2) := by
  simp only [arctan_sum]
  -- Derivative of sum = sum of derivatives
  rw [deriv_add]
  · rw [deriv_arctan_first b x hb, deriv_arctan_second b x hb]
  · sorry  -- Differentiability of first term
  · sorry  -- Differentiability of second term
```

---

## Step 4: Algebraic simplification (45 min)

```lean
/-- Simplified form of the derivative -/
lemma deriv_arctan_sum_simplified (b x : ℝ) (hb : 0 < b) :
  (-1/b) / (1 + ((1 - x) / b)^2) + (1/b) / (1 + ((1 + x) / b)^2) =
  (1/b) * ((1 / (1 + ((1+x)/b)^2)) - (1 / (1 + ((1-x)/b)^2))) := by
  ring
```

---

## Step 5: Show sign is ≤ 0 (45 min)

```lean
/-- The derivative is non-positive for x ∈ [-1,1] -/
lemma deriv_arctan_sum_sign (b x : ℝ) (hb : 0 < b) (hx : |x| ≤ 1) :
  (1 / (1 + ((1+x)/b)^2)) - (1 / (1 + ((1-x)/b)^2)) ≤ 0 := by
  -- When x ∈ [-1,1] and b > 0:
  -- (1+x)/b ≥ (1-x)/b  (since x ≥ -x when scaled)
  -- So denominators: 1 + ((1+x)/b)² ≥ 1 + ((1-x)/b)²
  -- Therefore: 1/(1+((1+x)/b)²) ≤ 1/(1+((1-x)/b)²)
  -- So the difference is ≤ 0
  sorry  -- Inequality reasoning
```

---

## Step 6: Assembly (15 min)

```lean
/-- Main theorem: derivative is non-positive -/
theorem arctan_sum_deriv_x_nonpos (b : ℝ) (hb : 0 < b) (b_le : b ≤ 1) :
  ∀ x ∈ Set.Icc (-1) 1, 
    deriv (fun x => arctan_sum b x) x ≤ 0 := by
  intro x hx
  rw [deriv_arctan_sum_formula b x hb b_le]
  rw [deriv_arctan_sum_simplified b x hb]
  apply mul_nonpos_of_nonneg_of_nonpos
  · exact div_nonneg (by linarith : 0 ≤ 1) hb.le
  · exact deriv_arctan_sum_sign b x hb (by simpa using hx)
```

---

## Timeline

Each step: 30-60 min  
Total: 3-4 hours (can do in parts)

**We can start NOW with Step 1!**

---

*Let's begin with Step 1 - computing the first derivative.*
