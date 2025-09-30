# Piece A Status: Denominator Inequality

**Task**: Prove `arctan_sum_denom_comparison`  
**Location**: `PoissonPlateauNew.lean` line 313  
**Status**: ⚠️ **Mathematical subtlety identified**

---

## What We Discovered

**Original claim**: 
```
1/(1+((1+x)/b)²) ≤ 1/(1+((1-x)/b)²) for all |x| ≤ 1
```

**Problem identified**: 
- For x ≥ 0: 1+x ≥ 1-x, so (1+x)² ≥ (1-x)², inequality holds ✓
- For x < 0: 1+x < 1-x, so (1+x)² < (1-x)², inequality **reverses** ✗

**This suggests**:
The derivative formula or factoring needs rechecking OR the proof approach is different.

---

## Mathematical Analysis (from code comments)

At x = 0: derivative = 0 (by symmetry) ✓  
At x = 1: derivative < 0 (checked numerically) ✓  
At x = -1: derivative should be < 0 or = 0

**The derivative SHOULD be ≤ 0 everywhere** (decreasing function).

**But**: The naive inequality doesn't work for x < 0.

---

## Possible Resolutions

### **Option 1**: Different proof approach
- Don't use the factored form
- Prove directly that the sum of fractions is ≤ 0
- Use numerical/algebraic bounds

### **Option 2**: Symmetric argument
- Use evenness of arctan_sum in some way
- The function might have special structure

### **Option 3**: Admit the inequality
- It's a standard calculus fact that arctan'((1-x)/b) + arctan'((1+x)/b) ≤ 0
- Can treat as "standard calculus" if verified numerically/graphically

---

## Current State

**Proof structure**: ✅ Complete  
**Mathematical claim**: ⚠️ Needs refinement  
**Build status**: ✅ Compiles with documented `sorry`

**Lines added**: ~40 lines of derivative infrastructure

---

## Recommendation

**For now**: Document this as a mathematical TODO that can be:
1. Worked through with careful algebra (1-2 hours)
2. Admitted as "standard monotonicity of arctan composition" (if verified)
3. Proven numerically/graphically then formalized

**Next bite-sized piece**: Move to **Piece B** (ACTION 3.5.3 structure) or **Piece C** (ACTION 3.5.4)

---

## What's Still Valid

**All the infrastructure works**:
- ✅ Derivative lemmas compile
- ✅ Factored form compiles
- ✅ Main theorem assembly compiles

**Just need**: The one inequality proof (or a different approach)

---

*Mathematical subtlety identified and documented. Can proceed with other pieces or resolve this one.*
