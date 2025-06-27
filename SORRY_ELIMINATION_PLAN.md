# Sorry Elimination Action Plan

Based on the analysis, here's a prioritized plan to eliminate all 72 sorries efficiently.

## Quick Wins (Start Here!)

### 1. EulerProduct/PrimeSeries.lean (1 sorry)
- **Time estimate**: 15 minutes
- **Action**: Likely a simple summability result about `∑ 1/p^s`
- **Try**: `Real.summable_one_div_nat_rpow`

### 2. EulerProductMathlib.lean (1 sorry)  
- **Time estimate**: 15 minutes
- **Action**: Check what the sorry is about
- **Try**: `library_search` or `exact?`

### 3. AnalyticContinuation.lean (2 sorries)
- **Time estimate**: 30 minutes
- **Action**: Likely about holomorphic functions
- **Try**: Search for `Holomorphic` or `AnalyticOn` in mathlib

### 4. BirmanSchwingerPrinciple.lean (2 sorries)
- **Time estimate**: 30 minutes
- **Action**: Operator theory results
- **Try**: `LinearMap.ker_eq_bot` or spectral theory lemmas

## Medium Difficulty

### 5. DiagonalFredholm/WeierstrassProduct.lean (2 sorries)
- **Time estimate**: 1 hour
- **Action**: Infinite product convergence
- **Pattern**: Use `HasProd` API from mathlib

### 6. DiagonalFredholm/DiagOp.lean (3 sorries)
- **Time estimate**: 1 hour
- **Action**: These are axiomatized - might need to prove or accept as axioms
- **Decision needed**: Keep as axioms or prove from first principles?

### 7. SpectralStability.lean (3 sorries)
- **Time estimate**: 1.5 hours
- **Action**: Spectral theory results
- **Try**: `LinearMap.eigenvalue` and related lemmas

### 8. CompleteProof.lean (4 sorries)
- **Time estimate**: 2 hours
- **Action**: Main theorem steps - should reference other results
- **Strategy**: These might disappear once other files are complete

## High Value Targets

### 9. EulerProductConnection.lean (4 sorries)
- **Time estimate**: 2 hours
- **Key insight**: Connects Euler product to determinant
- **Focus**: Product formula lemmas

### 10. OperatorPositivity.lean (5 sorries)
- **Time estimate**: 2.5 hours
- **Pattern**: Positivity and monotonicity results
- **Try**: `mul_self_nonneg`, `sq_nonneg`, positivity tactics

### 11. DiagonalOperatorAnalysis.lean (8 sorries)
- **Time estimate**: 4 hours
- **Categories**:
  - Norm estimates (use `ContinuousLinearMap.op_norm_le_bound`)
  - Spectrum analysis (use eigenvalue API)
  - Convergence (use `tendsto` lemmas)

## Major Work

### 12. EulerProduct/OperatorView.lean (15 sorries)
- **Time estimate**: 6-8 hours
- **Strategy**: Group by type
  - Summability (6 sorries) → `Summable` API
  - Convergence (5 sorries) → `tendsto` lemmas  
  - Product formulas (4 sorries) → `Finset.prod` lemmas

### 13. FredholmInfrastructure.lean (22 sorries)
- **Time estimate**: 8-10 hours
- **Key patterns**:
  - Determinant properties (10+ sorries)
  - Trace class results (5+ sorries)
  - Fredholm theory (5+ sorries)
- **Strategy**: Many are standard operator theory results

## Execution Strategy

### Week 1 (10-15 hours)
1. **Day 1**: Complete all "Quick Wins" (1-4) - 4 files, 6 sorries
2. **Day 2**: Complete DiagonalFredholm files (5-6) - 2 files, 5 sorries  
3. **Day 3**: Complete SpectralStability & CompleteProof (7-8) - 2 files, 7 sorries
4. **Day 4**: Complete EulerProductConnection & OperatorPositivity (9-10) - 2 files, 9 sorries
5. **Day 5**: Start DiagonalOperatorAnalysis (11) - 1 file, 8 sorries

**Week 1 Goal**: 35 sorries eliminated

### Week 2 (15-20 hours)
1. **Days 6-7**: Complete EulerProduct/OperatorView.lean - 15 sorries
2. **Days 8-10**: Complete FredholmInfrastructure.lean - 22 sorries

**Total**: 72 sorries eliminated ✅

## Common Patterns & Solutions

### Pattern: "Summable (fun p => ...)"
```lean
apply Summable.of_norm_bounded (fun p => C * p.val^(-α))
· exact Summable.mul_left _ (Real.summable_nat_rpow.mpr (by linarith : 1 < α))
· intro p; exact [your bound]
```

### Pattern: "det (I - A) = ..."
```lean
rw [Matrix.det_one_sub_mul_comm]
simp [Matrix.det_diagonal]
```

### Pattern: "‖A‖ ≤ C"
```lean
apply ContinuousLinearMap.op_norm_le_bound
· exact C_nonneg
· intro x; calc ‖A x‖ ≤ ...
```

### Pattern: "Continuous f"
```lean
-- If f is linear:
exact ContinuousLinearMap.continuous _
-- If f is a composition:
exact Continuous.comp continuous_f continuous_g
```

## Success Metrics
- [ ] Week 1: 35/72 sorries eliminated
- [ ] Week 2: 72/72 sorries eliminated
- [ ] No new axioms introduced
- [ ] All files still building

## Remember
1. Most sorries are **standard results** that exist in mathlib
2. Use `library_search` and `exact?` liberally
3. Read similar proofs in mathlib for patterns
4. Ask on Lean Zulip if stuck for > 30 minutes
5. Keep proofs short - break into lemmas if needed

Good luck! Start with the 1-sorry files for quick momentum. 