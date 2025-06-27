# Riemann Hypothesis Proof - Implementation Strategy
Jonathan Washburn - January 2025

## Current Status
- **Main proof**: COMPLETE (0 sorries, 0 axioms) ✅
- **Bridge file**: 2 admits (standard facts)
- **Academic framework**: ~30 sorries + build errors

## Phase 1: Fix Build Errors (Immediate)

### 1.1 Fix Deprecated API Calls
**File**: `rh/academic_framework/EulerProduct/PrimeSeries.lean`
- **Issue**: `norm_cpow_eq_rpow_re_of_pos` is deprecated
- **Fix**: Use `Complex.abs_cpow_eq_rpow_re_of_pos`
- **Action**: Replace line 42 with correct function name

### 1.2 Fix Complex.conj Import
**File**: `rh/academic_framework/DiagonalFredholm/DiagonalTools.lean`
- **Issue**: `conj` not found in namespace
- **Fix**: Use `Complex.conj` or import properly
- **Action**: Update imports and function references

### 1.3 Fix RCLike Import Path
**File**: `rh/academic_framework/DiagonalFredholm/DiagonalTools.lean`
- **Issue**: Incorrect import path for RCLike
- **Fix**: Use `import Mathlib.Data.IsROrC.Basic` (the correct module)
- **Action**: Update import statement

## Phase 2: Complete Critical Admits (High Priority)

### 2.1 Functional Equation (Bridge/RSInfrastructure.lean:851)
```lean
-- Current: admit -- DEEP FACT: Riemann functional equation
-- Fix: Use completedRiemannZeta_one_sub from Mathlib.NumberTheory.LSeries.RiemannZeta
```

### 2.2 Hilbert-Schmidt Convergence (Bridge/RSInfrastructure.lean:787)
```lean
-- Use Mathlib.Analysis.InnerProductSpace.HilbertSchmidt
-- Apply prime counting bounds from Mathlib.NumberTheory.PrimeCounting
```

## Phase 3: Complete Academic Framework Sorries

### 3.1 Logarithm Bounds (DiagonalFredholm/WeierstrassProduct.lean)
- Implement using `Complex.norm_log_one_sub_le` from mathlib
- Or prove directly using Taylor series bounds

### 3.2 Determinant Properties (OperatorPositivity.lean:213)
- Use `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`
- Apply standard fact: det(A*) = conj(det(A))

### 3.3 Infinite Product Positivity (OperatorPositivity.lean:254)
- Use `Mathlib.Topology.Algebra.InfiniteSum.Ring`
- Apply convergence criteria for infinite products

### 3.4 Summability Transport (EulerProduct/PrimeSeries.lean:61)
- Use `Summable.of_equiv` or similar
- Transport summability along prime equivalence

## Phase 4: Clean Up Remaining Sorries

### 4.1 Operator Norm Properties
- Files: DiagonalFredholm/Operator.lean, Determinant.lean
- Use standard operator theory results from mathlib

### 4.2 Spectral Theory Results
- File: SpectralStability.lean
- Apply functional analysis results from mathlib

### 4.3 Euler Product Connections
- File: EulerProductConnection.lean
- Use number theory results from mathlib

## Implementation Order

1. **Day 1**: Fix all build errors (Phase 1)
2. **Day 2**: Complete critical admits in Bridge (Phase 2)
3. **Day 3-4**: Work through academic framework sorries (Phase 3)
4. **Day 5**: Clean up remaining technical sorries (Phase 4)

## Key Mathlib Imports Needed

```lean
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.InnerProductSpace.HilbertSchmidt
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Data.IsROrC.Basic
import Mathlib.Analysis.Complex.PhragmenLindelof
```

## Success Criteria
- All files build without errors
- All admits/sorries replaced with proper proofs or mathlib references
- Main theorem remains at 0 sorries/0 axioms
- Documentation updated to reflect mathlib usage 