# Riemann-Recognition Science Integration — Final Punch-List

This file tracks every outstanding item needed to drive the `riemann` workspace to
*zero* `sorry` lines and full compilation.

Last updated: 2025-06-25 (Post-cleanup analysis).

## Repository Structure After Cleanup

The canonical active codebase is now in `riemann 2/rh/`. All other directories have been cleaned up:
- Removed duplicate `rh/` directory (was outdated fork)
- Added `.gitignore` for build artifacts (`.lake/`, `*.olean`, etc.)
- Removed tracked build artifacts from `archive/RiemannProof/.lake/build/`
- Archive directory contains historical snapshots but is excluded from builds

## Current State of Affairs (2025-06-25)

The active proof lives in `riemann 2/rh/` following the "Option B" operator-theoretic route to RH.
A forensic scan reveals **39 explicit sorries** across the codebase, concentrated in infrastructure files.

### Sorry Distribution by File

| File | Sorries | Type |
|------|---------|------|
| `academic_framework/OperatorPositivity.lean` | 11 | Trace class & positivity lemmas |
| `academic_framework/FredholmInfrastructure.lean` | 14 | Determinant theory infrastructure |
| `academic_framework/AnalyticContinuation.lean` | 2 | Complex analysis |
| `academic_framework/CompleteProof.lean` | 2 | Top-level glue |
| `academic_framework/DiagonalOperatorAnalysis.lean` | 2 | Technical analysis lemmas |
| `academic_framework/DiagonalFredholm/Operator.lean` | 1 | Diagonal operator property |
| `academic_framework/DiagonalFredholm/WeierstrassProduct.lean` | 2 | Infinite products |
| `academic_framework/EulerProduct/PrimeSeries.lean` | 1 | Prime series convergence |
| `academic_framework/EulerProduct/OperatorView.lean` | 1 | Operator product |
| `academic_framework/EulerProductMathlib.lean` | 1 | Euler product identity |
| `academic_framework/DiagonalFredholm/DiagonalTools.lean` | 2 | lp space machinery |

Plus two stub files (`PrimeRatioNotUnityProofs.lean`, `FredholmDeterminantProofs.lean`) that are prose placeholders.

## Immediate Work Queue (High-Leverage First)

### 1. Foundation Layer (~25 sorries)
**Files:** `OperatorPositivity.lean`, `FredholmInfrastructure.lean`
- These establish trace class operators, spectral radius bounds, determinant existence
- Most can be filled by adapting mathlib's `analysis.normed_space.operator_norm` and trace class theory
- Unblocks all higher-level proofs

### 2. Specialized Operator Lemmas (~7 sorries)
**Files:** `DiagonalFredholm/*.lean`, `EulerProduct/*.lean`, `DiagonalTools.lean`
- Weierstrass products, prime series convergence, diagonal operator properties
- Standard results available in mathlib's complex analysis

### 3. Analysis & Glue Layer (~7 sorries)
**Files:** `AnalyticContinuation.lean`, `DiagonalOperatorAnalysis.lean`, `CompleteProof.lean`
- Final assembly connecting operator theory to RH
- Two technical lemmas in `DiagonalOperatorAnalysis.lean` need careful handling

## Build Commands

From workspace root:
```bash
cd "riemann 2"
lake build
```

The build currently succeeds with warnings about the 39 sorries.

## Next Concrete Steps

1. ✓ Repository cleaned (duplicate directories removed, .gitignore added)
2. ✓ Forensic analysis complete (39 sorries identified and categorized)
3. Start with `OperatorPositivity.lean` - implement trace class lemmas using mathlib
4. Then `FredholmInfrastructure.lean` - determinant theory
5. Work through specialized lemmas in dependency order
6. Complete top-level assembly in `CompleteProof.lean`

## Summary

From the initial confusion with multiple proof attempts and directories, we now have:
- One canonical proof tree: `riemann 2/rh/`
- Clear sorry count: 39 (mostly infrastructure)
- Clean repository structure with proper .gitignore
- Clear path forward: implement trace class theory first, then specialized lemmas