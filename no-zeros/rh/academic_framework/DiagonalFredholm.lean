import rh.academic_framework.DiagonalFredholm.Operator
import rh.academic_framework.DiagonalFredholm.ProductLemmas
import rh.academic_framework.DiagonalFredholm.Determinant
import rh.academic_framework.DiagonalFredholm.Comprehensive

/-!
# Fredholm Determinants for Diagonal Operators

This file imports the modularized components of the diagonal Fredholm theory.
The content has been split into three modules for better compilation performance:

* `Operator` - Diagonal operator definitions and basic properties
* `ProductLemmas` - Helper lemmas about infinite products
* `Determinant` - Fredholm determinant definitions and main theorems
* `Comprehensive` - Complete comprehensive implementation with full proofs

## Usage

For basic usage, import the modular components. For comprehensive theory with
detailed proofs, use the `Comprehensive` module which provides a complete
self-contained implementation.
-/
