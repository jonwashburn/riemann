import rh.Common
import DeterminantProofsFinalComplete
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Determinant Identity Proofs - Final Assembly

This file contains the final proofs for the determinant identity decomposition.
-/

namespace RH.DeterminantProofsFinal

open Complex Real BigOperators Filter

/-- The Euler product converges for Re(s) > 1 -/
lemma euler_product_converges (s : ℂ) (hs : 1 < s.re) :
    Multipliable fun p : {p : ℕ // Nat.Prime p} => (1 - (p.val : ℂ)^(-s))⁻¹ :=
  DeterminantProofsFinalComplete.euler_product_converges_proof s hs

/-- The regularized product converges for Re(s) > 1/2 -/
lemma regularized_product_converges (s : ℂ) (hs : 1/2 < s.re) :
    Multipliable fun p : {p : ℕ // Nat.Prime p} =>
      (1 - (p.val : ℂ)^(-s)) * Complex.exp ((p.val : ℂ)^(-s)) :=
  DeterminantProofsFinalComplete.regularized_product_converges_proof s hs

/-- Prime sum convergence for σ > 1 -/
lemma prime_sum_converges {σ : ℝ} (hσ : 1 < σ) :
    Summable fun p : {p : ℕ // Nat.Prime p} => (p.val : ℝ)^(-σ) :=
  DeterminantProofsFinalComplete.prime_sum_converges_proof hσ

/-- Bound on complex powers of primes -/
lemma prime_power_bound (p : {p : ℕ // Nat.Prime p}) (s : ℂ) (hs : 0 < s.re) :
    Complex.abs ((p.val : ℂ)^(-s)) = (p.val : ℝ)^(-s.re) :=
  DeterminantProofsFinalComplete.prime_power_bound_proof p s hs

end RH.DeterminantProofsFinal
