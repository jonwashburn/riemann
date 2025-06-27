import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Data.Real.GoldenRatio
import Mathlib.Topology.Instances.ENNReal
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Common Infrastructure Definitions (academic framework)
-/

namespace RH

open Complex Real BigOperators

/-- The weighted ℓ² space over primes -/
noncomputable abbrev WeightedL2 := lp (fun _ : {p : ℕ // Nat.Prime p} => ℂ) 2

namespace WeightedL2

instance : Fact (1 ≤ 2) := ⟨by norm_num⟩

-- The DecidableEq instance is already provided by the subtype
-- No need to define it explicitly

/-- Basis vectors δ_p for each prime p -/
noncomputable def deltaBasis (p : {p : ℕ // Nat.Prime p}) : WeightedL2 :=
  lp.single 2 p 1

/-- deltaBasis p has value 1 at index p -/
@[simp]
lemma deltaBasis_apply_self (p : {p : ℕ // Nat.Prime p}) :
  deltaBasis p p = 1 := by
  simp [deltaBasis, lp.single_apply, eq_self_iff_true, if_true]

/-- deltaBasis p has value 0 at other indices -/
@[simp]
lemma deltaBasis_apply_ne (p q : {p : ℕ // Nat.Prime p}) (h : p ≠ q) :
  deltaBasis p q = 0 := by
  simp only [deltaBasis, lp.single_apply]
  have : ¬(q = p) := fun h' => h (h'.symm)
  simp [this]

/-- Domain of the arithmetic Hamiltonian -/
def domainH : Set WeightedL2 :=
  {ψ | Summable fun p => ‖ψ p‖^2 * (Real.log p.val)^2}

/-- The inner product on WeightedL2 -/
noncomputable instance : InnerProductSpace ℂ WeightedL2 := by
  infer_instance

-- (Commented out: a standard fact relating the `ℓ²` norm to the sum of squares of components.
-- A ready-made lemma `PiLp.norm_sq_eq_of_L2` from mathlib can be used whenever needed.)

end WeightedL2

noncomputable abbrev WeightedHilbertSpace := WeightedL2

export WeightedL2 (deltaBasis domainH)

/-- The regularized Fredholm determinant -/
noncomputable def fredholm_det2 (s : ℂ) : ℂ :=
  ∏' p : {p : ℕ // Nat.Prime p}, (1 - (p.val : ℂ)^(-s)) * Complex.exp ((p.val : ℂ)^(-s))

/-- The renormalization factor -/
noncomputable def renormE (s : ℂ) : ℂ :=
  Complex.exp (∑' k : ℕ, ∑' p : {p : ℕ // Nat.Prime p}, (p.val : ℂ)^(-(k + 1) * s) / (k + 1 : ℕ))

end RH
