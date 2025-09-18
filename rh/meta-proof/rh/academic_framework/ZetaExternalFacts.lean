import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# External Zeta Function Facts

This file simply re-exports three standard facts about the Riemann zeta
function that already exist in mathlib.  They give us:

* trivial zeros on the negative even integers;
* the simple pole at `s = 1` with residue `1`;
* non-vanishing on the half-plane `Re(s) > 1`.
-/

namespace AcademicRH.ZetaExternalFacts

open Complex Filter

/-- The Riemann zeta function has trivial zeros at the negative even integers
`−2 n` for `n ≥ 1`.  This is proved in mathlib as
`riemannZeta_neg_two_mul_nat_add_one` which is stated for `-2 * (k + 1)`.
We re-package it with the more convenient index `n ≥ 1`. -/
lemma zeta_trivial_zero (n : ℕ) (hn : 0 < n) :
    riemannZeta (-2 * n : ℂ) = 0 := by
  -- Handle the `n = k + 1` case explicitly.
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn) with ⟨k, rfl⟩
  -- Now use the mathlib lemma stated for `k + 1`.
  simpa using riemannZeta_neg_two_mul_nat_add_one k

/-- The function `(s - 1) • ζ(s)` tends to `1` as `s → 1` (with `s ≠ 1`),
so `ζ` has a simple pole of residue `1` at `s = 1`.  This is just
`riemannZeta_residue_one` from mathlib. -/
lemma zeta_residue_one :
    Tendsto (fun s ↦ (s - 1) * riemannZeta s)
      (nhdsWithin 1 {s : ℂ | s ≠ 1}) (nhds 1) :=
  riemannZeta_residue_one

/-- **No zeros for `Re(s) > 1`.**  For any complex `s` with real part
strictly larger than `1`, the Riemann zeta function does not vanish.  This
is `riemannZeta_ne_zero_of_one_lt_re` from mathlib. -/
lemma zeta_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_lt_re hs

end AcademicRH.ZetaExternalFacts
