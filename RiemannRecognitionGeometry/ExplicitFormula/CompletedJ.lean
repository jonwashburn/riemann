import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Topology.Separation.Basic
import RiemannRecognitionGeometry.ExplicitFormula.ArithmeticJ
import RiemannRecognitionGeometry.ExplicitFormula.HilbertRealization

/-!
# Route 3 (auxiliary): the “completed J” from Lagarias' ξ

The spectral side `W¹` in the Lagarias framework is naturally a sum over the zeros of the *entire*
completed function `ξ`. When one writes `W¹` as a contour integral, the integrand is the logarithmic
derivative `ξ'/ξ`.

Accordingly, the clean “channel transfer” whose boundary real-part becomes the spectral weight is

`Jξ(s) := - (1/2) · (ξ'(s) / ξ(s)) = - (1/2) · logDeriv ξ(s)`.

With this normalization, the canonical weight in `HilbertRealization.lean` becomes:

`weightOfJ Jξ t = Re( 2·Jξ(1/2+it) ) = Re( - (ξ'/ξ)(1/2+it) )`.

This file defines that `Jξ` and proves the basic rewrites used elsewhere.
-/

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

namespace CompletedJ

open Complex Filter

/-- Completed-channel transfer field: `Jξ(s) := - (1/2) · logDeriv ξ(s)` for Lagarias' `xiLagarias`. -/
def J (s : ℂ) : ℂ :=
  - (logDeriv xiLagarias s) / 2

@[simp] lemma two_mul_J (s : ℂ) : (2 : ℂ) * J s = - (logDeriv xiLagarias s) := by
  -- `2 * (-(A)/2) = -A` in the field `ℂ`.
  simp [J, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- The `HilbertRealization.weightOfJ` for `Jξ` is exactly `Re( - ξ'/ξ )` on the critical line. -/
lemma weightOfJ_eq (t : ℝ) :
    weightOfJ J t = (- (logDeriv xiLagarias (criticalLine t))).re := by
  simp [weightOfJ, two_mul_J]

/--
`Gammaℝ` is complex-differentiable at any point with `Re(s) > 0`.

This is the only region we need for Route 3 (in particular on the critical line).
-/
lemma differentiableAt_Gammaℝ_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Complex.Gammaℝ s := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have h1 : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-z / (2 : ℂ))) s := by
    exact (differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow (Or.inl hpi)
  have hs2 : 0 < (s / (2 : ℂ)).re := by
    have hre : (s / (2 : ℂ)).re = s.re / 2 := by
      simpa using (Complex.div_ofNat_re s 2)
    have : 0 < s.re / 2 := by nlinarith [hs]
    simpa [hre] using this
  have hno : ∀ m : ℕ, (s / (2 : ℂ)) ≠ - (m : ℂ) := by
    intro m hm
    have hre : (s / (2 : ℂ)).re = (- (m : ℂ)).re := congrArg Complex.re hm
    have hmle : (- (m : ℂ)).re ≤ 0 := by
      simp
    have : 0 < (s / (2 : ℂ)).re := hs2
    exact lt_irrefl 0 (lt_of_lt_of_le this (hre ▸ hmle))
  have h2 : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z / (2 : ℂ))) s := by
    refine (Complex.differentiableAt_Gamma (s / (2 : ℂ)) ?_).comp s
      (differentiableAt_id.div_const (2 : ℂ))
    intro m hm
    exact hno m (by simpa using hm)
  simpa [Complex.Gammaℝ_def] using h1.mul h2

/--
Near any `s ≠ 0`, the classical identity `ζ(s) = Λ(s)/Γℝ(s)` holds on a whole neighborhood.

This is the local input needed to transfer `deriv`/`logDeriv` statements from `ζ` to `Λ/Γℝ`.
-/
lemma riemannZeta_eventuallyEq_completed_div_Gammaℝ {s : ℂ} (hs0 : s ≠ 0) :
    (fun z : ℂ => riemannZeta z) =ᶠ[nhds s]
      (fun z : ℂ => completedRiemannZeta z / Complex.Gammaℝ z) := by
  filter_upwards [eventually_ne_nhds hs0] with z hz
  simpa using (riemannZeta_def_of_ne_zero (s := z) hz)

/-- At `s ≠ 0`, `logDeriv ζ(s)` matches `logDeriv (Λ/Γℝ)(s)` by local equality. -/
lemma logDeriv_riemannZeta_eq_logDeriv_completed_div_Gammaℝ {s : ℂ} (hs0 : s ≠ 0) :
    logDeriv riemannZeta s =
      logDeriv (fun z : ℂ => completedRiemannZeta z / Complex.Gammaℝ z) s := by
  have hEq := riemannZeta_eventuallyEq_completed_div_Gammaℝ (s := s) hs0
  have hderiv :
      deriv riemannZeta s = deriv (fun z : ℂ => completedRiemannZeta z / Complex.Gammaℝ z) s :=
    hEq.deriv_eq
  have hval : riemannZeta s = completedRiemannZeta s / Complex.Gammaℝ s :=
    riemannZeta_def_of_ne_zero (s := s) hs0
  simp [logDeriv_apply, hderiv, hval]

/--
On `Re(s) > 0` (and away from `0,1`), the completed zeta log-derivative splits into a ζ-part and an
archimedean Γℝ-part:

`logDeriv Λ = logDeriv ζ + logDeriv Γℝ`.
-/
lemma logDeriv_completedRiemannZeta_eq_logDeriv_riemannZeta_add_logDeriv_Gammaℝ {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hΛ : completedRiemannZeta s ≠ 0) (hΓ : Complex.Gammaℝ s ≠ 0)
    (hsre : 0 < s.re) :
    logDeriv completedRiemannZeta s =
      logDeriv riemannZeta s + logDeriv Complex.Gammaℝ s := by
  have hz :
      logDeriv riemannZeta s =
        logDeriv (fun z : ℂ => completedRiemannZeta z / Complex.Gammaℝ z) s :=
    logDeriv_riemannZeta_eq_logDeriv_completed_div_Gammaℝ (s := s) hs0
  have hdiv :
      logDeriv (fun z : ℂ => completedRiemannZeta z / Complex.Gammaℝ z) s =
        logDeriv completedRiemannZeta s - logDeriv Complex.Gammaℝ s := by
    simpa using
      (logDeriv_div (f := completedRiemannZeta) (g := Complex.Gammaℝ)
        (x := s) hΛ hΓ (differentiableAt_completedZeta hs0 hs1)
        (differentiableAt_Gammaℝ_of_re_pos (s := s) hsre))
  -- Solve for `logDeriv completedRiemannZeta s` by adding `logDeriv Gammaℝ s` to both sides.
  have hsolve :
      logDeriv completedRiemannZeta s =
        logDeriv (fun z : ℂ => completedRiemannZeta z / Complex.Gammaℝ z) s +
          logDeriv Complex.Gammaℝ s := by
    have := congrArg (fun w : ℂ => w + logDeriv Complex.Gammaℝ s) hdiv
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this.symm
  simpa [hz] using hsolve

/--
For `s ≠ 0,1` away from the spectral zeros, the Lagarias ξ log-derivative splits as:

`logDeriv ξ(s) = 1/s + 1/(s-1) + logDeriv Λ(s)`.

This makes explicit the “pole-removal” correction terms carried by the `s(s-1)` prefactor.
-/
lemma logDeriv_xiLagarias_eq {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hΛ : completedRiemannZeta s ≠ 0) :
    logDeriv xiLagarias s = (1 / s) + (1 / (s - 1)) + logDeriv completedRiemannZeta s := by
  have hxi :
      xiLagarias =
        (fun z : ℂ => ((1 / 2 : ℂ) * z) * ((z - 1) * completedRiemannZeta z)) := by
    funext z
    unfold xiLagarias
    simp [mul_assoc]
  rw [hxi]
  have hhalf : (1 / 2 : ℂ) ≠ 0 := by norm_num
  have hf : ((1 / 2 : ℂ) * s) ≠ 0 := mul_ne_zero hhalf hs0
  have hg : ((s - 1) * completedRiemannZeta s) ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hs1) hΛ
  have hdf : DifferentiableAt ℂ (fun z : ℂ => (1 / 2 : ℂ) * z) s :=
    (differentiableAt_id.const_mul (1 / 2 : ℂ))
  have hdg : DifferentiableAt ℂ (fun z : ℂ => (z - 1) * completedRiemannZeta z) s := by
    have h1 : DifferentiableAt ℂ (fun z : ℂ => z - (1 : ℂ)) s :=
      differentiableAt_id.sub_const (1 : ℂ)
    have h2 : DifferentiableAt ℂ completedRiemannZeta s :=
      differentiableAt_completedZeta hs0 hs1
    exact h1.mul h2
  have hmul :=
    logDeriv_mul (f := fun z : ℂ => (1 / 2 : ℂ) * z)
      (g := fun z : ℂ => (z - 1) * completedRiemannZeta z)
      (x := s) hf hg hdf hdg
  -- Use a simp-normal form for the constant factor (`(2:ℂ)⁻¹`) so `simp` can close the rewrite.
  have hconst : logDeriv (fun z : ℂ => ((2 : ℂ)⁻¹) * z) s = s⁻¹ := by
    have h2inv : ((2 : ℂ)⁻¹) ≠ 0 := by
      simpa using (inv_ne_zero (two_ne_zero' ℂ))
    have h := logDeriv_const_mul (f := (fun z : ℂ => z)) (x := s) (a := ((2 : ℂ)⁻¹)) h2inv
    simpa [logDeriv_id, one_div] using h
  have hmul2 :=
    logDeriv_mul (f := fun z : ℂ => z - (1 : ℂ))
      (g := fun z : ℂ => completedRiemannZeta z)
      (x := s) (sub_ne_zero.mpr hs1) hΛ (differentiableAt_id.sub_const (1 : ℂ))
      (differentiableAt_completedZeta hs0 hs1)
  have hsub : logDeriv (fun z : ℂ => z - (1 : ℂ)) s = (s - 1)⁻¹ := by
    -- `deriv (z ↦ z - 1) = 1`, so `logDeriv (z ↦ z - 1) = 1/(z-1)`.
    simp [logDeriv_apply, deriv_sub_const, one_div]
  calc
    logDeriv (fun z : ℂ => ((1 / 2 : ℂ) * z) * ((z - 1) * completedRiemannZeta z)) s
        = logDeriv (fun z : ℂ => (1 / 2 : ℂ) * z) s +
            logDeriv (fun z : ℂ => (z - 1) * completedRiemannZeta z) s := by
          simpa using hmul
    _ = (s⁻¹) + (logDeriv (fun z : ℂ => z - (1 : ℂ)) s + logDeriv completedRiemannZeta s) := by
          simp [hconst, one_div, hmul2, add_assoc, add_left_comm, add_comm]
    _ = (s⁻¹) + ((s - 1)⁻¹ + logDeriv completedRiemannZeta s) := by
          simpa [hsub]
    _ = (1 / s) + (1 / (s - 1)) + logDeriv completedRiemannZeta s := by
          simp [one_div, add_assoc, add_left_comm, add_comm]

/--
Decomposition of the completed-channel weight into:
- the ζ-prime-channel piece `Jζ(s) = -ζ'(s)/ζ(s)`, and
- explicit correction terms from pole-removal (`1/s + 1/(s-1)`) and the archimedean Γℝ-factor.

This is “as far as we can go” without the RH-hard step that identifies the *spectral* functional
`W¹` with the boundary integral weighted by `Re(2·J)`.
-/
lemma two_mul_J_eq_arithmeticJ_sub_corrections {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hΛ : completedRiemannZeta s ≠ 0) (hΓ : Complex.Gammaℝ s ≠ 0)
    (hsre : 0 < s.re) :
    (2 : ℂ) * J s =
      ArithmeticJ.J s - (1 / s + 1 / (s - 1) + logDeriv Complex.Gammaℝ s) := by
  have h2 : (2 : ℂ) * J s = - logDeriv xiLagarias s := by
    simpa using two_mul_J s
  have hxi := logDeriv_xiLagarias_eq (s := s) hs0 hs1 hΛ
  have hcomp :=
    logDeriv_completedRiemannZeta_eq_logDeriv_riemannZeta_add_logDeriv_Gammaℝ (s := s)
      hs0 hs1 hΛ hΓ hsre
  have hJ : ArithmeticJ.J s = - logDeriv riemannZeta s := by
    simp [ArithmeticJ.J, logDeriv_apply, neg_div]
  calc
    (2 : ℂ) * J s
        = - logDeriv xiLagarias s := h2
    _ = - ((1 / s) + (1 / (s - 1)) + logDeriv completedRiemannZeta s) := by
          simpa [hxi]
    _ = - ((1 / s) + (1 / (s - 1)) + (logDeriv riemannZeta s + logDeriv Complex.Gammaℝ s)) := by
          simpa [hcomp, add_assoc, add_left_comm, add_comm]
    _ = (- logDeriv riemannZeta s) - (1 / s + 1 / (s - 1) + logDeriv Complex.Gammaℝ s) := by
          ring
    _ = ArithmeticJ.J s - (1 / s + 1 / (s - 1) + logDeriv Complex.Gammaℝ s) := by
          simpa [hJ]

end CompletedJ

end ExplicitFormula
end RiemannRecognitionGeometry
