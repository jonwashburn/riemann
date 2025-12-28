
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.Bochner.VitaliCaratheodory
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Integration of top-degree differential forms

This file is intentionally minimal.

* The exterior derivative is provided by mathlib as `extDeriv`.
  We deliberately do **not** restate API lemmas for it here.
* We provide a thin definition `DiffForm.integral` for integrating a top-degree
  form on `ℝⁿ` (modeled as `EuclideanSpace ℝ (Fin n)`) against the standard
  volume form, obtained by evaluating the form on the standard basis.

This is meant to be used together with the divergence-theorem wrapper in
`Stokes.lean`.
-/

open MeasureTheory Set Function
open scoped BigOperators Topology

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {n : ℕ}

/-- Type alias for differential `n`-forms on `E` with values in `F`.

This matches the underlying representation used by mathlib's differential-form
infrastructure (see `Mathlib.Analysis.Calculus.DifferentialForm.Basic`). -/
abbrev DiffForm (𝕜 : Type*) [NontriviallyNormedField 𝕜] (n : ℕ) (E F : Type*)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] :=
  E → E [⋀^Fin n]→L[𝕜] F

namespace DiffForm

/-! ## Standard basis on `EuclideanSpace ℝ (Fin n)` -/

/-- The standard basis vector `e_i` in `EuclideanSpace ℝ (Fin n)` (a.k.a. `Fin n → ℝ`). -/
def stdBasisVec (n : ℕ) (i : Fin n) : EuclideanSpace ℝ (Fin n) :=
  EuclideanSpace.single i 1

@[simp] theorem stdBasisVec_apply {n : ℕ} (i j : Fin n) :
    stdBasisVec n i j = (if j = i then (1 : ℝ) else 0) := by
  simp [stdBasisVec, EuclideanSpace.single_apply, eq_comm]

/-- The standard basis `(e_0, …, e_{n-1})` as a map `Fin n → EuclideanSpace ℝ (Fin n)`. -/
def stdBasis (n : ℕ) : Fin n → EuclideanSpace ℝ (Fin n) :=
  stdBasisVec n

@[simp] theorem stdBasis_apply {n : ℕ} (i j : Fin n) :
    stdBasis n i j = (if j = i then (1 : ℝ) else 0) :=
  stdBasisVec_apply (n := n) i j

/-! ## Integration of top-degree forms -/

/-- Integration of an `n`-form over a measurable set `S ⊆ ℝⁿ`, obtained by evaluating the
form on the standard basis.

Downstream Stokes developments should *not* introduce a second exterior derivative;
use `extDeriv` from mathlib. -/
def integral {n : ℕ} [MeasureSpace (EuclideanSpace ℝ (Fin n))]
    (ω : DiffForm ℝ n (EuclideanSpace ℝ (Fin n)) ℝ)
    (S : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  ∫ x in S, ω x (stdBasis n)

notation "∫_[" S "] " ω:max => DiffForm.integral ω S

/-- The coefficient function of a top-degree form with respect to the standard basis. -/
def coeffFunction (ω : DiffForm ℝ n (EuclideanSpace ℝ (Fin n)) ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun x => ω x (stdBasis n)

@[simp] theorem integral_eq_integral_coeffFunction
    {n : ℕ} [MeasureSpace (EuclideanSpace ℝ (Fin n))]
    (ω : DiffForm ℝ n (EuclideanSpace ℝ (Fin n)) ℝ)
    (S : Set (EuclideanSpace ℝ (Fin n))) :
    (∫_[S] ω) = ∫ x in S, coeffFunction (n := n) ω x :=
  rfl

/-! ## Linearity lemmas -/

theorem integral_add
    {n : ℕ} [MeasureSpace (EuclideanSpace ℝ (Fin n))]
    (ω₁ ω₂ : DiffForm ℝ n (EuclideanSpace ℝ (Fin n)) ℝ)
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (hω₁ : IntegrableOn (fun x => ω₁ x (stdBasis n)) S volume)
    (hω₂ : IntegrableOn (fun x => ω₂ x (stdBasis n)) S volume) :
    ∫_[S] (ω₁ + ω₂) = ∫_[S] ω₁ + ∫_[S] ω₂ := by
  -- Just the corresponding lemma for integrals on a restricted measure.
  simpa [integral] using (MeasureTheory.integral_add hω₁ hω₂)


end DiffForm

end
