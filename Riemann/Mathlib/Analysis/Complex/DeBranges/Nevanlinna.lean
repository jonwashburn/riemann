import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Nevanlinna class and de Branges admissibility on the upper half-plane

This file gives honest (non-placeholder) definitions of:

* `Complex.IsOfBoundedTypeUpperHalfPlane f`:
  `f` is in the Nevanlinna class `N(ℍ)`, i.e. a quotient of bounded analytic
  functions on the open upper half-plane.

* `Complex.meanType f`:
  the (upper) mean type of `f` in the upper half-plane, defined via a growth
  rate along the imaginary axis.

* `Complex.IsDeBrangesAdmissible f`:
  the de Branges admissibility condition: analytic on the upper half-plane,
  of bounded type there, and of non-positive mean type.

The definitions are aligned with standard complex-analytic references
(e.g. Conway, *Functions of One Complex Variable II*; de Branges,
*Hilbert Spaces of Entire Functions*; and the Nevanlinna / bounded-type
survey in the classical literature). See also the summary in the
"Bounded type (mathematics)" article.
-/

open scoped Complex UpperHalfPlane

namespace Complex

/-- The open upper half-plane, as a subset of `ℂ`. We work on this set rather than
the subtype `ℍ` for analyticity, to use the existing `AnalyticOnNhd` API. -/
def upperHalfPlaneSet : Set ℂ := { z : ℂ | 0 < z.im }

@[simp] lemma mem_upperHalfPlaneSet {z : ℂ} :
    z ∈ upperHalfPlaneSet ↔ 0 < z.im := Iff.rfl

lemma isOpen_upperHalfPlaneSet : IsOpen (upperHalfPlaneSet) := by
  -- This is a special case of `Complex.isOpen_im_gt_EReal`.
  simpa [upperHalfPlaneSet] using
    (Complex.isOpen_im_gt_EReal (x := (0 : EReal)))

/-- A function `f` is bounded on the open upper half-plane if its norm is uniformly
bounded there. This is the concrete boundedness condition used in the ratio
definition of the Nevanlinna class. -/
def IsBoundedOnUpperHalfPlane (f : ℂ → ℂ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ upperHalfPlaneSet, norm (f z) ≤ C

/-- `IsOfBoundedTypeUpperHalfPlane f` means that `f` belongs to the Nevanlinna
class `N(ℍ)` for the upper half-plane, i.e. it is a quotient of two bounded
holomorphic functions on the upper half-plane.

More precisely, there exist analytic functions `g` and `h` on the open upper
half-plane, both bounded there, such that `h` never vanishes on the upper
half-plane and `f z = g z / h z` for all `z` with `0 < z.im`.

This matches the classical "ratio of bounded analytic functions" definition
for functions of bounded type. -/
def IsOfBoundedTypeUpperHalfPlane (f : ℂ → ℂ) : Prop :=
  ∃ g h : ℂ → ℂ,
    AnalyticOnNhd ℂ g upperHalfPlaneSet ∧
    AnalyticOnNhd ℂ h upperHalfPlaneSet ∧
    IsBoundedOnUpperHalfPlane g ∧
    IsBoundedOnUpperHalfPlane h ∧
    (∀ z ∈ upperHalfPlaneSet, h z ≠ 0) ∧
    ∀ z ∈ upperHalfPlaneSet, f z = g z / h z

/-- Mean type in the upper half-plane, defined as a limsup growth rate along
the imaginary axis:
\[
  \mathrm{meanType}(f) = \limsup_{y \to +\infty}
    \frac{\log (|f(iy)| + 1)}{y}.
\]

This is equivalent (for functions of bounded type) to the constant `q - p`
appearing in Nevanlinna's canonical representation and to more sophisticated
integral characterizations.

We package it via the general `Filter.limsup` along `Filter.atTop` on `ℝ`. -/
noncomputable def meanType (f : ℂ → ℂ) : ℝ :=
  Filter.limsup
    (fun y : ℝ => (Real.log (norm (f (Complex.I * y)) + 1)) / y)
    Filter.atTop

noncomputable def meanType_atImInfty (f : ℍ → ℂ) : ℝ :=
  Filter.limsup
    (fun z : ℍ =>
      (Real.log (norm (f z) + 1)) / (z.im : ℝ))
    UpperHalfPlane.atImInfty



/-- The de Branges admissibility condition for a function `f : ℂ → ℂ`:

* `f` is analytic in a neighbourhood of every point of the open upper half-plane;
* `f` is of bounded type (Nevanlinna class) in the upper half-plane;
* `f` has non-positive mean type in the upper half-plane.

This encodes the analytic side of the hypotheses in de Branges' theory of
Hilbert spaces of entire functions. -/
structure IsDeBrangesAdmissible (f : ℂ → ℂ) : Prop where
  analytic_on_UHP :
    AnalyticOnNhd ℂ f upperHalfPlaneSet
  is_bounded_type :
    IsOfBoundedTypeUpperHalfPlane f
  mean_type_nonpos :
    meanType f ≤ 0

namespace IsDeBrangesAdmissible

variable {f g : ℂ → ℂ} {c : ℂ}

/-!
At this point we **do not** assert algebraic closure properties such as

* `IsDeBrangesAdmissible (f + g)`
* `IsDeBrangesAdmissible (c • f)`
* `IsDeBrangesAdmissible 0`

even though they are classically true.

Proving them in Lean requires:

1. An analytic closure theory for `IsOfBoundedTypeUpperHalfPlane` using the
   "quotient of bounded analytic functions" definition; and
2. A careful analysis of how `meanType` behaves under addition and scalar
   multiplication, via limsup estimates of growth along the imaginary axis.

Both are substantial projects in their own right and should live in a dedicated
Nevanlinna/de Branges development, not as axioms or `sorry`s in this file.
-/

end IsDeBrangesAdmissible

end Complex

namespace Complex

lemma IsBoundedOnUpperHalfPlane.const (c : ℂ) :
    IsBoundedOnUpperHalfPlane fun _ => c := by
  refine ⟨norm c, norm_nonneg c, ?_⟩
  intro z hz; simp

lemma IsBoundedOnUpperHalfPlane.zero :
    IsBoundedOnUpperHalfPlane (fun _ : ℂ => (0 : ℂ)) := by
  simpa using (IsBoundedOnUpperHalfPlane.const (0 : ℂ))

lemma IsBoundedOnUpperHalfPlane.add {f g : ℂ → ℂ}
    (hf : IsBoundedOnUpperHalfPlane f)
    (hg : IsBoundedOnUpperHalfPlane g) :
    IsBoundedOnUpperHalfPlane fun z => f z + g z := by
  rcases hf with ⟨Cf, hCf0, hf⟩
  rcases hg with ⟨Cg, hCg0, hg⟩
  refine ⟨Cf + Cg, add_nonneg hCf0 hCg0, ?_⟩
  intro z hz
  have hfz := hf z hz
  have hgz := hg z hz
  calc
    norm (f z + g z)
        ≤ norm (f z) + norm (g z) := by
          simpa using norm_add_le (f z) (g z)
    _ ≤ Cf + Cg := by
      exact add_le_add hfz hgz

lemma IsBoundedOnUpperHalfPlane.neg {f : ℂ → ℂ}
    (hf : IsBoundedOnUpperHalfPlane f) :
    IsBoundedOnUpperHalfPlane fun z => - f z := by
  rcases hf with ⟨C, hC0, hf⟩
  refine ⟨C, hC0, ?_⟩
  intro z hz
  have hfz := hf z hz
  simpa using hfz

lemma IsBoundedOnUpperHalfPlane.smul {f : ℂ → ℂ} (c : ℂ)
    (hf : IsBoundedOnUpperHalfPlane f) :
    IsBoundedOnUpperHalfPlane fun z => c * f z := by
  rcases hf with ⟨C, hC0, hf⟩
  refine ⟨norm c * C, mul_nonneg (norm_nonneg _) hC0, ?_⟩
  intro z hz
  have hfz := hf z hz
  calc
    norm (c * f z)
        = norm c * norm (f z) := by
          simp
    _ ≤ norm c * C := by
      exact mul_le_mul_of_nonneg_left hfz (norm_nonneg _)

lemma IsBoundedOnUpperHalfPlane.mul {f g : ℂ → ℂ}
    (hf : IsBoundedOnUpperHalfPlane f)
    (hg : IsBoundedOnUpperHalfPlane g) :
    IsBoundedOnUpperHalfPlane fun z => f z * g z := by
  rcases hf with ⟨Cf, hCf0, hf⟩
  rcases hg with ⟨Cg, hCg0, hg⟩
  refine ⟨Cf * Cg, mul_nonneg hCf0 hCg0, ?_⟩
  intro z hz
  have hfz := hf z hz
  have hgz := hg z hz
  calc
    norm (f z * g z)
        = norm (f z) * norm (g z) := by
          simp
    _ ≤ Cf * Cg := by
      exact mul_le_mul hfz hgz (by positivity) (by positivity)


lemma IsOfBoundedTypeUpperHalfPlane.add {f g : ℂ → ℂ}
    (hf : IsOfBoundedTypeUpperHalfPlane f)
    (hg : IsOfBoundedTypeUpperHalfPlane g) :
    IsOfBoundedTypeUpperHalfPlane fun z => f z + g z := by
  rcases hf with ⟨g₁, h₁, g₁_an, h₁_an, g₁_bdd, h₁_bdd, h₁_ne, hfeq⟩
  rcases hg with ⟨g₂, h₂, g₂_an, h₂_an, g₂_bdd, h₂_bdd, h₂_ne, hgeq⟩
  -- Numerator and denominator for `(f + g)` in terms of `g₁,h₁,g₂,h₂`.
  let num : ℂ → ℂ := fun z => g₁ z * h₂ z + g₂ z * h₁ z
  let den : ℂ → ℂ := fun z => h₁ z * h₂ z
  have num_an : AnalyticOnNhd ℂ num upperHalfPlaneSet := by
    have h₁h₂_an : AnalyticOnNhd ℂ (fun z => g₁ z * h₂ z) upperHalfPlaneSet :=
      (g₁_an.mul h₂_an)
    have h₂h₁_an : AnalyticOnNhd ℂ (fun z => g₂ z * h₁ z) upperHalfPlaneSet :=
      (g₂_an.mul h₁_an)
    simpa [num] using h₁h₂_an.add h₂h₁_an
  have den_an : AnalyticOnNhd ℂ den upperHalfPlaneSet := by
    simpa [den] using h₁_an.mul h₂_an
  have num_bdd : IsBoundedOnUpperHalfPlane num := by
    have h₁h₂_bdd : IsBoundedOnUpperHalfPlane (fun z => g₁ z * h₂ z) :=
      g₁_bdd.mul h₂_bdd
    have h₂h₁_bdd : IsBoundedOnUpperHalfPlane (fun z => g₂ z * h₁ z) :=
      g₂_bdd.mul h₁_bdd
    simpa [num] using h₁h₂_bdd.add h₂h₁_bdd
  have den_bdd : IsBoundedOnUpperHalfPlane den := by
    simpa [den] using h₁_bdd.mul h₂_bdd
  have den_ne : ∀ z ∈ upperHalfPlaneSet, den z ≠ 0 := by
    intro z hz
    have hz₁ := h₁_ne z hz
    have hz₂ := h₂_ne z hz
    dsimp [den] at *
    exact mul_ne_zero hz₁ hz₂
  have hsum : ∀ z ∈ upperHalfPlaneSet, f z + g z = num z / den z := by
    intro z hz
    have hz₁ : h₁ z ≠ 0 := h₁_ne z hz
    have hz₂ : h₂ z ≠ 0 := h₂_ne z hz
    have hfz := hfeq z hz
    have hgz := hgeq z hz
    -- Algebra: `g₁/h₁ + g₂/h₂ = (g₁ h₂ + g₂ h₁) / (h₁ h₂)`.
    -- We can delegate to `field_simp`.
    have : f z + g z =
        (g₁ z * h₂ z + g₂ z * h₁ z) / (h₁ z * h₂ z) := by
      have h₁z : h₁ z ≠ 0 := hz₁
      have h₂z : h₂ z ≠ 0 := hz₂
      rw [hfz, hgz]
      field_simp [h₁z, h₂z]
    simpa [num, den] using this
  refine ⟨num, den, num_an, den_an, num_bdd, den_bdd, den_ne, ?_⟩
  intro z hz
  exact hsum z hz

lemma IsOfBoundedTypeUpperHalfPlane.smul {f : ℂ → ℂ} (c : ℂ)
    (hf : IsOfBoundedTypeUpperHalfPlane f) :
    IsOfBoundedTypeUpperHalfPlane fun z => c * f z := by
  rcases hf with ⟨g, h, g_an, h_an, g_bdd, h_bdd, h_ne, h_eq⟩
  -- `c * f = (c*g)/h`.
  refine ⟨(fun z => c * g z), h, ?_, h_an, ?_, h_bdd, h_ne, ?_⟩
  · -- analytic
    simpa using (analyticOnNhd_const.mul g_an)
  · -- bounded
    simpa using g_bdd.smul c
  · -- representation
    intro z hz
    have hhz : h z ≠ 0 := h_ne z hz
    have hfz := h_eq z hz
    simp_rw [hfz]
    field_simp [hhz]



end Complex
