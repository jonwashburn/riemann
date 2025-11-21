import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Topology.Algebra.Module.Star

/-!
# Conjugate reflection of a complex-valued function

For a function `F : ℂ → E` into a complex star module `E`, we define its
**conjugate reflection**
\[
  F^\#(z) := star (F (star z)),
\]
and establish its algebraic, topological, and (for `E = ℂ`) analytic properties.

On `ℂ`, `star` is complex conjugation, so this is the usual reflection across
the real axis followed by conjugation in the codomain.
-/

open scoped Complex

namespace Complex

variable {E : Type*}
  [AddCommGroup E] [Module ℂ E] [StarAddMonoid E] [StarModule ℂ E]

/-- Conjugate reflection of a function `F : ℂ → E`, defined by
`(Complex.conjugateReflection F) z = star (F (conj z))`. -/
def conjugateReflection (F : ℂ → E) : ℂ → E :=
  star ∘ F ∘ star

namespace ConjugateReflection

-- Localized notation for conjugate reflection
scoped notation:max F:max " #" => Complex.conjugateReflection F

variable {F G : ℂ → E} {c : ℂ} {z : ℂ}

@[simp] lemma apply (F : ℂ → E) (z : ℂ) : F# z = star (F (star z)) := rfl

@[simp] lemma apply_conj (F : ℂ → E) (z : ℂ) :
    F# (star z) = star (F z) := by
  -- `star_star` simplifies `star (star z)` back to `z`.
  simp [apply, star_star, Function.comp]

@[simp] lemma apply_real (F : ℂ → E) (x : ℝ) :
    F# x = star (F x) := by
  -- For real `x`, `star x = x`.
  simpa [Complex.ofReal_im, apply, Complex.real_smul, Complex.ofReal_im,
    Complex.ofReal_re] using
    (apply F (x : ℂ))

/-- Conjugate reflection is an involution on the space of functions. -/
@[simp] lemma involutive (F : ℂ → E) : F## = F := by
  ext z
  simp [apply, Function.comp, star_star]

lemma involutive' : Function.Involutive (Complex.conjugateReflection (E := E)) :=
  fun F => involutive (E := E) F

@[simp] lemma congr_arg (h : F = G) : F# = G# := by simpa [h]

/-! ### Algebraic properties -/

@[simp] lemma zero : ((0 : ℂ → E) #) = 0 := by
  ext z; simp [apply]

@[simp] lemma add (F G : ℂ → E) :
    (F + G)# = F# + G# := by
  ext z; simp [apply, map_add]

@[simp] lemma neg (F : ℂ → E) :
    (-F)# = - F# := by
  ext z; simp [apply, map_neg]

@[simp] lemma sub (F G : ℂ → E) :
    (F - G)# = F# - G# := by
  ext z; simp [apply, map_sub]

@[simp] lemma smul (c : ℂ) (F : ℂ → E) :
    (c • F)# = (star c) • F# := by
  ext z; simp [apply, map_smul]

/-- The conjugate reflection operation on functions is a star-linear equivalence. -/
@[simps!]
def equiv : (ℂ → E) ≃ₗ⋆[ℂ] (ℂ → E) where
  toLinearEquiv :=
  { toLinearMap :=
      { toLinearMap := fun F => F#
        map_add' := by
          intro F G; ext z; simp [apply, map_add]
        map_smul' := by
          intro c F; ext z; simp [apply, map_smul] }
    invFun := fun F => F#
    left_inv := fun F => by simpa using involutive (E := E) F
    right_inv := fun F => by simpa using involutive (E := E) F }
  map_star' := by
    intro F; ext z; simp [apply]

@[simp] lemma equiv_apply (F : ℂ → E) (z : ℂ) :
    equiv (E := E) F z = F# z := rfl

@[simp] lemma equiv_symm :
    (equiv (E := E)).symm = equiv := by
  -- Since `equiv` is involutive, it equals its own inverse.
  ext F z; rfl

/-! ### Topological properties -/

variable [TopologicalSpace E] [ContinuousStar E]

lemma continuous (hF : Continuous F) : Continuous F# :=
  continuous_star.comp <| hF.comp continuous_star

/-- Conjugate reflection is a homeomorphism of `ℂ → E` onto itself. -/
def homeomorph : (ℂ → E) ≃ₜ (ℂ → E) where
  toEquiv := equiv (E := E)
  continuous_toFun := by
    -- continuity of `F ↦ F#` in the topology of pointwise convergence
    refine continuous_pi ?_
    intro z; -- evaluation at a fixed `z`
    refine (continuous_apply z).star.comp ?_
    -- `F ↦ F (star z)` is continuous
    simpa [Function.comp] using (continuous_eval_const (x := star z))
  continuous_invFun := by simpa [homeomorph, equiv_symm] using
    (homeomorph (E := E)).continuous_toFun

end ConjugateReflection

end Complex

/-! ### Analytic properties in the scalar case `E = ℂ` -/

namespace Complex.ConjugateReflection

open Complex

/-- If `F : ℂ → ℂ` is holomorphic, then `conj ∘ F ∘ conj` is holomorphic. -/
lemma differentiable_conj_comp_conj {F : ℂ → ℂ}
    (hF : Differentiable ℂ F) :
    Differentiable ℂ (star ∘ F ∘ star) := by
  intro z
  -- Apply Mathlib's `DifferentiableAt.conj_conj` at `star z`.
  have hz : DifferentiableAt ℂ F (star z) := hF (star z)
  -- Rewrite to the concrete `star ∘ F ∘ star` form.
  simpa [Function.comp, Complex.conjugateReflection, Complex.ConjugateReflection.apply] using
    (DifferentiableAt.conj_conj (x := star z) hz)

/-- If `F : ℂ → ℂ` is differentiable, then its conjugate reflection is also differentiable. -/
lemma differentiable_C {F : ℂ → ℂ} (hF : Differentiable ℂ F) :
    Differentiable ℂ F# := by
  -- This is just `differentiable_conj_comp_conj` plus the definitional equality.
  have : (F#) = star ∘ F ∘ star := by
    rfl
  simpa [this] using differentiable_conj_comp_conj (F := F) hF

end Complex.ConjugateReflection
