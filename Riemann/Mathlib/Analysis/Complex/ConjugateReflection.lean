import Mathlib.Analysis.CStarAlgebra.Classes
import PrimeNumberTheoremAnd.ZetaConj

/-!
# Conjugate Reflection

This file defines the conjugate reflection of a function F : ℂ → E, denoted F#(z) = star(F(conj z)),
and establishes its analytical properties.
-/

open Complex Function

-- Generalized to a complex vector space E with a conjugate-linear star operation.
variable {E : Type*} [AddCommGroup E] [Module ℂ E] [StarAddMonoid E] [StarModule ℂ E]

/-- The conjugate reflection of a function F : ℂ → E, denoted F#(z) = star (F(conj z)). -/
def Complex.conjugateReflection (F : ℂ → E) : ℂ → E :=
  star ∘ F ∘ star


namespace Complex.ConjugateReflection

-- Localized notation
scoped notation:max F:max "#" => Complex.conjugateReflection F

omit [Module ℂ E] [StarModule ℂ E] in
@[simp] lemma apply (F : ℂ → E) (z : ℂ) : F# z = star (F (star z)) := rfl

omit [Module ℂ E] [StarModule ℂ E] in
@[simp] lemma involutive (F : ℂ → E) : F## = F := by
  ext z; simp [apply, star_star]

-- Algebraic properties (Zero, Add, Neg omitted for brevity)
@[simp] lemma smul (c : ℂ) (F : ℂ → E) : (c • F)# = (star c) • F# := by
  ext; simp [star_smul]

/-- The conjugate reflection operation is a conjugate-linear equivalence. -/
@[simps]
def equiv : (ℂ → E) ≃ₗ⋆[ℂ] (ℂ → E) where
  toFun := Complex.conjugateReflection
  invFun := Complex.conjugateReflection
  left_inv := involutive
  right_inv := involutive
  map_add' := by intros F G; ext x; simp only [apply, Pi.add_apply]; exact star_add _ _
  map_smul' := by intros c F; exact smul c F

-- Analysis properties
variable [TopologicalSpace E] [ContinuousStar E]

omit [Module ℂ E] [StarModule ℂ E] in
lemma continuous {F : ℂ → E} (hF : Continuous F) : Continuous (F#) :=
  continuous_star.comp <| hF.comp continuous_star

end Complex.ConjugateReflection

namespace Complex

/-- If `F` is differentiable, then `conj ∘ F ∘ conj` is differentiable. -/
lemma differentiable_conj_comp_conj {F : ℂ → ℂ} (hF : Differentiable ℂ F) :
    Differentiable ℂ (star ∘ F ∘ star) := by
  intro z
  have : star ∘ F ∘ star = fun w => star (F (star w)) := rfl
  rw [this]
  have h := hasDerivAt_conj_conj (hF (star z)).hasDerivAt
  have h' :
      HasDerivAt (fun w => star (F (star w))) (star (deriv F (star z))) z := by
    simpa [Function.comp_apply, star_star] using h
  exact h'.differentiableAt

end Complex

namespace Complex.ConjugateReflection

/-- If F : ℂ → ℂ is differentiable (holomorphic), then F# is also differentiable (holomorphic). -/
lemma differentiable_C {F : ℂ → ℂ} (hF : Differentiable ℂ F) : Differentiable ℂ (F#) := by
  have : F# = star ∘ F ∘ star := by
    ext z; simp [apply, comp_apply]
  rw [this]
  exact Complex.differentiable_conj_comp_conj hF

end Complex.ConjugateReflection
