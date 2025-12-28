import RiemannRecognitionGeometry.ExplicitFormula.Route3HypBundle
import RiemannRecognitionGeometry.ExplicitFormula.MathlibBridge
import RiemannRecognitionGeometry.ExplicitFormula.MulConvolution

/-!
# Spectral Identity Algebra

This file proves the algebraic part of the spectral identity:
matching the Mellin transform of the "pair" function to the product of transforms on the critical line.
-/

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula
namespace Route3

open Complex TestSpace

variable {F : Type} [TestSpace F]

/--
The "pair" operation `pair f g = g ⋆ₘ ˜ₘ(⋆ₜ f)` corresponds to `conj(M[f]) * M[g]` on the critical line.
This matches the Hilbert space inner product `⟪Tf, Tg⟫ = conj(Tf) * Tg`.
-/
lemma mellin_pair_eq_mul_conj_mellin {f g : F} {s : ℂ} (hs : s.re = 1/2) :
    Mellin (pair (F := F) f g) s = starRingEnd ℂ (Mellin f s) * Mellin g s := by
  unfold pair
  -- M[g * ~(*f)] = M[g] * M[~(*f)]
  rw [mellin_conv]
  -- M[~h] s = M[h] (1-s)
  rw [mellin_tilde]
  -- M[*f] (1-s) = star (M[f] (star (1-s)))
  rw [mellin_star]
  -- Simplify `star (1-s)` on critical line.
  have h_arg : starRingEnd ℂ (1 - s) = s := by
    apply Complex.ext
    · simp only [starRingEnd_apply, conj_re, map_sub, map_one, sub_re, one_re, hs]
      norm_num
    · simp only [starRingEnd_apply, conj_im, map_sub, map_one, sub_im, one_im, neg_sub, sub_zero]
  rw [h_arg]
  -- Result: M[g] s * star (M[f] s)
  -- Commutative multiplication in ℂ
  ring

end Route3
end ExplicitFormula
end RiemannRecognitionGeometry
