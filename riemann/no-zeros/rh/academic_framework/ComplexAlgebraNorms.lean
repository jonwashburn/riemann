import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace RH
namespace AcademicFramework
namespace ComplexAlgebraNorms

open Complex

lemma hsum_to_prod {R} [Semiring R] (a b d : R) :
    a * d + b * (a * d) = (a + b * a) * d := by
  calc
    a * d + b * (a * d)
        = a * d + (b * a) * d := by
            simpa [mul_assoc]
    _ = (a + b * a) * d := by
            simpa using (add_mul a (b * a) d).symm

lemma ratio_scale_cancel (c a b : ℂ) (hc : c ≠ 0) :
    (a / b) = (c * a) / (c * b) := by
  classical
  have hmul_inv : (c * b)⁻¹ = b⁻¹ * c⁻¹ := by
    simpa [mul_comm] using (mul_inv_rev₀ c b)
  have hcancel :
      (c * a) / (c * b) = a / b := by
    calc
      (c * a) / (c * b)
          = (c * a) * (c * b)⁻¹ := by
              simp [div_eq_mul_inv]
      _ = c * a * ((c * b)⁻¹) := by
              simp [mul_comm, mul_left_comm, mul_assoc]
      _ = c * a * (b⁻¹ * c⁻¹) := by
              simp [hmul_inv]
      _ = a * b⁻¹ * (c * c⁻¹) := by
              simp [mul_comm, mul_left_comm, mul_assoc]
      _ = a * b⁻¹ * 1 := by
              simp [hc, mul_comm, mul_left_comm, mul_assoc]
      _ = a * b⁻¹ := by simp
      _ = a / b := by simp [div_eq_mul_inv]
  exact hcancel.symm

lemma hbridge (c y s : ℂ) (hs : s = y * c) :
    (c + Complex.I * (y * c)) * (c - Complex.I * (y * c))⁻¹
      = c * (1 + Complex.I * y) * (c - Complex.I * s)⁻¹ := by
  subst hs
  have hmul : Complex.I * (y * c) = c * (Complex.I * y) := by
    have : Complex.I * (y * c) = (Complex.I * y) * c := by
      simpa [mul_assoc]
    simpa [mul_comm] using this
  have hnum : c + Complex.I * (y * c) = c * (1 + Complex.I * y) := by
    simp [hmul, mul_add, add_comm, add_left_comm, add_assoc]
  have hden : c - Complex.I * (y * c) = c * (1 - Complex.I * y) := by
    calc
      c - Complex.I * (y * c)
          = c - c * (Complex.I * y) := by
              simpa [hmul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      _ = c * 1 - c * (Complex.I * y) := by simp
      _ = c * (1 - Complex.I * y) := by
              simpa [mul_sub]
  have hden_inv :
      (c * (1 - Complex.I * y))⁻¹ = (c - Complex.I * (y * c))⁻¹ := by
    simpa using congrArg Inv.inv hden.symm
  calc
    (c + Complex.I * (y * c)) * (c - Complex.I * (y * c))⁻¹
        = (c * (1 + Complex.I * y)) * (c * (1 - Complex.I * y))⁻¹ := by
            simp [hnum, hden]
    _ = c * (1 + Complex.I * y) * (c * (1 - Complex.I * y))⁻¹ := by
            simp [mul_comm, mul_left_comm, mul_assoc]
    _ = c * (1 + Complex.I * y) * (c - Complex.I * (y * c))⁻¹ := by
            rw [hden_inv]

lemma hbridge' (c y : ℂ) :
    (c + Complex.I * (y * c)) * (c - Complex.I * (y * c))⁻¹
      = (Complex.I * y + 1) * (c * (c - Complex.I * (y * c))⁻¹) := by
  simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
    using hbridge (c := c) (y := y) (s := y * c) rfl

lemma hratio_align (c y : ℂ) (hc : c ≠ 0) :
    ((Complex.I * y + 1) / (1 - Complex.I * y))
      = ((Complex.I * y * c + c) / (-(Complex.I * y * c) + c)) := by
  have hmul : Complex.I * y * c = c * (Complex.I * y) := by
    have : Complex.I * y * c = (Complex.I * y) * c := by
      simp [mul_assoc]
    simpa [mul_comm] using this
  have hnum : Complex.I * y * c + c = c * (Complex.I * y + 1) := by
    simp [hmul, add_comm, add_left_comm, add_assoc, mul_add, mul_comm, mul_left_comm, mul_assoc]
  have hden : -(Complex.I * y * c) + c = c * (1 - Complex.I * y) := by
    calc
      -(Complex.I * y * c) + c
          = -(c * (Complex.I * y)) + c := by
              simpa [hmul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      _ = c - c * (Complex.I * y) := by simp [sub_eq_add_neg, add_comm]
      _ = c * 1 - c * (Complex.I * y) := by simp
      _ = c * (1 - Complex.I * y) := by
              simpa [mul_sub]
  have hcancel :=
    ratio_scale_cancel (c := c) (a := Complex.I * y + 1) (b := 1 - Complex.I * y) hc
  calc
    ((Complex.I * y + 1) / (1 - Complex.I * y))
        = (c * (Complex.I * y + 1)) / (c * (1 - Complex.I * y)) := hcancel
    _ = ((Complex.I * y * c + c) / (-(Complex.I * y * c) + c)) := by
            simp [hnum, hden, sub_eq_add_neg]

lemma hratio_mul (c y : ℂ) (hc : c ≠ 0) :
    (Complex.I * y + 1) * (1 - Complex.I * y)⁻¹
      = (Complex.I * y * c + c) * (-(Complex.I * y * c) + c)⁻¹ := by
  simpa [div_eq_mul_inv] using hratio_align (c := c) (y := y) hc

@[simp]
lemma neg_one_sub (z : ℂ) : -(1 - z) = z - 1 := by
  simpa [sub_eq_add_neg] using (neg_sub (1 : ℂ) z)

end ComplexAlgebraNorms
end AcademicFramework
end RH
