/-! ### Explicit Cayley ↔ unit-circle parametrization -/

/-! A closed form for `exp (i · 2 arctan y)` using trig closed forms in cartesian coordinates. -/
lemma exp_I_two_arctan_ratio (y : ℝ) :
  Complex.exp (Complex.I * (2 * Real.arctan y))
    = ((1 : ℝ) + Complex.I * y) / ((1 : ℝ) - Complex.I * y) := by
  classical
  set a : ℝ := Real.arctan y with ha
  set r : ℝ := Real.sqrt (1 + y^2) with hr
  have hr_pos : 0 < r := by
    have : 0 < 1 + y^2 := by positivity
    simpa [hr] using Real.sqrt_pos.mpr this
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  have hr_sq : r ^ 2 = 1 + y^2 := by
    have : 0 ≤ 1 + y^2 := by positivity
    calc
      r ^ 2 = (Real.sqrt (1 + y^2)) ^ 2 := by simpa [hr]
      _ = Real.sqrt (1 + y^2) * Real.sqrt (1 + y^2) := by simp [pow_two]
      _ = 1 + y^2 := by simpa [hr] using Real.mul_self_sqrt this
  have hcos : Real.cos a = 1 / r := by
    simpa [ha, hr] using Real.cos_arctan y
  have hsin : Real.sin a = y / r := by
    simpa [ha, hr] using Real.sin_arctan y
  have hcos_sq : Real.cos a ^ 2 = 1 / (1 + y^2) := by
    calc
      Real.cos a ^ 2 = (1 / r) ^ 2 := by simpa [hcos]
      _ = 1 / (r ^ 2) := by
        simp [pow_two, one_div, hr_ne, mul_comm, mul_left_comm, mul_assoc]
      _ = 1 / (1 + y^2) := by simpa [hr_sq]
  have hsin_sq : Real.sin a ^ 2 = y^2 / (1 + y^2) := by
    calc
      Real.sin a ^ 2 = (y / r) ^ 2 := by simpa [hsin]
      _ = y^2 / (r ^ 2) := by
        simp [pow_two, one_div, hr_ne, mul_comm, mul_left_comm, mul_assoc]
      _ = y^2 / (1 + y^2) := by simpa [hr_sq]
  have hden_ne0 : (1 + y^2 : ℝ) ≠ 0 := by
    exact ne_of_gt (by positivity : 0 < 1 + y^2)
  have hcos2 :
      Real.cos (2 * a) = (1 - y^2) / (1 + y^2) := by
    calc
      Real.cos (2 * a)
          = Real.cos a ^ 2 - Real.sin a ^ 2 := Real.cos_two_mul a
      _ = 1 / (1 + y^2) - y^2 / (1 + y^2) := by simpa [hcos_sq, hsin_sq]
      _ = (1 - y^2) / (1 + y^2) := by
        field_simp [hden_ne0]
  have hsin2 :
      Real.sin (2 * a) = (2 * y) / (1 + y^2) := by
    calc
      Real.sin (2 * a)
          = 2 * Real.sin a * Real.cos a := Real.sin_two_mul a
      _ = 2 * (y / r) * (1 / r) := by simpa [hsin, hcos]
      _ = (2 * y) / (1 + y^2) := by
        field_simp [one_div, hr_ne, hr_sq, hden_ne0, mul_comm, mul_left_comm, mul_assoc]
  have h_real :
      Real.cos (2 * a) + y * Real.sin (2 * a) = 1 := by
    have hnum : (1 - y^2) + 2 * y^2 = 1 + y^2 := by ring
    calc
      Real.cos (2 * a) + y * Real.sin (2 * a)
          = (1 - y^2) / (1 + y^2) + (2 * y^2) / (1 + y^2) := by
            simp [hcos2, hsin2, mul_comm, mul_left_comm, mul_assoc, one_div]
      _ = ((1 - y^2) + 2 * y^2) / (1 + y^2) := by
            field_simp [hden_ne0]
      _ = (1 + y^2) / (1 + y^2) := by simpa [hnum]
      _ = 1 := by field_simp [hden_ne0]
  have h_imag :
      Real.sin (2 * a) - y * Real.cos (2 * a) = y := by
    have hnum : (2 * y) - y * (1 - y^2) = y * (1 + y^2) := by ring
    calc
      Real.sin (2 * a) - y * Real.cos (2 * a)
          = (2 * y) / (1 + y^2) - y * ((1 - y^2) / (1 + y^2)) := by
            simp [hsin2, hcos2, mul_comm, mul_left_comm, mul_assoc, one_div]
      _ = ((2 * y) - y * (1 - y^2)) / (1 + y^2) := by
            field_simp [hden_ne0]
      _ = (y * (1 + y^2)) / (1 + y^2) := by simpa [hnum]
      _ = y := by field_simp [hden_ne0]
  have h_exp :
      Complex.exp (Complex.I * (2 * a))
        = Complex.ofReal (Real.cos (2 * a))
            + Complex.I * Complex.ofReal (Real.sin (2 * a)) := by
    simpa [Complex.ofReal_mul, mul_comm, mul_left_comm, mul_assoc]
      using (Complex.exp_mul_I (Complex.ofReal (2 * a)))
  have hden_ne_complex : ((1 : ℂ) - Complex.I * y) ≠ 0 := by
    intro h
    have : (1 : ℝ) = 0 := by
      simpa using congrArg Complex.re h
    exact one_ne_zero this
  have h_mul :
      Complex.exp (Complex.I * (2 * a)) * ((1 : ℂ) - Complex.I * y)
        = (1 : ℂ) + Complex.I * y := by
    calc
      Complex.exp (Complex.I * (2 * a)) * ((1 : ℂ) - Complex.I * y)
          = (Complex.ofReal (Real.cos (2 * a))
              + Complex.I * Complex.ofReal (Real.sin (2 * a)))
              * ((1 : ℂ) - Complex.I * y) := by simpa [h_exp]
      _ = Complex.ofReal (Real.cos (2 * a) + y * Real.sin (2 * a))
            + Complex.I * Complex.ofReal (Real.sin (2 * a) - y * Real.cos (2 * a)) := by
              simp [mul_add, add_mul, Complex.I_mul, Complex.mul_I, sub_eq_add_neg,
                mul_comm, mul_left_comm, mul_assoc]
      _ = (1 : ℂ) + Complex.I * y := by simp [h_real, h_imag]
  have hres :
      Complex.exp (Complex.I * (2 * a))
        = ((1 : ℂ) + Complex.I * y) / ((1 : ℂ) - Complex.I * y) := by
    have := congrArg (fun z : ℂ => z * ((1 : ℂ) - Complex.I * y)⁻¹) h_mul
    simpa [div_eq_mul_inv, hden_ne_complex] using this
  simpa [ha] using hres
