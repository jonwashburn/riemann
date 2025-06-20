theorem l2_norm_squared (ψ : l² ℕ) :
  ‖ψ‖² = ∑' p, ‖ψ p‖² := by
  have h1 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2 : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  have : ‖ψ‖ = (∑' p, ‖ψ p‖ ^ (2 : ℝ≥0∞).toReal) ^ ((2 : ℝ≥0∞).toReal)⁻¹ := by
    rw [lp.norm_eq_tsum_rpow h1 h2]
  rw [this]
  simp only [ENNReal.toReal_ofNat]
  ring_nf
  rw [← Real.rpow_natCast]
  norm_num
  rw [Real.sq_sqrt]
  · congr 1
    ext p
    rw [← Real.rpow_natCast]
    norm_num
  · apply tsum_nonneg
    intro p
    exact sq_nonneg _
