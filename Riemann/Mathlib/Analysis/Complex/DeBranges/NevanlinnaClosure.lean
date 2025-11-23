import Mathlib.Analysis.Analytic.Constructions
import Riemann.Mathlib.Analysis.Complex.DeBranges.Nevanlinna

/-!
# Algebraic Closure Properties of Nevanlinna and de Branges Classes

This file proves that the Nevanlinna class `N(ℍ)` and the set of de Branges
admissible functions are closed under standard algebraic operations (addition,
scalar multiplication, etc.).
-/

open scoped Complex UpperHalfPlane

namespace Complex

/-!
### Boundedness on the Upper Half-Plane
-/

/-- A constant function is bounded on the upper half-plane. -/
lemma IsBoundedOnUpperHalfPlane.const (c : ℂ) :
    IsBoundedOnUpperHalfPlane fun _ => c := by
  refine ⟨‖c‖, norm_nonneg c, ?_⟩
  intro z hz; simp

/-- The zero function is bounded on the upper half-plane. -/
lemma IsBoundedOnUpperHalfPlane.zero :
    IsBoundedOnUpperHalfPlane (fun _ : ℂ => (0 : ℂ)) := by
  simpa using (IsBoundedOnUpperHalfPlane.const (0 : ℂ))

/-- Boundedness is preserved under addition. -/
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
    ‖f z + g z‖
        ≤ ‖f z‖ + ‖g z‖ := by
          simpa using norm_add_le (f z) (g z)
    _ ≤ Cf + Cg := by
      exact add_le_add hfz hgz

/-- Boundedness is preserved under negation. -/
lemma IsBoundedOnUpperHalfPlane.neg {f : ℂ → ℂ}
    (hf : IsBoundedOnUpperHalfPlane f) :
    IsBoundedOnUpperHalfPlane fun z => - f z := by
  rcases hf with ⟨C, hC0, hf⟩
  refine ⟨C, hC0, ?_⟩
  intro z hz
  have hfz := hf z hz
  simpa using hfz

/-- Boundedness is preserved under scalar multiplication. -/
lemma IsBoundedOnUpperHalfPlane.smul {f : ℂ → ℂ} (c : ℂ)
    (hf : IsBoundedOnUpperHalfPlane f) :
    IsBoundedOnUpperHalfPlane fun z => c * f z := by
  rcases hf with ⟨C, hC0, hf⟩
  refine ⟨‖c‖ * C, mul_nonneg (norm_nonneg _) hC0, ?_⟩
  intro z hz
  have hfz := hf z hz
  calc
    ‖c * f z‖
        = ‖c‖ * ‖f z‖ := by
          simp
    _ ≤ ‖c‖ * C := by
      exact mul_le_mul_of_nonneg_left hfz (norm_nonneg _)


/-- Boundedness is preserved under pointwise multiplication. -/
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
    ‖f z * g z‖
        = ‖f z‖ * ‖g z‖ := by
          simp
    _ ≤ Cf * Cg := by
      exact mul_le_mul hfz hgz (by positivity) (by positivity)

/-!
### Algebraic Closure of Nevanlinna Class
-/

/-- The Nevanlinna bounded-type class is closed under addition. -/
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

/-- The Nevanlinna bounded-type class is closed under scalar multiplication. -/
lemma IsOfBoundedTypeUpperHalfPlane.smul {f : ℂ → ℂ} (c : ℂ)
    (hf : IsOfBoundedTypeUpperHalfPlane f) :
    IsOfBoundedTypeUpperHalfPlane fun z => c * f z := by
  rcases hf with ⟨g, h, g_an, h_an, g_bdd, h_bdd, h_ne, h_eq⟩
  -- `c * f = (c*g)/h`.
  refine ⟨(fun z => c * g z), h, ?_, h_an, ?_, h_bdd, h_ne, ?_⟩
  · -- analytic
    simpa using (analyticOnNhd_const (v := c).mul g_an)
  · -- bounded
    simpa using g_bdd.smul c
  · -- representation
    intro z hz
    have hhz : h z ≠ 0 := h_ne z hz
    have hfz := h_eq z hz
    simp_rw [hfz]
    field_simp [hhz]

/-!
### Algebraic Closure of de Branges Admissible Functions
-/

namespace IsDeBrangesAdmissible

variable {f g : ℂ → ℂ} {c : ℂ}

/-- Admissibility of the zero function. -/
lemma zero :
    IsDeBrangesAdmissible (fun _ : ℂ => (0 : ℂ)) := by
  refine
    { analytic_on_UHP := ?h_an
      is_bounded_type := ?h_bt
      mean_type_nonpos := ?h_mean }
  · -- `0` is analytic on the upper half-plane.
    simpa [upperHalfPlaneSet] using
      (analyticOnNhd_const (v := (0 : ℂ)) (s := upperHalfPlaneSet))
  · -- `0` is of bounded type: `0 = 0 / 1` with bounded analytic numerator/denominator.
    refine
      ⟨(fun _ => (0 : ℂ)), (fun _ => (1 : ℂ)),
        ?g_an, ?h_an', ?g_bdd, ?h_bdd, ?h_ne, ?h_rep⟩
    · -- numerator analytic
      simpa [upperHalfPlaneSet] using
        (analyticOnNhd_const (v := (0 : ℂ)) (s := upperHalfPlaneSet))
    · -- denominator analytic
      simpa [upperHalfPlaneSet] using
        (analyticOnNhd_const (v := (1 : ℂ)) (s := upperHalfPlaneSet))
    · -- numerator bounded on the upper half-plane
      simpa using (IsBoundedOnUpperHalfPlane.zero)
    · -- denominator bounded on the upper half-plane
      simpa using (IsBoundedOnUpperHalfPlane.const (c := (1 : ℂ)))
    · -- denominator never vanishes on the upper half-plane
      intro z hz
      simp
    · -- representation: `0 z = 0 / 1` on the upper half-plane
      intro z hz
      simp
  · -- Mean type of the zero function is `0`, hence ≤ 0.
    have : meanType (fun _ : ℂ => (0 : ℂ)) = 0 := by
      -- The integrand in the definition of `meanType` is identically zero.
      simp [meanType]
    simp [this]

/-- Admissibility is closed under addition. -/
lemma add (hf : IsDeBrangesAdmissible f) (hg : IsDeBrangesAdmissible g) :
    IsDeBrangesAdmissible (fun z => f z + g z) := by
  refine
    { analytic_on_UHP := ?_
      is_bounded_type := ?_
      mean_type_nonpos := ?_ }
  · -- analyticity on the upper half-plane
    -- `AnalyticOnNhd` is closed under addition.
    have h := hf.analytic_on_UHP.add hg.analytic_on_UHP
    simpa using h
  · -- bounded-type closure from the Nevanlinna part
    exact
      IsOfBoundedTypeUpperHalfPlane.add
        (f := f) (g := g) hf.is_bounded_type hg.is_bounded_type
  · -- mean type: use `meanType_add_le` and the hypotheses `≤ 0`
    have h_le : meanType (fun z => f z + g z) ≤ meanType f + meanType g :=
      meanType_add_le f g
    have h_sum_nonpos : meanType f + meanType g ≤ 0 := by
      have hf0 := hf.mean_type_nonpos
      have hg0 := hg.mean_type_nonpos
      have := add_le_add hf0 hg0
      simpa using this
    exact h_le.trans h_sum_nonpos

/-- Admissibility is closed under scalar multiplication. -/
lemma smul (hf : IsDeBrangesAdmissible f) (c : ℂ) :
    IsDeBrangesAdmissible (fun z => c * f z) := by
  refine
    { analytic_on_UHP := ?_
      is_bounded_type := ?_
      mean_type_nonpos := ?_ }
  · -- analyticity: constant times analytic function is analytic
    have h_const :
        AnalyticOnNhd ℂ (fun _ : ℂ => c) upperHalfPlaneSet :=
      analyticOnNhd_const (v := c) (s := upperHalfPlaneSet)
    have h := (AnalyticOnNhd.mul (f := fun _ : ℂ => c) (g := f)
      (hf := h_const) (hg := hf.analytic_on_UHP))
    simpa using h
  · -- bounded type: use `IsOfBoundedTypeUpperHalfPlane.smul`
    simpa using
      (IsOfBoundedTypeUpperHalfPlane.smul c hf.is_bounded_type)
  · -- mean type inequality
    have h_le : meanType (fun z => c * f z) ≤ meanType f :=
      meanType_smul_le c f
    exact h_le.trans hf.mean_type_nonpos

/-- Admissibility is closed under subtraction. -/
lemma sub (hf : IsDeBrangesAdmissible f) (hg : IsDeBrangesAdmissible g) :
    IsDeBrangesAdmissible (fun z => f z - g z) := by
  -- `f - g = f + (-1) * g`, so use `add` and `smul`.
  have h_neg_g :
      IsDeBrangesAdmissible (fun z => (-1 : ℂ) * g z) :=
    smul (hf := hg) (-1)
  have h_add :
      IsDeBrangesAdmissible (fun z => f z + (-1 : ℂ) * g z) :=
    add hf h_neg_g
  simpa [sub_eq_add_neg, mul_comm] using h_add

end IsDeBrangesAdmissible
end Complex
