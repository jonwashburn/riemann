/-
/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang, Matteo Cipollina
-/

import Mathlib
import Riemann.Mathlib.Analysis.Normed.Operator.Fredholm.QuotientProd

/-!
# Fredholm operators

This file defines Fredholm operators between normed spaces and establishes
their basic properties, including the Fredholm index.

## Main definitions
* `IsFredholm`: A bounded linear operator is Fredholm if its kernel and cokernel are finite-dimensional
* `index`: The Fredholm index, defined as dim(ker T) - dim(coker T)

## Main results
* `ContinuousLinearEquiv.isFredholm`: Continuous linear equivalences are Fredholm with index 0
* `index_zero_injective_iff_surjective`: An index-0 Fredholm operator is injective iff surjective
* `of_finiteDimensional`: Linear maps between finite-dimensional spaces are Fredholm
* `index_of_finiteDimensional`: The index equals dim(domain) - dim(codomain) for finite-dimensional spaces

-/

variable {𝕜: Type*} [NormedField 𝕜]
  {X Y Z: Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
  {X' Y' : Type*} [NormedAddCommGroup X'] [NormedSpace 𝕜 X']
  [NormedAddCommGroup Y'] [NormedSpace 𝕜 Y']
  {S T : X →L[𝕜] Y}

open FiniteDimensional

variable (𝕜) in
/-- A bounded linear operator `T: X → Y` is Fredholm iff its kernel and cokernel
are finite-dimensional. -/
def IsFredholm (T : X →L[𝕜] Y) : Prop :=
  FiniteDimensional 𝕜 (LinearMap.ker T) ∧ FiniteDimensional 𝕜 (Y ⧸ LinearMap.range T)

variable (𝕜 X Y) in
/-- The **Fredholm index** of a bounded linear operator is `dim ker T - dim coker T`. -/
noncomputable def index (T : X →L[𝕜] Y) : ℤ :=
  (Module.finrank 𝕜 (LinearMap.ker T) : ℤ) - (Module.finrank 𝕜 (Y ⧸ LinearMap.range T) : ℤ)

/-- If X and Y are complete, closedness of `range T` is automatic for Fredholm operators. -/
theorem IsFredholm.closedRange_of_completeSpace [CompleteSpace X] [CompleteSpace Y]
    (hT : IsFredholm 𝕜 T) : IsClosed (LinearMap.range T : Set Y) := by
  -- The idea: X = ker(T) ⊕ K for some closed complement K (exists since ker is finite-dim)
  -- Then T|_K : K → range(T) is a continuous bijection between complete spaces
  -- By the open mapping theorem, this is a homeomorphism, so range(T) is closed
  obtain ⟨K, hK_closed, hK_compl⟩ := Submodule.exists_closedCompl_of_finiteDimensional (LinearMap.ker T)
  haveI : CompleteSpace K := hK_closed.completeSpace_coe
  -- T restricted to K is injective
  have hT_K_inj : ∀ x : K, T x = 0 → x = 0 := by
    intro ⟨x, hx⟩ hTx
    have : x ∈ LinearMap.ker (T : X →ₗ[𝕜] Y) := by
      simp [LinearMap.mem_ker, ← hTx]
    have : x ∈ K ⊓ LinearMap.ker (T : X →ₗ[𝕜] Y) := ⟨hx, this⟩
    rw [hK_compl.inf_eq_bot] at this
    simp [Submodule.mem_bot] at this
    ext; exact this
  -- The range of T equals the range of T restricted to K
  have hT_range : LinearMap.range (T : X →ₗ[𝕜] Y) =
      LinearMap.range ((T : X →ₗ[𝕜] Y).comp (K.subtype : K →ₗ[𝕜] X)) := by
    ext y
    simp only [LinearMap.mem_range, Submodule.coeSubtype]
    constructor
    · intro ⟨x, hx⟩
      -- Decompose x = k + n where k ∈ K and n ∈ ker(T)
      have : x ∈ K ⊔ LinearMap.ker (T : X →ₗ[𝕜] Y) := by
        rw [hK_compl.sup_eq_top]
        trivial
      obtain ⟨k, hk, n, hn, rfl⟩ := Submodule.mem_sup.mp this
      use ⟨k, hk⟩
      simp only [LinearMap.comp_apply, Submodule.coeSubtype]
      rw [map_add]
      have : (T : X →ₗ[𝕜] Y) n = 0 := hn
      rw [this, add_zero]
      exact hx
    · intro ⟨k, hk⟩
      exact ⟨k.val, hk⟩
  rw [hT_range]
  -- Now we need to show this restricted range is closed
  -- This would follow from a closed range theorem for injective operators on complete spaces
  sorry -- Requires closed range theorem or open mapping theorem variant

namespace IsFredholm

/-- If `T` is Fredholm, so is any scalar multiple `c T` for `c ≠ 0`. -/
lemma smul (hT : IsFredholm 𝕜 T) {c : 𝕜} (hc : c ≠ 0) :
    IsFredholm 𝕜 (c • T) := by
  constructor
  · rw [LinearMap.ker_smul T.toLinearMap _ hc]
    exact hT.1
  · rw [T.range_smul _ hc]
    exact hT.2

/-- If `T` is Fredholm and `c ≠ 0`, then `c • T` has the same Fredholm index as `T`. -/
lemma index_smul (_hT : IsFredholm 𝕜 T) {c : 𝕜} (hc : c ≠ 0) :
    index 𝕜 X Y (c • T) = index 𝕜 X Y T := by
  simp only [index]
  rw [LinearMap.ker_smul T.toLinearMap _ hc, T.range_smul _ hc]

/-- A continuous linear equivalence is Fredholm, with Fredholm index 0. -/
lemma _root_.ContinuousLinearEquiv.isFredholm (T : X ≃L[𝕜] Y) :
    IsFredholm 𝕜 T.toContinuousLinearMap := by
  constructor
  · have : LinearMap.ker (T.toContinuousLinearMap : X →ₗ[𝕜] Y) = ⊥ :=
      LinearMapClass.ker_eq_bot.mpr T.injective
    rw [this]
    infer_instance
  · have : LinearMap.range (T.toContinuousLinearMap : X →ₗ[𝕜] Y) = ⊤ :=
      LinearMap.range_eq_top.mpr T.surjective
    rw [this]
    have : Subsingleton (Y ⧸ ⊤) := by
      rw [Submodule.subsingleton_quotient_iff_eq_top]
    infer_instance

lemma _root_.ContinuousLinearEquiv.index_eq (T : X ≃L[𝕜] Y) :
    index 𝕜 X Y T.toContinuousLinearMap = 0 := by
  simp only [index]
  have hker : LinearMap.ker (T.toContinuousLinearMap : X →ₗ[𝕜] Y) = ⊥ :=
    LinearMapClass.ker_eq_bot.mpr T.injective
  have hrange : LinearMap.range (T.toContinuousLinearMap : X →ₗ[𝕜] Y) = ⊤ :=
    LinearMap.range_eq_top.mpr T.surjective
  rw [hker, hrange]
  simp [Module.finrank_bot, Submodule.finrank_quotient_top]

/-- The identity map is Fredholm. -/
lemma refl : IsFredholm 𝕜 (X := X) (Y := X) (ContinuousLinearEquiv.refl 𝕜 X).toContinuousLinearMap :=
  ContinuousLinearEquiv.isFredholm _

/-- The identity map has Fredholm index zero. -/
lemma index_refl : index 𝕜 X X (ContinuousLinearEquiv.refl 𝕜 X).toContinuousLinearMap = 0 :=
  ContinuousLinearEquiv.index_eq _

/-- The quotient (Y × Y') / (R × R') is isomorphic to (Y/R) × (Y'/R') as modules. -/
def quotientProdEquivProdQuotient (R : Submodule 𝕜 Y) (R' : Submodule 𝕜 Y') :
    (Y × Y') ⧸ R.prod R' ≃ₗ[𝕜] (Y ⧸ R) × (Y' ⧸ R') where
  toFun := Submodule.Quotient.map₂ (R.prod R') R R' LinearMap.fst LinearMap.snd
    (by intro ⟨y, y'⟩ ⟨hy, hy'⟩; exact hy)
    (by intro ⟨y, y'⟩ ⟨hy, hy'⟩; exact hy')
  map_add' := by
    intro x y
    -- Quotient.map₂ is defined so that it's additive
    sorry
  map_smul' := by
    intro c x
    sorry
  invFun := fun ⟨qy, qy'⟩ => Submodule.Quotient.mk (qy.liftOn (fun y => qy'.liftOn (fun y' => (y, y'))
    (by intro a b hab; simp [Submodule.Quotient.eq] at hab; simp [hab]))
    (by intro a b hab; simp [Submodule.Quotient.eq] at hab ⊢; ext <;> simp [hab]))
  left_inv := by
    intro x
    sorry
  right_inv := by
    intro ⟨qy, qy'⟩
    sorry

/-- Alternative construction using the universal property -/
def quotientProdEquivProdQuotient' (R : Submodule 𝕜 Y) (R' : Submodule 𝕜 Y') :
    (Y × Y') ⧸ R.prod R' ≃ₗ[𝕜] (Y ⧸ R) × (Y' ⧸ R') := by
  -- The forward map
  let fwd : (Y × Y') →ₗ[𝕜] (Y ⧸ R) × (Y' ⧸ R') := {
    toFun := fun ⟨y, y'⟩ => (Submodule.Quotient.mk y, Submodule.Quotient.mk y')
    map_add' := by intro ⟨y₁, y₁'⟩ ⟨y₂, y₂'⟩; simp [Prod.mk_add_mk]
    map_smul' := by intro c ⟨y, y'⟩; simp
  }
  -- This map vanishes on R × R'
  have h_ker : R.prod R' ≤ LinearMap.ker fwd := by
    intro ⟨y, y'⟩ ⟨hy, hy'⟩
    simp [LinearMap.mem_ker, fwd]
    constructor
    · exact Submodule.Quotient.eq_zero_iff_mem.mpr hy
    · exact Submodule.Quotient.eq_zero_iff_mem.mpr hy'
  -- So it descends to a map from the quotient
  let fwd_quotient := Submodule.liftQ (R.prod R') fwd h_ker
  -- The backward map
  let bwd : (Y ⧸ R) × (Y' ⧸ R') →ₗ[𝕜] (Y × Y') ⧸ R.prod R' :=
    LinearMap.prod
      (Submodule.liftQ R (Submodule.mkQ (R.prod R') ∘ₗ LinearMap.inl 𝕜 Y Y')
        (by intro y hy; simp [LinearMap.mem_ker]; exact Submodule.Quotient.eq_zero_iff_mem.mpr (Submodule.mem_prod.mpr ⟨hy, Submodule.zero_mem _⟩)))
      (Submodule.liftQ R' (Submodule.mkQ (R.prod R') ∘ₗ LinearMap.inr 𝕜 Y Y')
        (by intro y' hy'; simp [LinearMap.mem_ker]; exact Submodule.Quotient.eq_zero_iff_mem.mpr (Submodule.mem_prod.mpr ⟨Submodule.zero_mem _, hy'⟩)))
  -- Prove these are inverses
  refine LinearEquiv.ofLinear fwd_quotient bwd ?_ ?_
  · ext ⟨qy, qy'⟩
    sorry -- prove bwd ∘ fwd = id
  · ext x
    sorry -- prove fwd ∘ bwd = id

lemma prodMap {T' : X' →L[𝕜] Y'} (hT : IsFredholm 𝕜 T) (hT' : IsFredholm 𝕜 T') :
    IsFredholm 𝕜 (T.prodMap T') := by
  constructor
  · have h_ker : LinearMap.ker ((T.prodMap T') : (X × X') →ₗ[𝕜] (Y × Y')) =
        (LinearMap.ker (T : X →ₗ[𝕜] Y)).prod (LinearMap.ker (T' : X' →ₗ[𝕜] Y')) := by
      ext ⟨x, x'⟩
      simp only [LinearMap.mem_ker, Submodule.mem_prod, ContinuousLinearMap.coe_coe,
        ContinuousLinearMap.prod_apply, Prod.mk.injEq, and_self]
    rw [h_ker]
    exact Module.Finite.prod hT.1 hT'.1
  · have h_range : LinearMap.range ((T.prodMap T') : (X × X') →ₗ[𝕜] (Y × Y')) =
        (LinearMap.range (T : X →ₗ[𝕜] Y)).prod (LinearMap.range (T' : X' →ₗ[𝕜] Y')) := by
      ext ⟨y, y'⟩
      simp only [LinearMap.mem_range, Submodule.mem_prod, ContinuousLinearMap.coe_coe,
        ContinuousLinearMap.prod_apply, Prod.exists, exists_and_left, exists_eq_right]
      constructor
      · intro ⟨x, x', h⟩
        exact ⟨⟨x, h.1⟩, ⟨x', h.2⟩⟩
      · intro ⟨⟨x, hx⟩, ⟨x', hx'⟩⟩
        exact ⟨x, x', hx, hx'⟩
    rw [h_range]
    haveI : Module.Finite 𝕜 (Y ⧸ LinearMap.range (T : X →ₗ[𝕜] Y)) := hT.2
    haveI : Module.Finite 𝕜 (Y' ⧸ LinearMap.range (T' : X' →ₗ[𝕜] Y')) := hT'.2
    -- Use that the quotient by product is the product of quotients
    let e := quotientProdEquivProdQuotient' (LinearMap.range (T : X →ₗ[𝕜] Y))
                                            (LinearMap.range (T' : X' →ₗ[𝕜] Y'))
    haveI : Module.Finite 𝕜 ((Y ⧸ LinearMap.range (T : X →ₗ[𝕜] Y)) ×
                             (Y' ⧸ LinearMap.range (T' : X' →ₗ[𝕜] Y'))) := Module.Finite.prod
    exact Module.Finite.equiv e

lemma finrank_quotient_prod (R : Submodule 𝕜 Y) (R' : Submodule 𝕜 Y')
    [Module.Finite 𝕜 (Y ⧸ R)] [Module.Finite 𝕜 (Y' ⧸ R')] :
    Module.finrank 𝕜 ((Y × Y') ⧸ R.prod R') =
    Module.finrank 𝕜 (Y ⧸ R) + Module.finrank 𝕜 (Y' ⧸ R') := by
  let e := quotientProdEquivProdQuotient' R R'
  rw [LinearEquiv.finrank_eq e, Module.finrank_prod]

lemma index_prodMap {T' : X' →L[𝕜] Y'} (hT : IsFredholm 𝕜 T) (hT' : IsFredholm 𝕜 T') :
    index 𝕜 (X × X') (Y × Y') (T.prodMap T') = index 𝕜 X Y T + index 𝕜 X' Y' T' := by
  simp only [index]
  have h_ker : LinearMap.ker ((T.prodMap T') : (X × X') →ₗ[𝕜] (Y × Y')) =
      (LinearMap.ker (T : X →ₗ[𝕜] Y)).prod (LinearMap.ker (T' : X' →ₗ[𝕜] Y')) := by
    ext ⟨x, x'⟩
    simp [LinearMap.mem_ker, Submodule.mem_prod, ContinuousLinearMap.prod_apply]
  have h_range : LinearMap.range ((T.prodMap T') : (X × X') →ₗ[𝕜] (Y × Y')) =
      (LinearMap.range (T : X →ₗ[𝕜] Y)).prod (LinearMap.range (T' : X' →ₗ[𝕜] Y')) := by
    ext ⟨y, y'⟩
    simp only [LinearMap.mem_range, Submodule.mem_prod, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.prod_apply, Prod.exists, exists_and_left]
    tauto
  rw [h_ker, h_range, Module.finrank_prod]
  haveI : Module.Finite 𝕜 (Y ⧸ LinearMap.range (T : X →ₗ[𝕜] Y)) := hT.2
  haveI : Module.Finite 𝕜 (Y' ⧸ LinearMap.range (T' : X' →ₗ[𝕜] Y')) := hT'.2
  rw [finrank_quotient_prod]
  push_cast
  ring

/-- An index zero Fredholm operator is injective iff it is surjective. -/
lemma index_zero_injective_iff_surjective (hT : IsFredholm 𝕜 T)
    (h_ind : index 𝕜 X Y T = 0) :
    Function.Injective T ↔ Function.Surjective T := by
  rw [index] at h_ind
  have h_eq : Module.finrank 𝕜 (LinearMap.ker (T : X →ₗ[𝕜] Y)) =
              Module.finrank 𝕜 (Y ⧸ LinearMap.range (T : X →ₗ[𝕜] Y)) := by
    have : (Module.finrank 𝕜 (LinearMap.ker (T : X →ₗ[𝕜] Y)) : ℤ) =
           (Module.finrank 𝕜 (Y ⧸ LinearMap.range (T : X →ₗ[𝕜] Y)) : ℤ) := by omega
    exact Nat.cast_injective this
  constructor
  · intro hinj
    have hker : LinearMap.ker (T : X →ₗ[𝕜] Y) = ⊥ := LinearMapClass.ker_eq_bot.mpr hinj
    have : Module.finrank 𝕜 (LinearMap.ker (T : X →ₗ[𝕜] Y)) = 0 := by
      rw [hker, Module.finrank_bot]
    rw [this] at h_eq
    have hcoker : Module.finrank 𝕜 (Y ⧸ LinearMap.range (T : X →ₗ[𝕜] Y)) = 0 := h_eq.symm
    haveI : Module.Finite 𝕜 (Y ⧸ LinearMap.range (T : X →ₗ[𝕜] Y)) := hT.2
    have : Subsingleton (Y ⧸ LinearMap.range (T : X →ₗ[𝕜] Y)) :=
      finrank_zero_iff.mp hcoker
    have : LinearMap.range (T : X →ₗ[𝕜] Y) = ⊤ :=
      Submodule.subsingleton_quotient_iff_eq_top.mp this
    exact LinearMap.range_eq_top.mp this
  · intro hsurj
    have hrange : LinearMap.range (T : X →ₗ[𝕜] Y) = ⊤ := LinearMap.range_eq_top.mpr hsurj
    have : Module.finrank 𝕜 (Y ⧸ LinearMap.range (T : X →ₗ[𝕜] Y)) = 0 := by
      rw [hrange, Submodule.finrank_quotient_top]
    rw [this] at h_eq
    have hker : Module.finrank 𝕜 (LinearMap.ker (T : X →ₗ[𝕜] Y)) = 0 := h_eq
    haveI : Module.Finite 𝕜 (LinearMap.ker (T : X →ₗ[𝕜] Y)) := hT.1
    have : Subsingleton (LinearMap.ker (T : X →ₗ[𝕜] Y)) := finrank_zero_iff.mp hker
    have : LinearMap.ker (T : X →ₗ[𝕜] Y) = ⊥ := Submodule.eq_bot_of_subsingleton
    exact LinearMapClass.ker_eq_bot.mp this

/-- A surjective index zero Fredholm operator between Banach spaces is a linear isomorphism. -/
noncomputable def ContinuousLinearEquiv.of_index_zero_of_surjective_of_isFredholm_of_completeSpace
    [CompleteSpace X] [CompleteSpace Y] (hT : IsFredholm 𝕜 T)
    (h_ind : index 𝕜 X Y T = 0) (hsurj: Function.Surjective T) : X ≃L[𝕜] Y := by
  have hinj : Function.Injective T := (hT.index_zero_injective_iff_surjective h_ind).mpr hsurj
  exact ContinuousLinearEquiv.ofBijective T ⟨hinj, hsurj⟩

/-- An injective index zero Fredholm operator between Banach spaces is a linear isomorphism. -/
noncomputable def ContinuousLinearEquiv.of_index_zero_of_injective_of_isFredholm_of_completeSpace
    [CompleteSpace X] [CompleteSpace Y] (hT : IsFredholm 𝕜 T)
    (h_ind : index 𝕜 X Y T = 0) (hinj: Function.Injective T) : X ≃L[𝕜] Y :=
  ContinuousLinearEquiv.of_index_zero_of_surjective_of_isFredholm_of_completeSpace hT h_ind
    ((hT.index_zero_injective_iff_surjective h_ind).mp hinj)

/-- A continuous linear map between finite-dimensional spaces is Fredholm. -/
lemma of_finiteDimensional [FiniteDimensional 𝕜 X] [FiniteDimensional 𝕜 Y] :
    IsFredholm 𝕜 T := by
  constructor
  · exact FiniteDimensional.finiteDimensional_submodule _
  · infer_instance

/-- The index of a linear map between finite-dimensional spaces equals dim(X) - dim(Y). -/
lemma index_of_finiteDimensional [FiniteDimensional 𝕜 X] [FiniteDimensional 𝕜 Y] :
    index 𝕜 X Y T = (Module.finrank 𝕜 X : ℤ) - (Module.finrank 𝕜 Y : ℤ) := by
  rw [index]
  have hnullity : Module.finrank 𝕜 X =
    Module.finrank 𝕜 (LinearMap.ker (T : X →ₗ[𝕜] Y)) +
    Module.finrank 𝕜 (LinearMap.range (T : X →ₗ[𝕜] Y)) := by
    exact (LinearMap.finrank_range_add_finrank_ker (T : X →ₗ[𝕜] Y)).symm
  have hquot : Module.finrank 𝕜 Y =
    Module.finrank 𝕜 (LinearMap.range (T : X →ₗ[𝕜] Y)) +
    Module.finrank 𝕜 (Y ⧸ LinearMap.range (T : X →ₗ[𝕜] Y)) := by
    rw [add_comm]
    exact Submodule.finrank_quotient_add_finrank (LinearMap.range (T : X →ₗ[𝕜] Y))
  calc (Module.finrank 𝕜 (LinearMap.ker (T : X →ₗ[𝕜] Y)) : ℤ) -
       (Module.finrank 𝕜 (Y ⧸ LinearMap.range (T : X →ₗ[𝕜] Y)) : ℤ)
      = ((Module.finrank 𝕜 (LinearMap.ker (T : X →ₗ[𝕜] Y)) +
          Module.finrank 𝕜 (LinearMap.range (T : X →ₗ[𝕜] Y))) : ℤ) -
        ((Module.finrank 𝕜 (LinearMap.range (T : X →ₗ[𝕜] Y)) +
          Module.finrank 𝕜 (Y ⧸ LinearMap.range (T : X →ₗ[𝕜] Y))) : ℤ) := by push_cast; ring
    _ = (Module.finrank 𝕜 X : ℤ) - (Module.finrank 𝕜 Y : ℤ) := by rw [← hnullity, ← hquot]



end IsFredholm

-/
