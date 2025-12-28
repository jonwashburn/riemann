/--
Intertwining maps between fundamental symmetries.

Kapustin-style constructions routinely transport an operator between different analytic models
(weighted `L²`, Hardy spaces, de Branges spaces, etc.).

At the level of the *indefinite metric*, the correct minimal invariant notion is that a map `U`
intertwines two fundamental symmetries `J` and `J'`:

`J' ∘ U = U ∘ J`.

From this purely algebraic hypothesis we obtain:

* `U` maps the `+1`/`-1` eigenspaces of `J` to those of `J'`.
* If `U` is a (bounded) linear equivalence, it restricts to linear equivalences on the
  `±1` eigenspaces.
* Consequently, the negative index (`Module.rank` of the `-1` eigenspace) is preserved under
  intertwining equivalences, and so is the Pontryagin property.

The rank statement is formulated with `Cardinal.lift` to allow universe-polymorphic use.
-/

import KapustinFormalization.Krein.FundamentalDecomposition

namespace Krein

universe u v

variable {𝕜 : Type*} [IsROrC 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

namespace FundamentalSymmetry

variable (K : FundamentalSymmetry 𝕜 E) (K' : FundamentalSymmetry 𝕜 F)

/-- A continuous linear map `U` *intertwines* the fundamental symmetries `K.J` and `K'.J` if
`K'.J ∘ U = U ∘ K.J`.

This condition is the natural requirement for transporting the `±1` eigenspace decompositions.
-/
def Intertwines (U : E →L[𝕜] F) : Prop :=
  K'.J.comp U = U.comp K.J

lemma intertwines_apply (U : E →L[𝕜] F) (h : Intertwines (K := K) (K' := K') U) (x : E) :
    K'.J (U x) = U (K.J x) := by
  -- Evaluate the equality of operators at `x`.
  have hx := congrArg (fun T : E →L[𝕜] F => T x) h
  simpa [Intertwines, ContinuousLinearMap.comp_apply] using hx

/-- Intertwining maps send the `+1` eigenspace of `K.J` into the `+1` eigenspace of `K'.J`. -/
lemma map_mem_posSubspace (U : E →L[𝕜] F) (h : Intertwines (K := K) (K' := K') U)
    {x : E} (hx : x ∈ posSubspace (K := K)) :
    U x ∈ posSubspace (K := K') := by
  -- Membership in `posSubspace` is exactly the fixed-point equation.
  change K'.J (U x) = U x
  -- Use intertwining and the assumption `K.J x = x`.
  simpa [hx] using (intertwines_apply (K := K) (K' := K') (U := U) h x)

/-- Intertwining maps send the `-1` eigenspace of `K.J` into the `-1` eigenspace of `K'.J`. -/
lemma map_mem_negSubspace (U : E →L[𝕜] F) (h : Intertwines (K := K) (K' := K') U)
    {x : E} (hx : x ∈ negSubspace (K := K)) :
    U x ∈ negSubspace (K := K') := by
  change K'.J (U x) = - U x
  -- Use intertwining and the assumption `K.J x = -x`.
  simpa [hx, map_neg] using (intertwines_apply (K := K) (K' := K') (U := U) h x)

/-!
## Induced equivalences on eigenspaces

If `U` is a bounded linear equivalence intertwining the symmetries, it restricts to linear
equivalences on the `±1` eigenspaces.

We formulate these as `LinearEquiv`s since only linear structure is needed.
-/

/-- A bounded equivalence intertwining `J` and `J'` induces a linear equivalence between the
`+1` eigenspaces. -/
noncomputable def posSubspaceEquiv
    (U : E ≃L[𝕜] F)
    (h : Intertwines (K := K) (K' := K') U.toContinuousLinearMap) :
    (posSubspace (K := K)) ≃ₗ[𝕜] (posSubspace (K := K')) := by
  classical
  refine
    { toFun := fun x =>
        ⟨U x.1,
          map_mem_posSubspace (K := K) (K' := K') (U := U.toContinuousLinearMap) h x.2⟩
      invFun := fun y =>
        ⟨U.symm y.1, ?_⟩
      left_inv := ?_
      right_inv := ?_
      map_add' := ?_
      map_smul' := ?_ }
  · -- `U.symm` maps `posSubspace K'` back into `posSubspace K`.
    have hy' : K'.J y.1 = y.1 := y.2
    have hJU : K'.J (U (U.symm y.1)) = U (K.J (U.symm y.1)) := by
      simpa using
        (intertwines_apply (K := K) (K' := K') (U := U.toContinuousLinearMap) h (U.symm y.1))
    have hEq : y.1 = U (K.J (U.symm y.1)) := by
      -- Rewrite the left-hand side using `U (U.symm y) = y` and the fixed-point hypothesis.
      have : K'.J y.1 = U (K.J (U.symm y.1)) := by
        simpa using hJU
      simpa [hy'] using this
    -- Apply `U.symm` to conclude `K.J (U.symm y) = U.symm y`.
    have : K.J (U.symm y.1) = U.symm y.1 := by
      -- `congrArg` yields `U.symm y = K.J (U.symm y)`; take `symm`.
      simpa using (congrArg U.symm hEq).symm
    exact this
  · intro x
    ext
    simp
  · intro y
    ext
    simp
  · intro x y
    ext
    simp
  · intro c x
    ext
    simp

/-- A bounded equivalence intertwining `J` and `J'` induces a linear equivalence between the
`-1` eigenspaces. -/
noncomputable def negSubspaceEquiv
    (U : E ≃L[𝕜] F)
    (h : Intertwines (K := K) (K' := K') U.toContinuousLinearMap) :
    (negSubspace (K := K)) ≃ₗ[𝕜] (negSubspace (K := K')) := by
  classical
  refine
    { toFun := fun x =>
        ⟨U x.1,
          map_mem_negSubspace (K := K) (K' := K') (U := U.toContinuousLinearMap) h x.2⟩
      invFun := fun y =>
        ⟨U.symm y.1, ?_⟩
      left_inv := ?_
      right_inv := ?_
      map_add' := ?_
      map_smul' := ?_ }
  · -- `U.symm` maps `negSubspace K'` back into `negSubspace K`.
    have hy' : K'.J y.1 = -y.1 := y.2
    have hJU : K'.J (U (U.symm y.1)) = U (K.J (U.symm y.1)) := by
      simpa using
        (intertwines_apply (K := K) (K' := K') (U := U.toContinuousLinearMap) h (U.symm y.1))
    have hEq : -y.1 = U (K.J (U.symm y.1)) := by
      -- Rewrite the left-hand side using `U (U.symm y) = y` and the `-1` eigenvector hypothesis.
      have : K'.J y.1 = U (K.J (U.symm y.1)) := by
        simpa using hJU
      simpa [hy'] using this
    -- Apply `U.symm` and rearrange.
    have : K.J (U.symm y.1) = - U.symm y.1 := by
      -- `congrArg` yields `U.symm (-y) = K.J (U.symm y)`.
      -- Simplify `U.symm (-y) = -(U.symm y)`.
      have h' := congrArg U.symm hEq
      -- Now `h' : U.symm (-y) = K.J (U.symm y)`.
      -- Rewrite the left side as `-(U.symm y)` and flip.
      simpa [map_neg] using h'.symm
    exact this
  · intro x
    ext
    simp
  · intro y
    ext
    simp
  · intro x y
    ext
    simp
  · intro c x
    ext
    simp

/-!
## Index invariance

The negative index is defined as the `Module.rank` of the negative eigenspace.
An intertwining equivalence yields a linear equivalence on negative eigenspaces, hence preserves
rank (and, in particular, finite dimensionality).
-/

/-- **Negative index invariance (universe-polymorphic form).**

If `U` is a bounded linear equivalence intertwining `J` and `J'`, then the lifted negative
indices coincide.
-/
theorem negIndexCard_lift_eq_of_intertwines
    (U : E ≃L[𝕜] F)
    (h : Intertwines (K := K) (K' := K') U.toContinuousLinearMap) :
    Cardinal.lift (negIndexCard (K := K)) = Cardinal.lift (negIndexCard (K := K')) := by
  -- Reduce to rank invariance under the induced linear equivalence on `negSubspace`.
  simpa [negIndexCard] using
    (LinearEquiv.lift_rank_eq (negSubspaceEquiv (K := K) (K' := K') U h))

/-- **Pontryagin invariance.**

Finite dimensionality of the negative eigenspace is preserved under intertwining equivalences.
-/
theorem isPontryagin_iff_of_intertwines
    (U : E ≃L[𝕜] F)
    (h : Intertwines (K := K) (K' := K') U.toContinuousLinearMap) :
    IsPontryagin (K := K) ↔ IsPontryagin (K := K') := by
  constructor
  · intro hP
    haveI : FiniteDimensional 𝕜 (negSubspace (K := K)) := hP
    haveI : FiniteDimensional 𝕜 (negSubspace (K := K')) :=
      (negSubspaceEquiv (K := K) (K' := K') U h).finiteDimensional
    exact (infer_instance : FiniteDimensional 𝕜 (negSubspace (K := K')))
  · intro hP
    haveI : FiniteDimensional 𝕜 (negSubspace (K := K')) := hP
    haveI : FiniteDimensional 𝕜 (negSubspace (K := K)) :=
      (negSubspaceEquiv (K := K) (K' := K') U h).symm.finiteDimensional
    exact (infer_instance : FiniteDimensional 𝕜 (negSubspace (K := K)))

/-- If both spaces are Pontryagin, the natural-number negative index `finrank` is invariant. -/
theorem negIndexNat_eq_of_intertwines
    (U : E ≃L[𝕜] F)
    (h : Intertwines (K := K) (K' := K') U.toContinuousLinearMap)
    [IsPontryagin (K := K)] [IsPontryagin (K := K')] :
    negIndexNat (K := K) = negIndexNat (K := K') := by
  -- `negIndexNat` is `finrank` of the negative eigenspace.
  simpa [negIndexNat] using
    (LinearEquiv.finrank_eq (negSubspaceEquiv (K := K) (K' := K') U h))

end FundamentalSymmetry

end Krein
