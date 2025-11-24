https://deepwiki.com/search/help-me-leverage-the-most-appr_84e4f79d-1fcc-4245-b120-d2841c5ffab8

# DeepWiki Q&A with Code Context for Repository: leanprover-community/mathlib4
## Q1
help me leverage the most appropriate and deepest mathlib API for the below project:
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.Algebra.Module.StrongTopology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A Fundamental Symmetry J is a unitary self-adjoint involution. -/
structure FundamentalSymmetry (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  J : H →L[ℂ] H
  is_self_adjoint : IsSelfAdjoint J
  is_unitary : J ∘L J = ContinuousLinearMap.id ℂ H

variable (S : FundamentalSymmetry H)

/-- The Indefinite Inner Product [x, y] = <J x, y> -/
def kreinInner (x y : H) : ℂ := inner (S.J x) y

/-- A bounded operator T is J-Self-Adjoint if J T* J = T -/
def IsKreinSelfAdjoint (T : H →L[ℂ] H) : Prop :=
  S.J ∘L (ContinuousLinearMap.adjoint T) ∘L S.J = T

/-- The Pontryagin Index: Dimension of the maximal negative subspace.
    This is the key invariant for the RH attack. -/
def NegativeIndex : ℕ∞ :=
  -- Definition involves finding the supremum of dimensions of subspaces
  -- on which kreinInner is negative definite.
  -- For the prototype, we leave this as a definition target.
  sorry

/-- Kapustin's Operator T = A - [·, u]u.
    We use Mathlib's `rankOne` which constructs |u><v|.
    Here we want the operator f ↦ A f - [f, u]u = A f - ⟪J f, u⟫ u = A f - ⟪f, J u⟫ u.
    This corresponds to `rankOne u (J u)`. -/
def mkKapustinOperator (A : H →L[ℂ] H) (u : H) : H →L[ℂ] H :=
  A - ContinuousLinearMap.rankOne u (S.J u)

theorem kapustin_operator_self_adjoint
    (A : H →L[ℂ] H) (u : H)
    (hA_sa : IsKreinSelfAdjoint S A)
    (hA_comm : Commute S.J A)
    (h_u_real : (kreinInner S u u).im = 0) :
    IsKreinSelfAdjoint S (mkKapustinOperator S A u) := by
  rw [mkKapustinOperator, IsKreinSelfAdjoint]
  -- Proof: T# = (A - P)# = A# - P# = A - P.
  -- We need to show P# = P for P = rankOne u (J u).
  -- This is pure algebra involving J^2 = 1 and adjoint properties.
  sorry
### Answer
You're working on a Krein space theory project involving fundamental symmetries, indefinite inner products, and Kapustin operators. Let me help you leverage the appropriate Mathlib APIs for your implementation.

## Key Mathlib APIs for Your Project

### Adjoint Operations

For proving `kapustin_operator_self_adjoint`, you'll need these core adjoint properties from mathlib4:113-118 :

- `adjoint_inner_left` and `adjoint_inner_right` establish the fundamental adjoint property
- `adjoint_adjoint` shows the adjoint is involutive mathlib4:121-123
- `adjoint_comp` handles composition of adjoints mathlib4:127-131

### Self-Adjoint Operators

Your `FundamentalSymmetry` uses `IsSelfAdjoint`, which is characterized by mathlib4:217-219 . <cite />

The key theorem connecting self-adjointness to symmetry is at mathlib4:301-304 , which shows `IsSelfAdjoint A ↔ (A : E →ₗ[𝕜] E).IsSymmetric`. <cite />

### Rank-One Operators

For `mkKapustinOperator`, you're using `ContinuousLinearMap.rankOne u (S.J u)`. The adjoint of rank-one operators is handled by mathlib4:251-257 :

- `adjoint_innerSL_apply` and `adjoint_toSpanSingleton` show how adjoints of rank-one operators behave

### Proof Strategy for `kapustin_operator_self_adjoint`

To prove your theorem, you'll need to:

1. **Use linearity of adjoint**: Show `(A - P)† = A† - P†` using the `StarRing` instance at mathlib4:208-209

2. **Show `P† = P` for `P = rankOne u (J u)`**: This requires:
   - Using `adjoint_toSpanSingleton` mathlib4:255-257
   - The fact that `J² = id` (from `is_unitary`)
   - The condition `h_u_real` ensuring the Krein inner product is real

3. **Apply commutativity**: Use `hA_comm : Commute S.J A` to show `J ∘L A† ∘L J = A`

4. **Combine**: Show `J ∘L (A - P)† ∘L J = J ∘L A† ∘L J - J ∘L P† ∘L J = A - P`

### Additional Useful Lemmas

- `eq_adjoint_iff` mathlib4:153-156  provides a characterization for proving adjoint equality
- For working with inner products and adjoints, use `ext_inner_left` and `ext_inner_right` patterns shown throughout the file

## Notes

The `rankOne` operator constructs `|u⟩⟨v|` style operators. Your comment correctly identifies that `rankOne u (J u)` gives the operator `f ↦ ⟪f, J u⟫ u`. <cite /> The adjoint properties of these operators, combined with `J² = id` and the reality condition on `⟪J u, u⟫`, should make `P` self-adjoint in the Krein sense. <cite />

For the `NegativeIndex` definition, you'll likely need to work with `Submodule` and dimension theory from `LinearAlgebra`, though this is more involved and may require additional API beyond what's shown in the adjoint file. <cite />

Wiki pages you might want to explore:
- [Analysis and Measure Theory (leanprover-community/mathlib4)](/wiki/leanprover-community/mathlib4#5)
### Citations
**File:** Mathlib/Analysis/InnerProductSpace/Adjoint.lean (L113-118)
```text
theorem adjoint_inner_left (A : E →L[𝕜] F) (x : E) (y : F) : ⟪(A†) y, x⟫ = ⟪y, A x⟫ :=
  adjointAux_inner_left A x y

/-- The fundamental property of the adjoint. -/
theorem adjoint_inner_right (A : E →L[𝕜] F) (x : E) (y : F) : ⟪x, (A†) y⟫ = ⟪A x, y⟫ :=
  adjointAux_inner_right A x y
```
**File:** Mathlib/Analysis/InnerProductSpace/Adjoint.lean (L121-123)
```text
@[simp]
theorem adjoint_adjoint (A : E →L[𝕜] F) : A†† = A :=
  adjointAux_adjointAux A
```
**File:** Mathlib/Analysis/InnerProductSpace/Adjoint.lean (L127-131)
```text
@[simp]
theorem adjoint_comp (A : F →L[𝕜] G) (B : E →L[𝕜] F) : (A ∘L B)† = B† ∘L A† := by
  ext v
  refine ext_inner_left 𝕜 fun w => ?_
  simp only [adjoint_inner_right, ContinuousLinearMap.coe_comp', Function.comp_apply]
```
**File:** Mathlib/Analysis/InnerProductSpace/Adjoint.lean (L153-156)
```text
theorem eq_adjoint_iff (A : E →L[𝕜] F) (B : F →L[𝕜] E) : A = B† ↔ ∀ x y, ⟪A x, y⟫ = ⟪x, B y⟫ := by
  refine ⟨fun h x y => by rw [h, adjoint_inner_left], fun h => ?_⟩
  ext x
  exact ext_inner_right 𝕜 fun y => by simp only [adjoint_inner_left, h x y]
```
**File:** Mathlib/Analysis/InnerProductSpace/Adjoint.lean (L208-209)
```text
instance : StarRing (E →L[𝕜] E) :=
  ⟨LinearIsometryEquiv.map_add adjoint⟩
```
**File:** Mathlib/Analysis/InnerProductSpace/Adjoint.lean (L217-219)
```text
/-- A continuous linear operator is self-adjoint iff it is equal to its adjoint. -/
theorem isSelfAdjoint_iff' {A : E →L[𝕜] E} : IsSelfAdjoint A ↔ A† = A :=
  Iff.rfl
```
**File:** Mathlib/Analysis/InnerProductSpace/Adjoint.lean (L251-257)
```text
theorem adjoint_innerSL_apply (x : E) :
    adjoint (innerSL 𝕜 x) = toSpanSingleton 𝕜 x :=
  ext_ring <| ext_inner_left 𝕜 <| fun _ => by simp [adjoint_inner_right]

theorem adjoint_toSpanSingleton (x : E) :
    adjoint (toSpanSingleton 𝕜 x) = innerSL 𝕜 x := by
  simp [← adjoint_innerSL_apply]
```
**File:** Mathlib/Analysis/InnerProductSpace/Adjoint.lean (L301-304)
```text
theorem _root_.ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric {A : E →L[𝕜] E} :
    IsSelfAdjoint A ↔ (A : E →ₗ[𝕜] E).IsSymmetric :=
  ⟨fun hA => hA.isSymmetric, fun hA =>
    ext fun x => ext_inner_right 𝕜 fun y => (A.adjoint_inner_left y x).symm ▸ (hA x y).symm⟩
```
## Q2
i want to formalize each element on its own right,, starting from Krein spaces. Help me formalize Krein spaces and their core API and main results for mathlib at the higest, deepest level of generality
### Answer
You're asking to formalize **Krein spaces** as a foundational mathematical structure in Mathlib, building from the ground up with full generality rather than just implementing them for your specific Riemann Hypothesis application.

## Understanding Krein Spaces

A Krein space is a vector space with an **indefinite inner product** (also called a Krein inner product) that can be decomposed into positive and negative definite subspaces. This generalizes Hilbert spaces by allowing the inner product to be indefinite. <cite />

## Formalization Strategy

Based on Mathlib's existing inner product space infrastructure, here's how to formalize Krein spaces at the highest level of generality:

### 1. Core Structure: `KreinSpace` Class

Model this after `InnerProductSpace` mathlib4:102-111 . Your Krein space should:

```lean
class KreinSpace (𝕜 : Type*) (E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] where
  /-- The indefinite inner product -/
  kreinInner : E → E → 𝕜
  /-- Hermitian symmetry -/
  conj_krein_symm : ∀ x y, conj (kreinInner y x) = kreinInner x y
  /-- Additivity in first argument -/
  add_left : ∀ x y z, kreinInner (x + y) z = kreinInner x z + kreinInner y z
  /-- Conjugate linearity in first argument -/
  smul_left : ∀ x y r, kreinInner (r • x) y = conj r * kreinInner x y
  /-- Non-degeneracy -/
  nondegenerate : ∀ x, (∀ y, kreinInner x y = 0) → x = 0
```

Note: Unlike `InnerProductSpace` which requires `norm_sq_eq_re_inner` mathlib4:105-105 , Krein spaces don't have a canonical norm from the indefinite inner product alone. <cite />

### 2. Fundamental Decomposition

The key theorem is that every Krein space admits a **fundamental decomposition** `E = E₊ ⊕ E₋` where the Krein inner product is positive definite on `E₊` and negative definite on `E₋`:

```lean
structure FundamentalDecomposition (𝕜 : Type*) (E : Type*)
    [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [KreinSpace 𝕜 E] where
  pos : Submodule 𝕜 E
  neg : Submodule 𝕜 E
  /-- Direct sum decomposition -/
  isCompl : IsCompl pos neg
  /-- Orthogonality -/
  orthogonal : ∀ x ∈ pos, ∀ y ∈ neg, kreinInner x y = 0
  /-- Positive definiteness on pos -/
  pos_definite : ∀ x ∈ pos, x ≠ 0 → 0 < re (kreinInner x x)
  /-- Negative definiteness on neg -/
  neg_definite : ∀ x ∈ neg, x ≠ 0 → re (kreinInner x x) < 0
```

### 3. Fundamental Symmetry

Your `FundamentalSymmetry` is the operator-theoretic representation of the decomposition. Generalize it:

```lean
structure FundamentalSymmetry (𝕜 : Type*) (E : Type*)
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [KreinSpace 𝕜 E] where
  J : E →L[𝕜] E
  /-- Self-adjoint with respect to the Hilbert inner product -/
  is_self_adjoint : IsSelfAdjoint J
  /-- Involution -/
  is_involution : J ∘L J = ContinuousLinearMap.id 𝕜 E
  /-- Relates Krein and Hilbert inner products -/
  krein_eq_hilbert : ∀ x y, kreinInner x y = inner (J x) y
```

The relationship between fundamental decomposition and fundamental symmetry should be formalized as an equivalence. <cite />

### 4. Core API Lemmas

Following the pattern in `InnerProductSpace.Core` mathlib4:194-240 , develop:

**Basic properties:**
- `krein_inner_conj_symm`
- `krein_inner_add_left`, `krein_inner_add_right`
- `krein_inner_smul_left`, `krein_inner_smul_right`
- `krein_inner_neg_left`, `krein_inner_neg_right`
- `krein_inner_sub_left`, `krein_inner_sub_right`
- `krein_inner_zero_left`, `krein_inner_zero_right`

**Orthogonality:**
- `krein_orthogonal_def : KreinOrthogonal x y ↔ kreinInner x y = 0`
- `krein_orthogonal_comm`
- Orthogonal complement for subspaces

### 5. Pontryagin Spaces (Finite Rank Indefiniteness)

A **Pontryagin space** is a Krein space where one of `E₊` or `E₋` is finite-dimensional:

```lean
class PontryaginSpace (𝕜 : Type*) (E : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [KreinSpace 𝕜 E] where
  exists_finite_neg : ∃ (decomp : FundamentalDecomposition 𝕜 E),
    FiniteDimensional 𝕜 decomp.neg
```

The **Pontryagin index** (or **negative index**) is:

```lean
def pontryaginIndex [PontryaginSpace 𝕜 E] : ℕ :��
  FiniteDimensional.finrank 𝕜 (Classical.choose PontryaginSpace.exists_finite_neg).neg
```

### 6. J-Self-Adjoint Operators

Generalize your `IsKreinSelfAdjoint`:

```lean
def IsKreinSelfAdjoint (𝕜 : Type*) (E : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [KreinSpace 𝕜 E]
    (J : FundamentalSymmetry 𝕜 E) (T : E →L[𝕜] E) : Prop :=
  J.J ∘L (adjoint T) ∘L J.J = T
```

Key theorems:
- Composition of J-self-adjoint operators
- Spectrum properties of J-self-adjoint operators
- Existence of J-orthonormal bases

### 7. Connection to Existing Mathlib Infrastructure

**From Hilbert to Krein:** Every Hilbert space is a Krein space with `kreinInner = inner`:

```lean
instance (priority := 100) [InnerProductSpace 𝕜 E] : KreinSpace 𝕜 E where
  kreinInner := inner
  conj_krein_symm := inner_conj_symm
  add_left := inner_add_left
  smul_left := inner_smul_left
  nondegenerate := fun x h => ...
```

**Induced topology:** Use the pattern from `InnerProductSpace.Core.topology_eq` mathlib4:502-525  to show the Krein inner product induces a locally convex topology. <cite />

## Main Results to Formalize

1. **Fundamental decomposition theorem**: Every Krein space admits a fundamental decomposition (existence and uniqueness up to isomorphism)
2. **Equivalence**: Fundamental decompositions ↔ Fundamental symmetries
3. **Pontryagin's invariance theorem**: The Pontryagin index is independent of the choice of fundamental decomposition
4. **Spectral theory**: J-self-adjoint compact operators have real spectrum
5. **Riesz representation**: Continuous linear functionals on Krein spaces

## Notes

This formalization should live in a new file `Mathlib/Analysis/InnerProductSpace/Krein/Defs.lean` following the structure of the existing inner product space hierarchy mathlib4:1747-1795 . The generality here (working over `RCLike 𝕜` rather than just `ℂ`, not assuming completeness unless needed) follows Mathlib's philosophy of maximum generality. <cite />

Wiki pages you might want to explore:
- [Overview (leanprover-community/mathlib4)](/wiki/leanprover-community/mathlib4#1)
### Citations
**File:** Mathlib/Analysis/InnerProductSpace/Defs.lean (L102-111)
```text
class InnerProductSpace (𝕜 : Type*) (E : Type*) [RCLike 𝕜] [SeminormedAddCommGroup E] extends
    NormedSpace 𝕜 E, Inner 𝕜 E where
  /-- The inner product induces the norm. -/
  norm_sq_eq_re_inner : ∀ x : E, ‖x‖ ^ 2 = re (inner x x)
  /-- The inner product is *Hermitian*, taking the `conj` swaps the arguments. -/
  conj_inner_symm : ∀ x y, conj (inner y x) = inner x y
  /-- The inner product is additive in the first coordinate. -/
  add_left : ∀ x y z, inner (x + y) z = inner x z + inner y z
  /-- The inner product is conjugate linear in the first coordinate. -/
  smul_left : ∀ x y r, inner (r • x) y = conj r * inner x y
```
**File:** Mathlib/Analysis/InnerProductSpace/Defs.lean (L194-240)
```text
namespace InnerProductSpace.Core

section PreInnerProductSpace.Core

variable [AddCommGroup F] [Module 𝕜 F] [c : PreInnerProductSpace.Core 𝕜 F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- Local notation for `RCLike.ext_iff 𝕜` -/
local notation "ext_iff" => @RCLike.ext_iff 𝕜 _

/-- Local notation for `starRingEnd _` -/
local postfix:90 "†" => starRingEnd _

/-- Inner product defined by the `PreInnerProductSpace.Core` structure. We can't reuse
`PreInnerProductSpace.Core.toInner` because it takes `PreInnerProductSpace.Core` as an explicit
argument. -/
def toPreInner' : Inner 𝕜 F :=
  c.toInner

attribute [local instance] toPreInner'

/-- The norm squared function for `PreInnerProductSpace.Core` structure. -/
def normSq (x : F) :=
  re ⟪x, x⟫

/-- The norm squared function for `PreInnerProductSpace.Core` structure. -/
local notation "normSqF" => @normSq 𝕜 F _ _ _ _

theorem inner_conj_symm (x y : F) : ⟪y, x⟫† = ⟪x, y⟫ :=
  c.conj_inner_symm x y

theorem inner_self_nonneg {x : F} : 0 ≤ re ⟪x, x⟫ :=
  c.re_inner_nonneg _

theorem inner_self_im (x : F) : im ⟪x, x⟫ = 0 := by
  rw [← @ofReal_inj 𝕜, im_eq_conj_sub]
  simp [inner_conj_symm]

theorem inner_add_left (x y z : F) : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫ :=
  c.add_left _ _ _

theorem inner_add_right (x y z : F) : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫ := by
  rw [← inner_conj_symm, inner_add_left, RingHom.map_add]; simp only [inner_conj_symm]

theorem ofReal_normSq_eq_inner_self (x : F) : (normSqF x : 𝕜) = ⟪x, x⟫ := by
  rw [ext_iff]
```
**File:** Mathlib/Analysis/InnerProductSpace/Defs.lean (L502-525)
```text
lemma topology_eq
    [tF : TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜 F]
    (h : ContinuousAt (fun (v : F) ↦ cd.inner v v) 0)
    (h' : IsVonNBounded 𝕜 {v : F | re (cd.inner v v) < 1}) :
    tF = cd.toNormedAddCommGroup.toMetricSpace.toUniformSpace.toTopologicalSpace := by
  let p : Seminorm 𝕜 F := @normSeminorm 𝕜 F _ cd.toNormedAddCommGroup.toSeminormedAddCommGroup
    InnerProductSpace.Core.toNormedSpace
  suffices WithSeminorms (fun (i : Fin 1) ↦ p) by
    rw [(SeminormFamily.withSeminorms_iff_topologicalSpace_eq_iInf _).1 this]
    simp
  have : p.ball 0 1 = {v | re (cd.inner v v) < 1} := by
    ext v
    simp only [ball_normSeminorm, Metric.mem_ball, dist_eq_norm, sub_zero, Set.mem_setOf_eq, p]
    change √(re (cd.inner v v)) < 1 ↔ re (cd.inner v v) < 1
    conv_lhs => rw [show (1 : ℝ) = √ 1 by simp]
    rw [sqrt_lt_sqrt_iff]
    exact InnerProductSpace.Core.inner_self_nonneg
  rw [withSeminorms_iff_mem_nhds_isVonNBounded, this]
  refine ⟨?_, h'⟩
  have A : ContinuousAt (fun (v : F) ↦ re (cd.inner v v)) 0 := by fun_prop
  have B : Set.Iio 1 ∈ 𝓝 (re (cd.inner 0 0)) := by
    simp only [InnerProductSpace.Core.inner_zero_left, map_zero]
    exact Iio_mem_nhds (by positivity)
  exact A B
```
**File:** Mathlib.lean (L1747-1795)
```text
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Affine
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.CanonicalTensor
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.ConformalLinearMap
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.Harmonic.Analytic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.InnerProductSpace.MulOpposite
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.InnerProductSpace.OfNorm
import Mathlib.Analysis.InnerProductSpace.Orientation
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.Semisimple
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.InnerProductSpace.TwoDim
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
```
## Q3
conduct a deeper research in mathlib to identify the most appropriate API for our formalization
### Answer
Based on my search through the Mathlib4 codebase, here are the most appropriate and deepest APIs for formalizing Krein spaces:

## Core Structure: Bilinear Forms Instead of Inner Product Spaces

For Krein spaces, you should **not** use `InnerProductSpace` directly, as it requires positive definiteness. mathlib4:169-178  Instead, use **`LinearMap.BilinForm`** (bilinear forms) as your foundation for the indefinite inner product.

## Indefinite Inner Product

The indefinite inner product should be formalized as a **symmetric bilinear form**:

- **`LinearMap.BilinForm.IsSymm`**: Define symmetry of the bilinear form mathlib4:84-96
- The structure is defined in `Mathlib/LinearAlgebra/BilinearForm/Properties.lean` and provides the basic properties you need

## Nondegeneracy

For the nondegeneracy condition (which replaces positive definiteness in Krein spaces):

- **`LinearMap.BilinForm.Nondegenerate`**: States that for all nonzero `m`, there exists `n` with `B m n ≠ 0` mathlib4:271-280
- **`nondegenerate_iff_ker_eq_bot`**: Equivalently characterizes nondegeneracy via trivial kernel mathlib4:312-318

## Orthogonality and Orthogonal Complements

For orthogonality with respect to your indefinite form:

- **`LinearMap.BilinForm.IsOrtho`**: Two elements are orthogonal if `B x y = 0` mathlib4:47-53
- **`LinearMap.BilinForm.orthogonal`**: The orthogonal complement of a submodule mathlib4:122-136
- **`orthogonal_span_singleton_eq_toLin_ker`**: Characterizes orthogonal complements of singleton spans mathlib4:175-183

## Fundamental Decomposition

For the fundamental decomposition into positive and negative subspaces:

- **`IsCompl`**: Two subspaces are complementary if they are disjoint and codisjoint (their sup is top) mathlib4:398-407
- **`isCompl_span_singleton_orthogonal`**: Shows when a subspace and its orthogonal complement are complementary mathlib4:192-195

This provides the infrastructure for decomposing your space as `V = V₊ ⊕ V₋` where the bilinear form is positive/negative definite on each component.

## Fundamental Symmetry J

The fundamental symmetry operator J (which satisfies J² = I and defines the decomposition) should be formalized using:

- **`IsSelfAdjoint`**: For self-adjointness of J with respect to the standard inner product (if working in a Hilbert space setting) mathlib4:45-47
- For the involution property J² = I, you would use standard `LinearMap` or `ContinuousLinearMap` properties

## J-Self-Adjoint Operators

For operators that are self-adjoint with respect to the indefinite form (the J-inner product):

- **`LinearMap.IsAdjointPair`**: Defines when two maps `f` and `g` are adjoint with respect to bilinear forms `B` and `B'` mathlib4:453-456
- **`isAdjointPair_unique_of_nondegenerate`**: Uniqueness of adjoints for nondegenerate forms mathlib4:327-330

For a J-self-adjoint operator `A`, you would express this as `IsAdjointPair B_J B_J A A` where `B_J` is your indefinite inner product.

## Additional Useful Infrastructure

- **Dual bases**: For nondegenerate bilinear forms mathlib4:369-376
- **`QuadraticMap.PosDef`**: For expressing positive definiteness on the positive subspace mathlib4:1130-1133
- For sesquilinear forms (complex case), see `Mathlib/LinearAlgebra/SesquilinearForm/Basic.lean` mathlib4:1-35

## Notes

The key insight is that Krein spaces require **symmetric nondegenerate bilinear forms** rather than positive definite inner products. The Mathlib4 infrastructure for bilinear forms in `Mathlib/LinearAlgebra/BilinearForm/` provides exactly the right level of generality. You should build your Krein space structure by:

1. Starting with a `BilinForm K V` that is symmetric and nondegenerate
2. Using `IsCompl` to express the fundamental decomposition
3. Defining the fundamental symmetry J as a linear map satisfying appropriate properties
4. Using `IsAdjointPair` to define J-adjoint operators

This approach mirrors how `InnerProductSpace` is structured mathlib4:94-100  but works with the more general setting of indefinite forms.
### Citations
**File:** Mathlib/Analysis/InnerProductSpace/Defs.lean (L94-100)
```text
/-- A (pre) inner product space is a vector space with an additional operation called inner product.
The (semi)norm could be derived from the inner product, instead we require the existence of a
seminorm and the fact that `‖x‖^2 = re ⟪x, x⟫` to be able to put instances on `𝕂` or product spaces.

Note that `NormedSpace` does not assume that `‖x‖=0` implies `x=0` (it is rather a seminorm).

To construct a seminorm from an inner product, see `PreInnerProductSpace.ofCore`.
```
**File:** Mathlib/Analysis/InnerProductSpace/Defs.lean (L169-178)
```text
  smul_left := cd.smul_left

/-- Define `PreInnerProductSpace.Core` from `InnerProductSpace`. Defined to reuse lemmas about
`PreInnerProductSpace.Core` for `PreInnerProductSpace`s. Note that the `Seminorm` instance provided
by `PreInnerProductSpace.Core.norm` is propositionally but not definitionally equal to the original
norm. -/
def PreInnerProductSpace.toCore [SeminormedAddCommGroup E] [c : InnerProductSpace 𝕜 E] :
    PreInnerProductSpace.Core 𝕜 E where
  __ := c
  re_inner_nonneg x := by rw [← InnerProductSpace.norm_sq_eq_re_inner]; apply sq_nonneg
```
**File:** Mathlib/LinearAlgebra/BilinearForm/Properties.lean (L84-96)
```text
structure IsSymm (B : BilinForm R M) : Prop where
  protected eq : ∀ x y, B x y = B y x

theorem isSymm_def : IsSymm B ↔ ∀ x y, B x y = B y x where
  mp := fun ⟨h⟩ ↦ h
  mpr h := ⟨h⟩

theorem isSymm_iff : IsSymm B ↔ LinearMap.IsSymm B := by
  simp [isSymm_def, LinearMap.isSymm_def]

namespace IsSymm

theorem isRefl (H : B.IsSymm) : B.IsRefl := fun x y H1 => H.eq x y ▸ H1
```
**File:** Mathlib/LinearAlgebra/BilinearForm/Properties.lean (L271-280)
```text
/-- A nondegenerate bilinear form is a bilinear form such that the only element that is orthogonal
to every other element is `0`; i.e., for all nonzero `m` in `M`, there exists `n` in `M` with
`B m n ≠ 0`.

Note that for general (neither symmetric nor antisymmetric) bilinear forms this definition has a
chirality; in addition to this "left" nondegeneracy condition one could define a "right"
nondegeneracy condition that in the situation described, `B n m ≠ 0`.  This variant definition is
not currently provided in mathlib. In finite dimension either definition implies the other. -/
def Nondegenerate (B : BilinForm R M) : Prop :=
  ∀ m : M, (∀ n : M, B m n = 0) → m = 0
```
**File:** Mathlib/LinearAlgebra/BilinearForm/Properties.lean (L312-318)
```text
theorem nondegenerate_iff_ker_eq_bot {B : BilinForm R M} :
    B.Nondegenerate ↔ LinearMap.ker B = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  simp [Nondegenerate, LinearMap.ext_iff]

theorem Nondegenerate.ker_eq_bot {B : BilinForm R M} (h : B.Nondegenerate) :
    LinearMap.ker B = ⊥ := nondegenerate_iff_ker_eq_bot.mp h
```
**File:** Mathlib/LinearAlgebra/BilinearForm/Properties.lean (L327-330)
```text
theorem isAdjointPair_unique_of_nondegenerate (B : BilinForm R₁ M₁) (b : B.Nondegenerate)
    (φ ψ₁ ψ₂ : M₁ →ₗ[R₁] M₁) (hψ₁ : IsAdjointPair B B ψ₁ φ) (hψ₂ : IsAdjointPair B B ψ₂ φ) :
    ψ₁ = ψ₂ :=
  B.compLeft_injective b <| ext fun v w => by rw [compLeft_apply, compLeft_apply, hψ₁, hψ₂]
```
**File:** Mathlib/LinearAlgebra/BilinearForm/Properties.lean (L369-376)
```text
/-- The `B`-dual basis `B.dualBasis hB b` to a finite basis `b` satisfies
`B (B.dualBasis hB b i) (b j) = B (b i) (B.dualBasis hB b j) = if i = j then 1 else 0`,
where `B` is a nondegenerate (symmetric) bilinear form and `b` is a finite basis. -/
noncomputable def dualBasis (B : BilinForm K V) (hB : B.Nondegenerate) (b : Basis ι K V) :
    Basis ι K V :=
  haveI := b.finiteDimensional_of_finite
  b.dualBasis.map (B.toDual hB).symm

```
**File:** Mathlib/LinearAlgebra/BilinearForm/Orthogonal.lean (L47-53)
```text
/-- The proposition that two elements of a bilinear form space are orthogonal. For orthogonality
of an indexed set of elements, use `BilinForm.iIsOrtho`. -/
def IsOrtho (B : BilinForm R M) (x y : M) : Prop :=
  B x y = 0

theorem isOrtho_def {B : BilinForm R M} {x y : M} : B.IsOrtho x y ↔ B x y = 0 :=
  Iff.rfl
```
**File:** Mathlib/LinearAlgebra/BilinearForm/Orthogonal.lean (L122-136)
```text
/-- The orthogonal complement of a submodule `N` with respect to some bilinear form is the set of
elements `x` which are orthogonal to all elements of `N`; i.e., for all `y` in `N`, `B y x = 0`.

Note that for general (neither symmetric nor antisymmetric) bilinear forms this definition has a
chirality; in addition to this "right" orthogonal complement one could define a "left" orthogonal
complement for which, for all `y` in `N`, `B x y = 0`.  This variant definition is not currently
provided in mathlib. -/
def orthogonal (B : BilinForm R M) (N : Submodule R M) : Submodule R M where
  carrier := { m | ∀ n ∈ N, IsOrtho B n m }
  zero_mem' x _ := isOrtho_zero_right x
  add_mem' {x y} hx hy n hn := by
    rw [IsOrtho, add_right, show B n x = 0 from hx n hn, show B n y = 0 from hy n hn, zero_add]
  smul_mem' c x hx n hn := by
    rw [IsOrtho, smul_right, show B n x = 0 from hx n hn, mul_zero]

```
**File:** Mathlib/LinearAlgebra/BilinearForm/Orthogonal.lean (L175-183)
```text
theorem orthogonal_span_singleton_eq_toLin_ker {B : BilinForm K V} (x : V) :
    B.orthogonal (K ∙ x) = LinearMap.ker (LinearMap.BilinForm.toLinHomAux₁ B x) := by
  ext y
  simp_rw [mem_orthogonal_iff, LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · exact fun h => h x ⟨1, one_smul _ _⟩
  · rintro h _ ⟨z, rfl⟩
    rw [IsOrtho, smul_left, mul_eq_zero]
    exact Or.intro_right _ h
```
**File:** Mathlib/LinearAlgebra/BilinearForm/Orthogonal.lean (L192-195)
```text
theorem isCompl_span_singleton_orthogonal {B : BilinForm K V} {x : V} (hx : ¬B.IsOrtho x x) :
    IsCompl (K ∙ x) (B.orthogonal <| K ∙ x) :=
  { disjoint := disjoint_iff.2 <| span_singleton_inf_orthogonal_eq_bot hx
    codisjoint := codisjoint_iff.2 <| span_singleton_sup_orthogonal_eq_top hx }
```
**File:** Mathlib/Order/Disjoint.lean (L398-407)
```text
/-- Two elements `x` and `y` are complements of each other if `x ⊔ y = ⊤` and `x ⊓ y = ⊥`. -/
structure IsCompl [PartialOrder α] [BoundedOrder α] (x y : α) : Prop where
  /-- If `x` and `y` are to be complementary in an order, they should be disjoint. -/
  protected disjoint : Disjoint x y
  /-- If `x` and `y` are to be complementary in an order, they should be codisjoint. -/
  protected codisjoint : Codisjoint x y

theorem isCompl_iff [PartialOrder α] [BoundedOrder α] {a b : α} :
    IsCompl a b ↔ Disjoint a b ∧ Codisjoint a b :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩
```
**File:** Mathlib/Algebra/Star/SelfAdjoint.lean (L45-47)
```text
/-- An element is self-adjoint if it is equal to its star. -/
def IsSelfAdjoint [Star R] (x : R) : Prop :=
  star x = x
```
**File:** Mathlib/LinearAlgebra/SesquilinearForm/Basic.lean (L1-35)
```text
/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow
-/
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Sesquilinear maps

This file provides properties about sesquilinear maps and forms. The maps considered are of the
form `M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M`, where `I₁ : R₁ →+* R` and `I₂ : R₂ →+* R` are ring homomorphisms and
`M₁` is a module over `R₁`, `M₂` is a module over `R₂` and `M` is a module over `R`.
Sesquilinear forms are the special case that `M₁ = M₂`, `M = R₁ = R₂ = R`, and `I₁ = RingHom.id R`.
Taking additionally `I₂ = RingHom.id R`, then one obtains bilinear forms.

Sesquilinear maps are a special case of the bilinear maps defined in `BilinearMap.lean`, and many
basic lemmas about construction and elementary calculations are found there.

## Main declarations

* `IsOrtho`: states that two vectors are orthogonal with respect to a sesquilinear map
* `IsSymm`, `IsAlt`: states that a sesquilinear form is symmetric and alternating, respectively
* `orthogonalBilin` provides the orthogonal complement with respect to a sesquilinear form

## References

* <https://en.wikipedia.org/wiki/Sesquilinear_form#Over_arbitrary_rings>

## Tags

Sesquilinear form, Sesquilinear map
-/
```
**File:** Mathlib/LinearAlgebra/SesquilinearForm/Basic.lean (L453-456)
```text
/-- Given a pair of modules equipped with bilinear maps, this is the condition for a pair of
maps between them to be mutually adjoint. -/
def IsAdjointPair (f : M → M₁) (g : M₁ → M) :=
  ∀ x y, B' (f x) y = B x (g y)
```
**File:** Mathlib/LinearAlgebra/QuadraticForm/Basic.lean (L1130-1133)
```text
/-- A positive definite quadratic form is positive on nonzero vectors. -/
def PosDef (Q₂ : QuadraticMap R₂ M N) : Prop :=
  ∀ x, x ≠ 0 → 0 < Q₂ x

```
## Q4
conduct a deeper research in mathlib to identify the most appropriate API for our formalization
## Krein Space Formalization API in Mathlib4
This codemap traces the API stack for formalizing Krein spaces in Mathlib4, showing how bilinear forms [1a-1c] provide the foundation for indefinite inner products, orthogonal complements enable fundamental decompositions [2a-2c], adjoint pairs define J-self-adjoint operators [3a-3c], existing operator infrastructure supports fundamental symmetries [4a-4c], and positivity properties handle subspace definiteness [5a-5c].
### 1. Bilinear Form Foundation for Krein Spaces
How indefinite inner products are formalized using bilinear forms instead of positive-definite inner products
### 1a. Symmetric Bilinear Form Structure (`Properties.lean:84`)
Defines symmetry property essential for Krein inner products
```text
structure IsSymm (B : BilinForm R M) : Prop where
```
### 1b. Nondegeneracy Condition (`Properties.lean:279`)
Replaces positive definiteness for indefinite forms
```text
def Nondegenerate (B : BilinForm R M) : Prop :=
```
### 1c. Kernel Characterization (`Properties.lean:312`)
Connects nondegeneracy to trivial kernel
```text
theorem nondegenerate_iff_ker_eq_bot {B : BilinForm R M} :
```
### 2. Orthogonal Complement and Fundamental Decomposition
How orthogonal complements and decompositions enable Krein space structure
### 2a. Orthogonal Complement Definition (`Orthogonal.lean:129`)
Creates orthogonal subspaces for decomposition
```text
def orthogonal (B : BilinForm R M) (N : Submodule R M) : Submodule R M where
```
### 2b. Complementary Subspaces (`Disjoint.lean:399`)
Defines fundamental decomposition structure
```text
structure IsCompl [PartialOrder α] [BoundedOrder α] (x y : α) : Prop where
```
### 2c. Fundamental Decomposition Theorem (`Orthogonal.lean:192`)
Shows how non-isotropic vectors generate complementary decompositions
```text
theorem isCompl_span_singleton_orthogonal {B : BilinForm K V} {x : V} (hx : ¬B.IsOrtho x x) :
```
### 3. J-Self-Adjoint Operators via Adjoint Pairs
How operators self-adjoint with respect to indefinite forms are defined
### 3a. Adjoint Pair Definition (`Basic.lean:455`)
General framework for adjointness with respect to forms
```text
def IsAdjointPair (f : M → M₁) (g : M₁ → M) :=
```
### 3b. Hilbert Space Adjoint Implementation (`Adjoint.lean:245`)
Shows how adjoint pairs work in inner product spaces
```text
theorem isAdjointPair_inner (A : E →L[𝕜] F) :
```
### 3c. Self-Adjoint Operators (`Basic.lean:567`)
Special case for operators equal to their own adjoint
```text
protected def IsSelfAdjoint (f : M → M) :=
```
### 4. Fundamental Symmetry Implementation
How fundamental symmetries are constructed using existing operator infrastructure
### 4a. Self-Adjoint Characterization (`Adjoint.lean:218`)
Connects abstract self-adjointness to concrete adjoint equality
```text
theorem isSelfAdjoint_iff' {A : E →L[𝕜] E} : IsSelfAdjoint A ↔ A† = A :=
```
### 4b. Adjoint Involution Property (`Adjoint.lean:120`)
Essential for J² = I property of fundamental symmetries
```text
theorem adjoint_adjoint {A : E →L[𝕜] F} : A†† = A :=
```
### 4c. Star Ring Structure (`Adjoint.lean:208`)
Provides algebraic structure for adjoint operations
```text
instance : StarRing (E →L[𝕜] E) :=
```
### 5. Positive/Negative Definite Subspaces
How definiteness properties are handled for subspaces in Krein decomposition
### 5a. Positive Semidefinite Forms (`Properties.lean:203`)
Defines positivity on subspaces
```text
structure IsPosSemidef [LE R] (B : BilinForm R M) extends
```
### 5b. Positive Definite Quadratic Forms (`Basic.lean:1131`)
Strict positivity for Pontryagin spaces
```text
def PosDef (Q₂ : QuadraticMap R₂ M N) : Prop :=
```
### 5c. Nondegenerate Restrictions (`Orthogonal.lean:204`)
Ensures subspaces inherit nondegeneracy
```text
theorem nondegenerate_restrict_of_disjoint_orthogonal (B : BilinForm R₁ M₁) (b : B.IsRefl)
```
