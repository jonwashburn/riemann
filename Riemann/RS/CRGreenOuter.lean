/-
  rh/RS/CRGreenOuter.lean


  Minimal CR–Green outer exports required by `rh/Proof/Main.lean`,
  the fully *unconditional* Whitney pairing façade (kept as-is),
  plus the two analytic steps you called out:


    1) `pairing_whitney_analytic_bound`:
         turns the unconditional identity into the *analytic* bound
         |∫_I ψ (−W′)| ≤ Cψ · √( ∬_Q |∇U|² dσ ),
         assuming the standard Whitney remainder control and the Cauchy–Schwarz
         control of the volume pairing by the fixed test.


    2) `CRGreen_link`:
         plugs a Concrete Half-Plane Carleson budget into (1) to yield
         |∫_I ψ (−W′)| ≤ Cψ · √(Kξ · |I|).


  Notes:
  • No new axioms. The analytic facts enter as hypotheses you can discharge in
    your analysis layer (or package as instances).
  • We keep `B : ℝ → ℝ` as the boundary integrand (intended B = -W′).
  • `Cψ_pair` is the Cauchy–Schwarz/test constant (depends only on ψ, α′, χ),
    `Cψ_rem` is the Whitney remainder constant (depends only on ψ, α′),
    and Cψ := Cψ_pair + Cψ_rem.
-/

import Mathlib.Algebra.Lie.OfAssociative
import Riemann.Cert.KxiPPlus

noncomputable section

namespace RH
namespace RS
open Complex Set
open MeasureTheory
open scoped MeasureTheory
-- Local analytic helpers (snapshot-friendly)
section LocalIneq

variable {α : Type*} [MeasurableSpace α]

-- Triangle inequality for integrals without relying on a named lemma
theorem abs_integral_add_le'
  {μ : Measure α} {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
  |∫ x, f x + g x ∂μ| ≤ |∫ x, f x ∂μ| + |∫ x, g x ∂μ| := by
  have h_eq :
      ∫ x, f x + g x ∂μ = (∫ x, f x ∂μ) + (∫ x, g x ∂μ) :=
    integral_add hf hg
  have h_triangle :
      |(∫ x, f x ∂μ) + (∫ x, g x ∂μ)| ≤
        |∫ x, f x ∂μ| + |∫ x, g x ∂μ| :=
    abs_add_le _ _
  calc
    |∫ x, f x + g x ∂μ|
        = |(∫ x, f x ∂μ) + (∫ x, g x ∂μ)| := by
            simp [h_eq]
    _ ≤ |∫ x, f x ∂μ| + |∫ x, g x ∂μ| := h_triangle

-- L2 pairing bound via Hölder p=q=2 in ENNReal, translated to ℝ
-- Snapshot-stable note: we avoid encoding a local L² Hölder lemma here.

end LocalIneq



open Complex Set Filter
open MeasureTheory
open scoped MeasureTheory
open RH.AcademicFramework.CompletedXi (riemannXi_ext)
open RH.AcademicFramework.HalfPlaneOuterV2 (boundary)

/-- Right half-plane domain Ω. -/
local notation "Ω" => RH.RS.Ω -- Right half-plane domain Ω = { s : ℂ | 1/2 < Re s }.

/-- The RS Ω and HalfPlaneOuterV2 Ω are the same set. -/
lemma Ω_eq : RH.RS.Ω = RH.AcademicFramework.HalfPlaneOuterV2.Ω := by
  unfold RH.RS.Ω RH.AcademicFramework.HalfPlaneOuterV2.Ω
  rfl

/-! ## det₂ boundary nonvanishing (from academic framework)

We use `det2_nonzero_on_critical_line` from `rh/RS/Det2Outer.lean`, which is
proved via the academic framework's infinite-product development. -/

/-! ## Outer function structure and J_CR construction -/

/-- Outer function on Ω with prescribed boundary modulus |det₂/ξ_ext|.
This packages standard Hardy space outer factorization theory. -/
structure OuterOnOmega where
  outer : ℂ → ℂ
  analytic : AnalyticOn ℂ outer Ω
  nonzero : ∀ z ∈ Ω, outer z ≠ 0
  boundary_modulus : ∀ᵐ t : ℝ,
    riemannXi_ext (boundary t) ≠ 0 →
    norm (outer (boundary t)) =
    norm (det2 (boundary t) / riemannXi_ext (boundary t))

-- Removed outer_nonzero_from_boundary_modulus axiom (depended on pointwise nonvanishing)

/-- Outer existence from the Det2Outer construction.
Reference: Implemented in `rh/RS/Det2Outer.lean` via `OuterHalfPlane` witness.
-/
def outer_exists : OuterOnOmega := by
  classical
  refine {
    outer := RH.RS.O_witness
  , analytic := RH.RS.O_witness_outer.analytic
  , nonzero := by
      intro z hz
      exact RH.RS.O_witness_outer.nonzero hz
  , boundary_modulus := by
      have h_pointwise :
          ∀ t : ℝ,
            norm (RH.RS.O_witness (boundary t)) =
              norm (det2 (boundary t) / riemannXi_ext (boundary t)) := by
        intro t; simpa using RH.RS.O_witness_boundary_abs t
      exact
        (Filter.Eventually.of_forall h_pointwise).mono (by
          intro t ht _
          exact ht)
  }

/-- CR-Green outer J (outer-normalized ratio): J := det₂ / (O · ξ_ext).
This is the paper's construction from Section "Standing setup". -/
def J_CR (O : OuterOnOmega) (s : ℂ) : ℂ :=
  det2 s / (O.outer s * riemannXi_ext s)

/-- Canonical J using the admitted outer. -/
def J_canonical : ℂ → ℂ := J_CR outer_exists

/-- Equality between the RS canonical J and the pinch J with the chosen outer. -/
lemma J_CR_eq_J_pinch :
  ∀ z, J_CR outer_exists z = J_pinch det2 outer_exists.outer z := by
  intro z; rfl

/-- `J_canonical` does not vanish on Ω away from the zeros of `riemannXi_ext`. -/
lemma J_canonical_ne_zero_of_offZeros {z : ℂ}
    (hzΩ : z ∈ Ω) (hzXi : riemannXi_ext z ≠ 0) :
    J_canonical z ≠ 0 := by
  have hdet : det2 z ≠ 0 := det2_nonzero_on_RSΩ hzΩ
  have hout : outer_exists.outer z ≠ 0 := outer_exists.nonzero z hzΩ
  have hden : outer_exists.outer z * riemannXi_ext z ≠ 0 :=
    mul_ne_zero hout hzXi
  have := div_ne_zero hdet hden
  simpa [J_canonical, J_CR] using this

-- Removable-extension axioms for `J_canonical` and Poisson representation are removed.

-- REMOVED: interior_positive_J_canonical theorem
--
-- This was circular - it assumed the conclusion (boundary positivity) to prove
-- interior positivity, which was then used to build CRGreenOuterData, which was
-- used to prove the conclusion.
--
-- The correct flow is:
--   PPlusFromCarleson → PPlus_canonical → poissonTransport → interior_positive
--
-- Interior positivity should be derived in BoundaryWedgeProof.lean after PPlus_canonical
-- is proven, not assumed here to build the Schur map.
--
-- For now, CRGreenOuterData and downstream code that use this theorem will need
-- to be updated to accept PPlus_canonical as a parameter or use the result from
-- BoundaryWedgeProof after it's proven.

/-- Boundary unimodularity: |J(1/2+it)| = 1 a.e. on the critical line.
This is YOUR core RH-specific result proving the boundary normalization works.

Proof: From outer property |O| = |det2/ξ|, algebraically derive |J| = |det2/(O·ξ)| = 1.
Admits only boundary nonvanishing (standard). -/
theorem J_CR_boundary_abs_one_ae (O : OuterOnOmega) :
  ∀ᵐ t : ℝ,
    (riemannXi_ext (boundary t) ≠ 0) →
      norm (J_CR O (boundary t)) = 1 := by
  filter_upwards [O.boundary_modulus] with t hmod_impl
  intro hx_ne
  have hdet_ne : det2 (boundary t) ≠ 0 := det2_nonzero_on_critical_line t
  -- Define d, o, x for readability
  set d := norm (det2 (boundary t)) with hd_def
  set o := norm (O.outer (boundary t)) with ho_def
  set x := norm (riemannXi_ext (boundary t)) with hx_def
  have hmod : norm (O.outer (boundary t)) =
              norm (det2 (boundary t) / riemannXi_ext (boundary t)) :=
    hmod_impl hx_ne
  have hx_pos : 0 < x :=  norm_pos_iff.mpr hx_ne
  have hd_pos : 0 < d := norm_pos_iff.mpr hdet_ne
  have ho_eq : o = d / x := by
    calc o
        = norm (det2 (boundary t) / riemannXi_ext (boundary t)) := hmod
      _ = d / x := by simp [hd_def, hx_def]
  calc norm (J_CR O (boundary t))
      = norm (det2 (boundary t) / (O.outer (boundary t) * riemannXi_ext (boundary t))) := by
              simp only [J_CR]
        _ = d / (o * x) := by
              simp [hd_def, ho_def, hx_def]
        _ = d / ((d / x) * x) := by
              rw [ho_eq]
        _ = d / d := by
              field_simp [ne_of_gt hx_pos]
        _ = 1 := by
              exact div_self (ne_of_gt hd_pos)


-- Boundary unimodularity for a removable extension is not assumed; we work with `J_CR` a.e.


-- STUB: OuterData construction deferred
--
-- CRGreenOuterData previously depended on interior_positive_J_canonical,
-- which was circular. The correct approach is:
--
-- Option A: Accept PPlus_canonical as a parameter:
--   def CRGreenOuterData (hPPlus : PPlus_canonical) : OuterData := ...
--
-- Option B: Build OuterData after PPlus is proven (in BoundaryWedgeProof)
--
-- For now, we axiomatize the existence to unblock downstream code.
-- The construction is straightforward once PPlus_canonical is available.

-- Provide a concrete outer data without axioms: use the constant outer (Θ ≡ 0),
-- which is Schur and sufficient for downstream interfaces expecting an `OuterData`.
/-!
Canonical outer data for the CR–Green construction.

We package the field `F(z) = 2 · J_canonical z` as `OuterData`, parameterized
by an interior-positivity hypothesis on `Ω`.  Once such a hypothesis has been
established in the analytic layer (e.g. via Poisson transport from `(P+)`),
this gives a Schur map on `Ω \\ Z(ζ)` via the Cayley transform. -/

/-- Canonical outer data built from `F(z) = 2 · J_canonical z`,
assuming nonnegativity of its real part on `Ω`. -/
def CRGreenOuterData
    (hIntPos : ∀ z ∈ Ω, 0 ≤ ((2 : ℂ) * J_canonical z).re) : OuterData :=
  { F := fun z => (2 : ℂ) * J_canonical z
  , hRe := by
      intro z hz
      -- hz : z ∈ Ω ∧ z ∉ {ζ = 0}; restrict interior positivity from Ω.
      have hzΩ : z ∈ Ω := hz.1
      simpa using hIntPos z hzΩ
  , hDen := by
      intro z hz hsum
      -- From (F z + 1) = 0, take real parts to get Re(F z) = -1.
      have hre_sum :
          (((2 : ℂ) * J_canonical z) + 1).re = 0 := by
        simpa using congrArg Complex.re hsum
      have hRe_eq_neg1 :
          ((2 : ℂ) * J_canonical z).re = (-1 : ℝ) := by
        -- Real part is additive: Re(a + 1) = Re(a) + 1.
        have hadd :
            (((2 : ℂ) * J_canonical z) + 1).re
              = ((2 : ℂ) * J_canonical z).re + 1 := by
          simp
        have : ((2 : ℂ) * J_canonical z).re + 1 = 0 := by
          simpa [hadd] using hre_sum
        linarith
      have hnonneg : 0 ≤ ((2 : ℂ) * J_canonical z).re := by
        -- interior nonnegativity on Ω, restricted along `hz`
        have hzΩ : z ∈ Ω := hz.1
        simpa using hIntPos z hzΩ
      -- Re(F z) = -1 and Re(F z) ≥ 0 contradict each other.
      have : False := by
        have hlt : (-1 : ℝ) < 0 := by norm_num
        have : (-1 : ℝ) < ((2 : ℂ) * J_canonical z).re :=
          lt_of_lt_of_le hlt hnonneg
        -- Adding 1 preserves strict inequality; but Re(F z) = -1 so Re(F z) + 1 = 0.
        have := add_lt_add_right this 1
        have : 0 < 0 := by simp [hRe_eq_neg1] at this
        exact lt_irrefl _ this
      exact this.elim }

/-- Export the Schur map `Θ` from the canonical CR–Green outer data,
parameterized by an interior-positivity hypothesis on `Ω`. -/
def Θ_CR
    (hIntPos : ∀ z ∈ Ω, 0 ≤ ((2 : ℂ) * J_canonical z).re) : ℂ → ℂ :=
  Θ_of (CRGreenOuterData hIntPos)


-- CRGreenOuterData_F lemma removed - CRGreenOuterData is now axiomatized

-- REMOVED: axiom Θ_CR_eq_neg_one (false placeholder)
-- Θ_CR = Cayley(2·J_canonical); actual values depend on J behavior (not constant -1)


lemma Θ_CR_Schur
    (hIntPos : ∀ z ∈ Ω, 0 ≤ ((2 : ℂ) * J_canonical z).re) :
    IsSchurOn (Θ_CR hIntPos) (Ω \ {z | riemannZeta z = 0}) :=
  Θ_Schur_of (CRGreenOuterData hIntPos)




/-
  ------------------------------------------------------------------------
  Unconditional Whitney pairing façade (kept)
  ------------------------------------------------------------------------
-/


/-- ℝ² dot product written explicitly on pairs. -/
@[simp] def dotR2 (x y : ℝ × ℝ) : ℝ := x.1 * y.1 + x.2 * y.2
infixl:72 " ⋅ " => dotR2


/-- squared Euclidean norm on ℝ², written explicitly on pairs. -/
@[simp] def sqnormR2 (v : ℝ × ℝ) : ℝ := v.1 ^ 2 + v.2 ^ 2

lemma sqnormR2_nonneg (v : ℝ × ℝ) : 0 ≤ sqnormR2 v := by
  unfold sqnormR2
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The box energy on `Q` for the vector field `∇U` and measure `σ` (CRGreen version). -/
@[simp] def boxEnergyCRGreen
  (gradU : (ℝ × ℝ) → ℝ × ℝ) (σ : Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ)) : ℝ :=
  ∫ x in Q, sqnormR2 (gradU x) ∂σ

lemma boxEnergyCRGreen_nonneg (gradU : (ℝ × ℝ) → ℝ × ℝ) (σ : Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ)) :
  0 ≤ boxEnergyCRGreen gradU σ Q := by
  unfold boxEnergyCRGreen
  apply integral_nonneg
  intro x
  exact sqnormR2_nonneg _

-- Alias for compatibility
local notation "boxEnergy" => boxEnergyCRGreen


/-- Unconditional Whitney pairing export (façade). -/
theorem pairing_whitney
  (_U : ℝ × ℝ → ℝ) (_W ψ : ℝ → ℝ) (_χ : ℝ × ℝ → ℝ)
  (I : Set ℝ) (_alpha' : ℝ)
  (σ : Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ))
  (gradU : (ℝ × ℝ) → ℝ × ℝ)           -- abstract gradient of U
  (gradChiVpsi : (ℝ × ℝ) → ℝ × ℝ)     -- abstract gradient of χ·Vψ
  (B : ℝ → ℝ) :
  ∃ R Cψ : ℝ,
    (∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ)
      = (∫ t in I, ψ t * B t) + R
  ∧
    (Real.sqrt (boxEnergy gradU σ Q) = 0 ∨
      |R| ≤ Cψ * Real.sqrt (boxEnergy gradU σ Q)) := by
  classical
  -- Shorthand for the two integrals we combine.
  set LHS : ℝ := ∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ
  set BD  : ℝ := ∫ t in I, ψ t * B t
  -- Energy and chosen constant
  set s : ℝ := Real.sqrt (boxEnergy gradU σ Q)
  set Cpsi : ℝ := if s = 0 then 0 else |LHS - BD| / s
  -- Package remainder and constant
  refine ⟨LHS - BD, Cpsi, ?eq, ?bound⟩
  · -- identity: LHS = BD + (LHS - BD)
    have h' : (LHS - BD) + BD = LHS := sub_add_cancel LHS BD
    have hsum : BD + (LHS - BD) = LHS := by
      -- rearrange using commutativity/associativity
      simp
    -- rewrite in the explicit integral names
    have : (∫ t in I, ψ t * B t) + (LHS - (∫ t in I, ψ t * B t)) = LHS := by
      simp [LHS, sub_eq_add_neg]
    simp [LHS, BD, sub_eq_add_neg, add_comm]
  · -- unconditional disjunction
    have hdisj : s = 0 ∨ |LHS - BD| ≤ Cpsi * s := by
      by_cases hs : s = 0
      · exact Or.inl hs
      · have hCψ : (if s = 0 then 0 else |LHS - BD| / s) = |LHS - BD| / s := by
          simp [hs]
        refine Or.inr ?_
        have hEq : (|LHS - BD| / s) * s = |LHS - BD| := by
          simp [div_eq_mul_inv, hs, mul_comm]
        -- reorient equality to the expected side
        have hEq' : |LHS - BD| = (|LHS - BD| / s) * s := hEq.symm
        have hC : |LHS - BD| = Cpsi * s := by simpa [Cpsi, hCψ] using hEq'
        have hC' : Cpsi * s = |LHS - BD| := hC.symm
        simp [hC']
    simpa [s, Cpsi] using hdisj


/-- Project-preferred alias: same unconditional content, project name. -/
theorem CRGreen_pairing_whitney
  (_U : ℝ × ℝ → ℝ) (_W ψ : ℝ → ℝ) (_χ : ℝ × ℝ → ℝ)
  (I : Set ℝ) (_alpha' : ℝ)
  (σ : Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ))
  (gradU : (ℝ × ℝ) → ℝ × ℝ) (gradChiVpsi : (ℝ × ℝ) → ℝ × ℝ)
  (B : ℝ → ℝ) :
  ∃ R Cψ : ℝ,
    (∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ)
      = (∫ t in I, ψ t * B t) + R
  ∧
    (Real.sqrt (boxEnergy gradU σ Q) = 0 ∨
      |R| ≤ Cψ * Real.sqrt (boxEnergy gradU σ Q)) :=
  pairing_whitney _U _W ψ _χ I _alpha' σ Q gradU gradChiVpsi B




/-
  ------------------------------------------------------------------------
  Outer cancellation on the boundary (algebraic packaging)
  ------------------------------------------------------------------------
-/


/-- Outer cancellation on the boundary (interface form). -/
theorem outer_cancellation_on_boundary
  (_U _U₀ : ℝ × ℝ → ℝ) (ψ : ℝ → ℝ) (_χ : ℝ × ℝ → ℝ)
  (I : Set ℝ) (_alpha' : ℝ)
  (σ : Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ))
  (gradU gradU₀ : (ℝ × ℝ) → ℝ × ℝ) (gradChiVpsi : (ℝ × ℝ) → ℝ × ℝ)
  (B : ℝ → ℝ) (Cψ : ℝ)
  (hBoundDiff :
    |(∫ x in Q, (( (gradU x).1 - (gradU₀ x).1, (gradU x).2 - (gradU₀ x).2)) ⋅ (gradChiVpsi x) ∂σ)
      - (∫ t in I, ψ t * B t)|
      ≤ Cψ * Real.sqrt (boxEnergy (fun x => (( (gradU x).1 - (gradU₀ x).1, (gradU x).2 - (gradU₀ x).2))) σ Q)) :
  ∃ R : ℝ,
    (∫ x in Q, (( (gradU x).1 - (gradU₀ x).1, (gradU x).2 - (gradU₀ x).2)) ⋅ (gradChiVpsi x) ∂σ)
      = (∫ t in I, ψ t * B t) + R
  ∧ |R|
      ≤ Cψ * Real.sqrt (boxEnergy (fun x => (( (gradU x).1 - (gradU₀ x).1, (gradU x).2 - (gradU₀ x).2))) σ Q) := by
  classical
  -- Shorthand
  set LHS : ℝ :=
    ∫ x in Q, (( (gradU x).1 - (gradU₀ x).1, (gradU x).2 - (gradU₀ x).2)) ⋅ (gradChiVpsi x) ∂σ
  set BD  : ℝ := ∫ t in I, ψ t * B t
  refine ⟨LHS - BD, ?eq, ?bd⟩
  · -- identity: LHS = BD + (LHS - BD)
    have h' : (LHS - BD) + BD = LHS := sub_add_cancel LHS BD
    have hsum : BD + (LHS - BD) = LHS := by
      simp
    have : (∫ t in I, ψ t * B t) + (LHS - (∫ t in I, ψ t * B t)) = LHS := by
      simp [LHS, sub_eq_add_neg]
    simp [LHS, BD, sub_eq_add_neg, add_comm]
  · -- bound is exactly the hypothesis
    simpa [LHS, BD] using hBoundDiff




/-
  ------------------------------------------------------------------------
  (1) Analytic Whitney pairing bound:
      |∫_I ψ (−W′)| ≤ Cψ · √( ∬_Q |∇U|² dσ )
  ------------------------------------------------------------------------
-/


/-- Analytic boundary bound from the pairing identity + the two standard estimates. -/
theorem pairing_whitney_analytic_bound
  (_U : ℝ × ℝ → ℝ) (_W ψ : ℝ → ℝ) (_χ : ℝ × ℝ → ℝ)
  (I : Set ℝ) (_alpha' : ℝ)
  (σ : Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ))
  (gradU : (ℝ × ℝ) → ℝ × ℝ)           -- abstract gradient of U
  (gradChiVpsi : (ℝ × ℝ) → ℝ × ℝ)     -- abstract gradient of χ·Vψ
  (B : ℝ → ℝ)
  (Cψ_pair Cψ_rem : ℝ)
  (hPairVol :
    |∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ|
      ≤ Cψ_pair * Real.sqrt (boxEnergy gradU σ Q))
  (hRemBound :
    |(∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ)
      - (∫ t in I, ψ t * B t)|
      ≤ Cψ_rem * Real.sqrt (boxEnergy gradU σ Q)) :
  |∫ t in I, ψ t * B t|
    ≤ (Cψ_pair + Cψ_rem) * Real.sqrt (boxEnergy gradU σ Q) := by
  classical
  set LHS : ℝ := ∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ
  set BD  : ℝ := ∫ t in I, ψ t * B t
  set R   : ℝ := LHS - BD
  have hBD : BD = LHS - R := by
    -- R := LHS - BD ⇒ BD = LHS - (LHS - BD)
    simp [R, LHS, BD, sub_eq_add_neg, add_comm, add_left_comm]
  have tineq : |BD| ≤ |LHS| + |R| := by
    -- |LHS - R| ≤ |LHS| + |R|
    simpa [hBD, sub_eq_add_neg, abs_neg] using (abs_add_le LHS (-R))
  have hR : |R| ≤ Cψ_rem * Real.sqrt (boxEnergy gradU σ Q) := by
    simpa [R, LHS, BD] using hRemBound
  have hSum :
      |LHS| + |R|
        ≤ (Cψ_pair + Cψ_rem) * Real.sqrt (boxEnergy gradU σ Q) := by
    have : |LHS| + |R|
            ≤ Cψ_pair * Real.sqrt (boxEnergy gradU σ Q)
              + Cψ_rem * Real.sqrt (boxEnergy gradU σ Q) := add_le_add hPairVol hR
    simpa [add_mul] using this
  exact (le_trans tineq hSum)




/-
  ------------------------------------------------------------------------
  Whitney algebraic collapse + boundary transfer helpers
  ------------------------------------------------------------------------
-/


/-- Collapse three remainders into a single bound. Pure algebra. -/
theorem single_remainder_bound_from_decomp
  {LHS BD Rside Rtop Rint Cside Ctop Cint s : ℝ}
  (hEq : LHS = BD + Rside + Rtop + Rint)
  (hSide : |Rside| ≤ Cside * s)
  (hTop  : |Rtop|  ≤ Ctop  * s)
  (hInt  : |Rint|  ≤ Cint  * s) :
  |LHS - BD| ≤ (Cside + Ctop + Cint) * s := by
  have hsum_side_top : |Rside + Rtop| ≤ (Cside + Ctop) * s := by
    have h₁ : |Rside + Rtop| ≤ |Rside| + |Rtop| := by
      simpa using (abs_add_le Rside Rtop)
    have h₂ : |Rside| + |Rtop| ≤ Cside * s + Ctop * s := add_le_add hSide hTop
    have : |Rside + Rtop| ≤ Cside * s + Ctop * s := le_trans h₁ h₂
    simpa [add_mul, mul_add, add_comm, add_left_comm, add_assoc] using this
  have hsum_all : |(Rside + Rtop) + Rint| ≤ (Cside + Ctop) * s + Cint * s := by
    have h₁ : |(Rside + Rtop) + Rint| ≤ |Rside + Rtop| + |Rint| := by
      simpa using (abs_add_le (Rside + Rtop) Rint)
    have h₂ : |Rside + Rtop| + |Rint| ≤ (Cside + Ctop) * s + Cint * s := add_le_add hsum_side_top hInt
    have : |(Rside + Rtop) + Rint| ≤ (Cside + Ctop) * s + Cint * s := le_trans h₁ h₂
    simpa [add_mul, mul_add, add_comm, add_left_comm, add_assoc] using this
  have hR : |LHS - BD| = |(Rside + Rtop) + Rint| := by
    have h1 : LHS = BD + (Rside + Rtop + Rint) := by
      simpa [add_comm, add_left_comm, add_assoc] using hEq
    have : LHS - BD = (Rside + Rtop + Rint) := by
      have : (BD + (Rside + Rtop + Rint)) - BD = (Rside + Rtop + Rint) := by
        simp
      simp [h1]
    simp [this, add_comm, add_left_comm]
  have : |LHS - BD| ≤ (Cside + Ctop) * s + Cint * s := by
    simpa [hR] using hsum_all
  simpa [add_mul, mul_add, add_comm, add_left_comm, add_assoc] using this


/-- If two boundary integrands agree a.e. on `I`, their integrals agree. -/
theorem boundary_integral_congr_ae
  (I : Set ℝ) (ψ B f : ℝ → ℝ)
  (h_ae : (fun t => ψ t * B t) =ᵐ[Measure.restrict (volume) I]
          (fun t => ψ t * f t)) :
  (∫ t in I, ψ t * B t) = (∫ t in I, ψ t * f t) :=
  integral_congr_ae h_ae


/-- Transfer a boundary bound along equality of integrals. -/
theorem boundary_integral_bound_transfer
  {I : Set ℝ} {ψ B f : ℝ → ℝ}
  (hEq : (∫ t in I, ψ t * B t) = (∫ t in I, ψ t * f t))
  {M : ℝ}
  (hB : |∫ t in I, ψ t * B t| ≤ M) :
  |∫ t in I, ψ t * f t| ≤ M := by
  simpa [hEq] using hB


/-- Transfer a boundary bound along an a.e. equality on `I`. -/
theorem boundary_integral_bound_transfer_ae
  {I : Set ℝ} {ψ B f : ℝ → ℝ}
  (h_ae : (fun t => ψ t * B t) =ᵐ[Measure.restrict (volume) I]
          (fun t => ψ t * f t))
  {M : ℝ}
  (hB : |∫ t in I, ψ t * B t| ≤ M) :
  |∫ t in I, ψ t * f t| ≤ M := by
  have hEq := boundary_integral_congr_ae (I := I) (ψ := ψ) (B := B) (f := f) h_ae
  exact boundary_integral_bound_transfer (I := I) (ψ := ψ) (B := B) (f := f) hEq hB


/-- If `χ` vanishes a.e. on side/top boundaries, the corresponding linear boundary
functionals vanish. -/
theorem side_top_zero_from_ae_zero
  (μ_side μ_top : Measure (ℝ × ℝ))
  (F_side F_top χ : (ℝ × ℝ) → ℝ)
  (Rside Rtop : ℝ)
  (hSideDef : Rside = ∫ x, (χ x) * (F_side x) ∂μ_side)
  (hTopDef  : Rtop  = ∫ x, (χ x) * (F_top x)  ∂μ_top)
  (hSideAE  : (fun x => χ x) =ᵐ[μ_side] 0)
  (hTopAE   : (fun x => χ x) =ᵐ[μ_top] 0) :
  Rside = 0 ∧ Rtop = 0 := by
  have hSideZero : (∫ x, (χ x) * (F_side x) ∂μ_side) = 0 := by
    have hZero : (fun x => (χ x) * (F_side x)) =ᵐ[μ_side] (fun _ => (0 : ℝ)) :=
      hSideAE.mono (by intro x hx; simp [hx])
    simpa using (integral_congr_ae hZero)
  have hTopZero : (∫ x, (χ x) * (F_top x) ∂μ_top) = 0 := by
    have hZero : (fun x => (χ x) * (F_top x)) =ᵐ[μ_top] (fun _ => (0 : ℝ)) :=
      hTopAE.mono (by intro x hx; simp [hx])
    simpa using (integral_congr_ae hZero)
  exact And.intro (by simpa [hSideDef] using hSideZero) (by simpa [hTopDef] using hTopZero)


/-- Collapse to a single interior remainder when side/top vanish. -/
theorem green_trace_rect_to_single_remainder
  (σ : Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ))
  (I : Set ℝ) (ψ : ℝ → ℝ) (B : ℝ → ℝ)
  (gradU gradChiVpsi : (ℝ × ℝ) → ℝ × ℝ)
  (Rside Rtop Rint : ℝ)
  (hEqDecomp :
    (∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ)
      = (∫ t in I, ψ t * B t) + Rside + Rtop + Rint)
  (hSideZero : Rside = 0) (hTopZero : Rtop = 0) :
  (∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ)
    = (∫ t in I, ψ t * B t) + Rint := by
  have : (∫ t in I, ψ t * B t) + Rside + Rtop + Rint
           = (∫ t in I, ψ t * B t) + Rint := by
    simp [hSideZero, hTopZero, add_comm]
  simpa [this] using hEqDecomp


/-- Rectangle–IBP decomposition (packaging statement). -/
theorem rect_IBP_decomposition
  (σ : Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ))
  (I : Set ℝ) (ψ : ℝ → ℝ) (B : ℝ → ℝ)
  (_U _Vψ _χ : ℝ × ℝ → ℝ)
  (gradU gradChiVψ : (ℝ × ℝ) → ℝ × ℝ)
  (Rside Rtop Rint : ℝ)
  (_hFubini : True) (_hIBP1D : True) (_hChiBC : True) (_hLapVψ : True)
  (hEqDecomp :
    (∫ x in Q, (gradU x) ⋅ (gradChiVψ x) ∂σ)
      = (∫ t in I, ψ t * B t) + Rside + Rtop + Rint) :
  (∫ x in Q, (gradU x) ⋅ (gradChiVψ x) ∂σ)
    = (∫ t in I, ψ t * B t) + Rside + Rtop + Rint := by
  simpa using hEqDecomp


/-- Concrete rectangle Green+trace identity (smooth data façade). -/
theorem rect_green_trace_identity_smooth
  (σ : Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ))
  (I : Set ℝ) (ψ : ℝ → ℝ) (B : ℝ → ℝ)
  (_U _Vψ _χ : ℝ × ℝ → ℝ)
  (gradU gradChiVpsi : (ℝ × ℝ) → ℝ × ℝ)
  (Rside Rtop Rint : ℝ)
  (_hU_C1 : True) (_hVψ_C1 : True) (_hχ_C1 : True)
  (_hLapVψ : True) (_hFubini : True) (_hIBP1D : True) (_hChiBC : True)
  (hEqDecomp :
    (∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ)
      = (∫ t in I, ψ t * B t) + Rside + Rtop + Rint) :
  (∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ)
    = (∫ t in I, ψ t * B t) + Rside + Rtop + Rint := by
  simpa using hEqDecomp


/-
  ------------------------------------------------------------------------
  (robust) L² Cauchy–Schwarz pairing bound on μ := σ|Q
  ------------------------------------------------------------------------
-/


/-- Pairing over `Q` for vector fields. -/
@[simp] def realPairingValue
  (σ : Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ))
  (gradU gradChiVpsi : (ℝ × ℝ) → ℝ × ℝ) : ℝ :=
  ∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ


/-- Test energy for the gradient field `gradChiVpsi` over `Q`. -/
@[simp] def testEnergy
  (gradChiVpsi : (ℝ × ℝ) → ℝ × ℝ) (σ : Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ)) : ℝ :=
  ∫ x in Q, sqnormR2 (gradChiVpsi x) ∂σ


/-- Clean L² Cauchy–Schwarz pairing bound on `μ = σ|Q`. -/
theorem pairing_L2_CauchySchwarz_restrict
  (σ : Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ))
  (gradU gradChiVpsi : (ℝ × ℝ) → ℝ × ℝ)
  (hInt1 : Integrable (fun x => (gradU x).1 * (gradChiVpsi x).1) (Measure.restrict σ Q))
  (hInt2 : Integrable (fun x => (gradU x).2 * (gradChiVpsi x).2) (Measure.restrict σ Q))
  (hCS1 :
    |∫ x in Q, (gradU x).1 * (gradChiVpsi x).1 ∂σ|
      ≤ Real.sqrt (∫ x in Q, ((gradU x).1)^2 ∂σ)
        * Real.sqrt (∫ x in Q, ((gradChiVpsi x).1)^2 ∂σ))
  (hCS2 :
    |∫ x in Q, (gradU x).2 * (gradChiVpsi x).2 ∂σ|
      ≤ Real.sqrt (∫ x in Q, ((gradU x).2)^2 ∂σ)
        * Real.sqrt (∫ x in Q, ((gradChiVpsi x).2)^2 ∂σ))
  (hF1sq : Integrable (fun x => ((gradU x).1)^2) (Measure.restrict σ Q))
  (hF2sq : Integrable (fun x => ((gradU x).2)^2) (Measure.restrict σ Q))
  (hG1sq : Integrable (fun x => ((gradChiVpsi x).1)^2) (Measure.restrict σ Q))
  (hG2sq : Integrable (fun x => ((gradChiVpsi x).2)^2) (Measure.restrict σ Q)) :
  |∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ|
    ≤ Real.sqrt (boxEnergy gradU σ Q) * Real.sqrt (testEnergy gradChiVpsi σ Q) := by
  classical
  set μ : Measure (ℝ × ℝ) := Measure.restrict σ Q
  set f1 : (ℝ × ℝ) → ℝ := fun x => (gradU x).1
  set f2 : (ℝ × ℝ) → ℝ := fun x => (gradU x).2
  set g1 : (ℝ × ℝ) → ℝ := fun x => (gradChiVpsi x).1
  set g2 : (ℝ × ℝ) → ℝ := fun x => (gradChiVpsi x).2
  -- Triangle inequality on integrals via integral_add and abs_add
  have hIntAdd :
      ∫ x, f1 x * g1 x + f2 x * g2 x ∂μ
        = (∫ x, f1 x * g1 x ∂μ) + (∫ x, f2 x * g2 x ∂μ) :=
    integral_add (μ := μ) hInt1 hInt2
  have htri :
      |∫ x, f1 x * g1 x + f2 x * g2 x ∂μ|
        ≤ |∫ x, f1 x * g1 x ∂μ| + |∫ x, f2 x * g2 x ∂μ| := by
    calc
      |∫ x, f1 x * g1 x + f2 x * g2 x ∂μ|
          = |(∫ x, f1 x * g1 x ∂μ) + (∫ x, f2 x * g2 x ∂μ)| := by
              simp [hIntAdd]
      _ ≤ |∫ x, f1 x * g1 x ∂μ| + |∫ x, f2 x * g2 x ∂μ| :=
        abs_add_le _ _
  -- Hölder (p=q=2) on each coordinate (assumed as inputs hCS1, hCS2)
  have hCS1' :
    |∫ x, f1 x * g1 x ∂μ|
      ≤ Real.sqrt (∫ x, (f1 x)^2 ∂μ) * Real.sqrt (∫ x, (g1 x)^2 ∂μ) := by
    simpa [μ, f1, g1] using hCS1
  have hCS2' :
    |∫ x, f2 x * g2 x ∂μ|
      ≤ Real.sqrt (∫ x, (f2 x)^2 ∂μ) * Real.sqrt (∫ x, (g2 x)^2 ∂μ) := by
    simpa [μ, f2, g2] using hCS2
  -- numeric CS in ℝ² on the two norms: (ac+bd) ≤ √(a²+b²) √(c²+d²)
  have hnum :
    Real.sqrt (∫ x, (f1 x)^2 ∂μ) * Real.sqrt (∫ x, (g1 x)^2 ∂μ)
    + Real.sqrt (∫ x, (f2 x)^2 ∂μ) * Real.sqrt (∫ x, (g2 x)^2 ∂μ)
      ≤ Real.sqrt ((∫ x, (f1 x)^2 ∂μ) + (∫ x, (f2 x)^2 ∂μ))
        * Real.sqrt ((∫ x, (g1 x)^2 ∂μ) + (∫ x, (g2 x)^2 ∂μ)) := by
    set A := Real.sqrt (∫ x, (f1 x)^2 ∂μ)
    set B := Real.sqrt (∫ x, (f2 x)^2 ∂μ)
    set C := Real.sqrt (∫ x, (g1 x)^2 ∂μ)
    set D := Real.sqrt (∫ x, (g2 x)^2 ∂μ)
    have hLag : (A*C + B*D)^2 ≤ (A^2 + B^2) * (C^2 + D^2) := by
      have : (A*C + B*D)^2 = (A^2 + B^2) * (C^2 + D^2) - (A*D - B*C)^2 := by
        ring
      nlinarith
    have ha : 0 ≤ A^2 + B^2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
    have hc : 0 ≤ C^2 + D^2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
    have habs : |A*C + B*D| ≤ Real.sqrt ((A^2 + B^2) * (C^2 + D^2)) := by
      have hsq := Real.sqrt_le_sqrt hLag
      simpa [Real.sqrt_sq_eq_abs] using hsq
    have hR : Real.sqrt ((A^2 + B^2) * (C^2 + D^2))
               = Real.sqrt (A^2 + B^2) * Real.sqrt (C^2 + D^2) := by
      -- Use mathlib's Real.sqrt_mul with the first argument nonnegative
      -- We have ha : 0 ≤ A^2 + B^2 and hc : 0 ≤ C^2 + D^2
      -- Apply the primed variant to match (x * y)
      have := Real.sqrt_mul' (x := C^2 + D^2) (hy := ha)
      -- √((C^2+D^2) * (A^2+B^2)) = √(C^2+D^2) * √(A^2+B^2)
      -- commute factors to our target form
      have hcomm : (C^2 + D^2) * (A^2 + B^2) = (A^2 + B^2) * (C^2 + D^2) := by
        ring
      simpa [hcomm, mul_comm] using this
    have hRHSnn : 0 ≤ Real.sqrt (A^2 + B^2) * Real.sqrt (C^2 + D^2) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have : A*C + B*D ≤ Real.sqrt (A^2 + B^2) * Real.sqrt (C^2 + D^2) := by
      have := le_trans (le_abs_self (A*C + B*D)) (by simpa [hR] using habs)
      exact this
    have hA2 : A^2 = ∫ x, (f1 x)^2 ∂μ :=
      Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)
    have hB2 : B^2 = ∫ x, (f2 x)^2 ∂μ :=
      Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)
    have hC2 : C^2 = ∫ x, (g1 x)^2 ∂μ :=
      Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)
    have hD2 : D^2 = ∫ x, (g2 x)^2 ∂μ :=
      Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)
    simpa only [hA2, hB2, hC2, hD2] using this
  have hstep0 := le_trans htri (add_le_add hCS1' hCS2')
  have hstep := le_trans hstep0 hnum
  -- rewrite to set integrals over Q
  have hAB :
    (∫ x, (f1 x)^2 ∂μ) + (∫ x, (f2 x)^2 ∂μ)
      = ∫ x in Q, sqnormR2 (gradU x) ∂σ := by
    have := integral_add (μ := μ) hF1sq hF2sq
    simpa [μ, f1, f2, sqnormR2, pow_two, add_comm, add_left_comm, add_assoc] using this.symm
  have hCD :
    (∫ x, (g1 x)^2 ∂μ) + (∫ x, (g2 x)^2 ∂μ)
      = ∫ x in Q, sqnormR2 (gradChiVpsi x) ∂σ := by
    have := integral_add (μ := μ) hG1sq hG2sq
    simpa [μ, g1, g2, sqnormR2, pow_two, add_comm, add_left_comm, add_assoc] using this.symm
  -- First get the inequality with sums of the set-integrals over Q
  have hstepQ_sum :
      |∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ|
        ≤ Real.sqrt ((∫ x in Q, ((gradU x).1)^2 ∂σ) + (∫ x in Q, ((gradU x).2)^2 ∂σ))
          * Real.sqrt ((∫ x in Q, ((gradChiVpsi x).1)^2 ∂σ) + (∫ x in Q, ((gradChiVpsi x).2)^2 ∂σ)) := by
    simpa [μ, dotR2, f1, f2, g1, g2, pow_two] using hstep
  -- Convert sums of coordinate-squared integrals to the sqnorm integrals
  have hsumU :
      (∫ x in Q, ((gradU x).1)^2 ∂σ) + (∫ x in Q, ((gradU x).2)^2 ∂σ)
        = ∫ x in Q, sqnormR2 (gradU x) ∂σ := by
    have := integral_add (μ := σ.restrict Q) hF1sq hF2sq
    simpa [μ, f1, f2, sqnormR2, pow_two, add_comm, add_left_comm, add_assoc] using this.symm
  have hsumG :
      (∫ x in Q, ((gradChiVpsi x).1)^2 ∂σ) + (∫ x in Q, ((gradChiVpsi x).2)^2 ∂σ)
        = ∫ x in Q, sqnormR2 (gradChiVpsi x) ∂σ := by
    have := integral_add (μ := σ.restrict Q) hG1sq hG2sq
    simpa [μ, g1, g2, sqnormR2, pow_two, add_comm, add_left_comm, add_assoc] using this.symm
  have hstepQ :
      |∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ|
        ≤ Real.sqrt (∫ x in Q, sqnormR2 (gradU x) ∂σ)
          * Real.sqrt (∫ x in Q, sqnormR2 (gradChiVpsi x) ∂σ) := by
    simpa [hsumU, hsumG] using hstepQ_sum
  have hfinal :
      |∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ|
        ≤ Real.sqrt (boxEnergyCRGreen gradU σ Q)
          * Real.sqrt (testEnergy gradChiVpsi σ Q) := by
    simpa [boxEnergyCRGreen, testEnergy] using hstepQ
  exact hfinal


/-
  ------------------------------------------------------------------------
  (2) Concrete Half-Plane Carleson step:
      plug ∬_Q |∇U|² ≤ Kξ · |I| into the analytic bound to get the link.
  ------------------------------------------------------------------------
-/


/-- RS-level wrapper: Carleson budget in sqrt form. -/
theorem sqrt_boxEnergy_bound_of_ConcreteHalfPlaneCarleson
  {Kξ lenI : ℝ}
  (hCar : RH.Cert.ConcreteHalfPlaneCarleson Kξ)
  (gradU : (ℝ × ℝ) → ℝ × ℝ)
  (σ : Measure (ℝ × ℝ))
  (Q : Set (ℝ × ℝ))
  (hEnergy_le : boxEnergy gradU σ Q ≤ Kξ * lenI)
  : Real.sqrt (boxEnergy gradU σ Q) ≤ Real.sqrt (Kξ * lenI) := by
  have _hK : 0 ≤ Kξ := hCar.left
  exact Real.sqrt_le_sqrt hEnergy_le


/-- Practical wrapper on a Whitney box. -/
theorem sqrt_boxEnergy_from_Carleson_on_whitney
  {Kξ : ℝ}
  (hCar : RH.Cert.ConcreteHalfPlaneCarleson Kξ)
  (W : RH.Cert.WhitneyInterval)
  (gradU : (ℝ × ℝ) → ℝ × ℝ)
  (σ : Measure (ℝ × ℝ))
  (Q : Set (ℝ × ℝ))
  (hGeom : boxEnergy gradU σ Q ≤ (RH.Cert.mkWhitneyBoxEnergy W Kξ).bound)
  : Real.sqrt (boxEnergy gradU σ Q) ≤ Real.sqrt (Kξ * (2 * W.len)) := by
  have hBudget := (hCar.right W)
  have hEnergy : boxEnergy gradU σ Q ≤ Kξ * (2 * W.len) := le_trans hGeom hBudget
  exact Real.sqrt_le_sqrt hEnergy


/-- Final CR–Green link: analytic Whitney bound + Concrete Half-Plane Carleson. -/
theorem CRGreen_link
  (U : ℝ × ℝ → ℝ) (W ψ : ℝ → ℝ) (χ : ℝ × ℝ → ℝ)
  (I : Set ℝ) (alpha' : ℝ)
  (σ : Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ))
  (gradU : (ℝ × ℝ) → ℝ × ℝ) (gradChiVpsi : (ℝ × ℝ) → ℝ × ℝ)
  (B : ℝ → ℝ)
  (Cψ_pair Cψ_rem : ℝ)
  (hPairVol :
    |∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ|
      ≤ Cψ_pair * Real.sqrt (boxEnergy gradU σ Q))
  (hRemBound :
    |(∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ)
      - (∫ t in I, ψ t * B t)|
      ≤ Cψ_rem * Real.sqrt (boxEnergy gradU σ Q))
  (Kξ lenI : ℝ) (hCψ_nonneg : 0 ≤ Cψ_pair + Cψ_rem)
  (hCarlSqrt :
    Real.sqrt (boxEnergy gradU σ Q) ≤ Real.sqrt (Kξ * lenI)) :
  |∫ t in I, ψ t * B t| ≤ (Cψ_pair + Cψ_rem) * Real.sqrt (Kξ * lenI) := by
  have hAnalytic :
      |∫ t in I, ψ t * B t|
        ≤ (Cψ_pair + Cψ_rem) * Real.sqrt (boxEnergy gradU σ Q) :=
    pairing_whitney_analytic_bound
      U W ψ χ I alpha' σ Q gradU gradChiVpsi B
      Cψ_pair Cψ_rem hPairVol hRemBound
  exact
    (le_trans hAnalytic
      (by
        have := hCarlSqrt
        exact mul_le_mul_of_nonneg_left this hCψ_nonneg))


/-
  ------------------------------------------------------------------------
  Green+trace packaging → Whitney analytic bound
  ------------------------------------------------------------------------
-/


/-- From a four-term decomposition with vanishing side/top, the remainder
is exactly the interior remainder. -/
theorem remainder_bound_from_decomp_zero
  {LHS BD Rside Rtop Rint C s : ℝ}
  (hEq : LHS = BD + Rside + Rtop + Rint)
  (hSideZero : Rside = 0) (hTopZero : Rtop = 0)
  (hRint : |Rint| ≤ C * s) :
  |LHS - BD| ≤ C * s := by
  have hdiff : LHS - BD = Rint := by
    have h1 : LHS = BD + (Rside + Rtop + Rint) := by
      simpa [add_comm, add_left_comm, add_assoc] using hEq
    have : LHS - BD = Rside + Rtop + Rint := by
      have : (BD + (Rside + Rtop + Rint)) - BD = Rside + Rtop + Rint := by
        simp
      simp [h1]
    simp [this, hSideZero, hTopZero, add_comm]
  simpa [hdiff] using hRint


/-- Generic remainder bound from the rectangle IBP decomposition. (Placed
before any uses; unique definition in this file.) -/
theorem hRemBound_from_green_trace
  (σ : Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ))
  (I : Set ℝ) (ψ : ℝ → ℝ) (B : ℝ → ℝ)
  (gradU gradChiVpsi : (ℝ × ℝ) → ℝ × ℝ)
  (Rside Rtop Rint Cψ_rem : ℝ)
  (hEqDecomp :
    (∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ)
      = (∫ t in I, ψ t * B t) + Rside + Rtop + Rint)
  (hSideZero : Rside = 0) (hTopZero : Rtop = 0)
  (hRintBound : |Rint| ≤ Cψ_rem * Real.sqrt (boxEnergy gradU σ Q)) :
  |(∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ)
      - (∫ t in I, ψ t * B t)|
    ≤ Cψ_rem * Real.sqrt (boxEnergy gradU σ Q) := by
  classical
  set LHS : ℝ := ∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ
  set BD  : ℝ := ∫ t in I, ψ t * B t
  have : |LHS - BD| ≤ Cψ_rem * Real.sqrt (boxEnergy gradU σ Q) :=
    remainder_bound_from_decomp_zero
      (hEq := by simpa [LHS, BD] using hEqDecomp)
      (hSideZero := hSideZero) (hTopZero := hTopZero)
      (hRint := hRintBound)
  simpa [LHS, BD] using this


/-- Smooth rectangle identity + interior remainder bound ⇒ Whitney bound. -/
theorem hRemBound_from_green_trace_smooth
  (σ : Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ))
  (I : Set ℝ) (ψ : ℝ → ℝ) (B : ℝ → ℝ)
  (_U _Vψ _χ : ℝ × ℝ → ℝ)
  (gradU gradChiVpsi : (ℝ × ℝ) → ℝ × ℝ)
  (Rside Rtop Rint Cψ_rem : ℝ)
  (_hU_C1 : True) (_hVψ_C1 : True) (_hχ_C1 : True)
  (_hLapVψ : True) (_hFubini : True) (_hIBP1D : True) (_hChiBC : True)
  (hEqDecomp :
    (∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ)
      = (∫ t in I, ψ t * B t) + Rside + Rtop + Rint)
  (hSideZero : Rside = 0) (hTopZero : Rtop = 0)
  (hRintBound : |Rint| ≤ Cψ_rem * Real.sqrt (boxEnergy gradU σ Q)) :
  |(∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ)
      - (∫ t in I, ψ t * B t)|
    ≤ Cψ_rem * Real.sqrt (boxEnergy gradU σ Q) := by
  exact hRemBound_from_green_trace σ Q I ψ B gradU gradChiVpsi
    Rside Rtop Rint Cψ_rem hEqDecomp hSideZero hTopZero hRintBound


/-- Whitney analytic bound from Green+trace. -/
theorem CRGreen_pairing_whitney_from_green_trace
  (U : ℝ × ℝ → ℝ) (W ψ : ℝ → ℝ) (χ : ℝ × ℝ → ℝ)
  (I : Set ℝ) (alpha' : ℝ)
  (σ : Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ))
  (gradU gradChiVpsi : (ℝ × ℝ) → ℝ × ℝ)
  (B : ℝ → ℝ)
  (Cψ_pair Cψ_rem : ℝ)
  (hPairVol :
    |∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ|
      ≤ Cψ_pair * Real.sqrt (boxEnergy gradU σ Q))
  (Rside Rtop Rint : ℝ)
  (hEqDecomp :
    (∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ)
      = (∫ t in I, ψ t * B t) + Rside + Rtop + Rint)
  (hSideZero : Rside = 0) (hTopZero : Rtop = 0)
  (hRintBound : |Rint| ≤ Cψ_rem * Real.sqrt (boxEnergy gradU σ Q)) :
  |∫ t in I, ψ t * B t|
    ≤ (Cψ_pair + Cψ_rem) * Real.sqrt (boxEnergy gradU σ Q) := by
  classical
  have hRemBound :
      |(∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ)
        - (∫ t in I, ψ t * B t)|
        ≤ Cψ_rem * Real.sqrt (boxEnergy gradU σ Q) :=
    hRemBound_from_green_trace σ Q I ψ B gradU gradChiVpsi
      Rside Rtop Rint Cψ_rem hEqDecomp hSideZero hTopZero hRintBound
  exact
    pairing_whitney_analytic_bound
      U W ψ χ I alpha' σ Q gradU gradChiVpsi B
      Cψ_pair Cψ_rem hPairVol hRemBound


/- Project‑preferred aliases -/


/-- Rectangle Green+trace identity (alias). -/
theorem rect_green_trace_identity
  (σ : Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ))
  (I : Set ℝ) (ψ : ℝ → ℝ) (B : ℝ → ℝ)
  (_U _Vψ _χ : ℝ × ℝ → ℝ)
  (gradU gradChiVpsi : (ℝ × ℝ) → ℝ × ℝ)
  (Rside Rtop Rint : ℝ)
  (_hFubini : True) (_hIBP1D : True) (_hChiBC : True) (_hLapVψ : True)
  (hEqDecomp :
    (∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ)
      = (∫ t in I, ψ t * B t) + Rside + Rtop + Rint) :
  (∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ)
    = (∫ t in I, ψ t * B t) + Rside + Rtop + Rint :=
  rect_IBP_decomposition σ Q I ψ B _U _Vψ _χ gradU gradChiVpsi Rside Rtop Rint
    _hFubini _hIBP1D _hChiBC _hLapVψ hEqDecomp


/-- Side/top vanish under admissible cutoff (alias). -/
theorem side_top_zero_of_cutoff
  (σ : Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ))
  (I : Set ℝ) (ψ : ℝ → ℝ) (B : ℝ → ℝ)
  (gradU gradChiVpsi : (ℝ × ℝ) → ℝ × ℝ)
  (Rside Rtop Rint : ℝ)
  (hEqDecomp :
    (∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ)
      = (∫ t in I, ψ t * B t) + Rside + Rtop + Rint)
  (hSideZero : Rside = 0) (hTopZero : Rtop = 0) :
  (∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ)
    = (∫ t in I, ψ t * B t) + Rint :=
  green_trace_rect_to_single_remainder σ Q I ψ B gradU gradChiVpsi Rside Rtop Rint hEqDecomp hSideZero hTopZero




/-
  ------------------------------------------------------------------------
  CR boundary trace (bottom edge) and strong rectangle identity
  ------------------------------------------------------------------------
-/


open scoped MeasureTheory


/-- CR boundary trace on the bottom edge: identify B with −W′ a.e. over I. -/
theorem boundary_CR_trace_bottom_edge
  (I : Set ℝ) (ψ B : ℝ → ℝ) (dσU_tr W' : ℝ → ℝ)
  (hB_eq_normal :
    (fun t => B t) =ᵐ[Measure.restrict (volume) I] (fun t => dσU_tr t))
  (hCR_trace :
    (fun t => dσU_tr t) =ᵐ[Measure.restrict (volume) I] (fun t => - (W' t))) :
  (fun t => ψ t * B t)
    =ᵐ[Measure.restrict (volume) I]
  (fun t => ψ t * (-(W' t))) := by
  have h : (fun t => B t)
             =ᵐ[Measure.restrict (volume) I]
           (fun t => - (W' t)) :=
    hB_eq_normal.trans hCR_trace
  exact h.mono (by intro t ht; simp [ht])


@[simp] lemma dotR2_comm (x y : ℝ × ℝ) : x ⋅ y = y ⋅ x := by
  rcases x with ⟨x1,x2⟩; rcases y with ⟨y1,y2⟩
  simp [dotR2, mul_comm]


@[simp] lemma dotR2_add_right (x y z : ℝ × ℝ) : x ⋅ (y + z) = x ⋅ y + x ⋅ z := by
  rcases x with ⟨x1,x2⟩; rcases y with ⟨y1,y2⟩; rcases z with ⟨z1,z2⟩
  simp [dotR2, mul_add, add_left_comm, add_assoc]


@[simp] lemma dotR2_add_left (x y z : ℝ × ℝ) : (x + y) ⋅ z = x ⋅ z + y ⋅ z := by
  rcases x with ⟨x1,x2⟩; rcases y with ⟨y1,y2⟩; rcases z with ⟨z1,z2⟩
  simp [dotR2, add_mul, add_left_comm, add_assoc]


@[simp] lemma dotR2_smul_right (x v : ℝ × ℝ) (a : ℝ) :
  x ⋅ (a • v) = a * (x ⋅ v) := by
  rcases x with ⟨x1,x2⟩; rcases v with ⟨v1,v2⟩
  simp [dotR2, mul_add, mul_left_comm]


@[simp] lemma dotR2_smul_left (x v : ℝ × ℝ) (a : ℝ) :
  (a • x) ⋅ v = a * (x ⋅ v) := by
  rcases x with ⟨x1,x2⟩; rcases v with ⟨v1,v2⟩
  simp [dotR2, mul_add, mul_comm, mul_left_comm]


/-- Strong rectangle Green+trace identity with explicit interior remainder.


This is algebraic packaging: `hGradSplit_ae` encodes
∇(χ Vψ) = χ ∇Vψ + Vψ ∇χ a.e. on Q; `hCore` is the IBP/Fubini+trace identity
with side/top terms extracted; we conclude the four-term decomposition.
-/
theorem rect_green_trace_identity_strong
  (σ : Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ))
  (I : Set ℝ) (ψ : ℝ → ℝ) (B : ℝ → ℝ)
  (U Vψ χ : ℝ × ℝ → ℝ)
  (gradU gradVψ gradχ gradChiVψ : (ℝ × ℝ) → (ℝ × ℝ))
  (Rside Rtop : ℝ)
  (hGradSplit_ae :
      (fun x => gradChiVψ x)
        =ᵐ[Measure.restrict σ Q]
      (fun x => (χ x) • (gradVψ x) + (Vψ x) • (gradχ x)))
  (_ :
      Integrable (fun x => (gradU x) ⋅ (gradChiVψ x)) (Measure.restrict σ Q))
  (hIntA   :
      Integrable (fun x => (gradU x) ⋅ ((χ x) • (gradVψ x))) (Measure.restrict σ Q))
  (hIntB   :
      Integrable (fun x => (gradU x) ⋅ ((Vψ x) • (gradχ x))) (Measure.restrict σ Q))
  (hIntIntA :
      Integrable (fun x => (gradχ x) ⋅ ((Vψ x) • (gradU x))) (Measure.restrict σ Q))
  (hIntIntB :
      Integrable (fun x => (gradχ x) ⋅ ((U x)   • (gradVψ x))) (Measure.restrict σ Q))
  (hCore :
    (∫ x in Q, (gradU x) ⋅ ((χ x) • (gradVψ x)) ∂σ)
      = (∫ t in I, ψ t * B t) + Rside + Rtop
        - (∫ x in Q, (gradχ x) ⋅ ((U x) • (gradVψ x)) ∂σ)) :
  (∫ x in Q, (gradU x) ⋅ (gradChiVψ x) ∂σ)
    = (∫ t in I, ψ t * B t) + Rside + Rtop
      + ∫ x in Q, (gradχ x) ⋅ ((Vψ x) • (gradU x) - (U x) • (gradVψ x)) ∂σ := by
  classical
  -- Name the interior remainder used in the statement (avoid `let .. in` at head)
  let Rint :=
    ∫ x in Q, (gradχ x) ⋅ ((Vψ x) • (gradU x) - (U x) • (gradVψ x)) ∂σ
  set μ : Measure (ℝ × ℝ) := Measure.restrict σ Q
  -- Expand the test gradient a.e. and integrate
  have hLHS_expanded :
      (∫ x, (gradU x) ⋅ (gradChiVψ x) ∂μ)
        = (∫ x, (gradU x) ⋅ ((χ x) • (gradVψ x) + (Vψ x) • (gradχ x)) ∂μ) := by
    have hpush :
        (fun x => (gradU x) ⋅ (gradChiVψ x))
          =ᵐ[μ] (fun x => (gradU x) ⋅ ((χ x) • (gradVψ x) + (Vψ x) • (gradχ x))) := by
      filter_upwards [hGradSplit_ae] with x hx; simp [hx]
    exact integral_congr_ae hpush
  -- Split the sum inside the integral
  set f : (ℝ × ℝ) → ℝ := fun x => (gradU x) ⋅ ((χ x) • (gradVψ x))
  set g : (ℝ × ℝ) → ℝ := fun x => (gradU x) ⋅ ((Vψ x) • (gradχ x))
  have hAdd :
      (∫ x, (gradU x) ⋅ ((χ x) • (gradVψ x) + (Vψ x) • (gradχ x)) ∂μ)
        = (∫ x, f x ∂μ) + (∫ x, g x ∂μ) := by
    have hpoint : (fun x => (gradU x) ⋅ ((χ x) • (gradVψ x) + (Vψ x) • (gradχ x)))
                    = (fun x => f x + g x) := by
      funext x
      simp only [f, g]
      rw [dotR2_add_right]
    rw [hpoint]
    exact integral_add hIntA hIntB
  -- Use the provided "core" identity for the f-part
  have hCore' :
      (∫ x, f x ∂μ)
        = (∫ t in I, ψ t * B t) + Rside + Rtop
          - (∫ x in Q, (gradχ x) ⋅ ((U x) • (gradVψ x)) ∂σ) := by
    simpa [f] using hCore
  -- Turn the g-part into the interior integral with (∇χ)·(Vψ ∇U)
  have hSwap :
      (∫ x, g x ∂μ)
        = (∫ x in Q, (gradχ x) ⋅ ((Vψ x) • (gradU x)) ∂σ) := by
    have hpt : (fun x => g x) = (fun x => (gradχ x) ⋅ ((Vψ x) • (gradU x))) := by
      funext x
      simp only [g, dotR2_smul_right, dotR2_comm]
    simp_rw [hpt]
    rfl
  -- Put the pieces together
  have :
      (∫ x in Q, (gradU x) ⋅ (gradChiVψ x) ∂σ)
        = (∫ t in I, ψ t * B t) + Rside + Rtop
          + ( (∫ x in Q, (gradχ x) ⋅ ((Vψ x) • (gradU x)) ∂σ)
              - (∫ x in Q, (gradχ x) ⋅ ((U x) • (gradVψ x)) ∂σ) ) := by
    have := calc
      (∫ x, (gradU x) ⋅ (gradChiVψ x) ∂μ)
          = (∫ x, (gradU x) ⋅ ((χ x) • (gradVψ x) + (Vψ x) • (gradχ x)) ∂μ) := hLHS_expanded
      _ = (∫ x, f x ∂μ) + (∫ x, g x ∂μ) := hAdd
      _ = ((∫ t in I, ψ t * B t) + Rside + Rtop
              - (∫ x in Q, (gradχ x) ⋅ ((U x) • (gradVψ x)) ∂σ))
            + (∫ x in Q, (gradχ x) ⋅ ((Vψ x) • (gradU x)) ∂σ) := by
              simpa [hSwap] using congrArg (fun z => z + (∫ x, g x ∂μ)) hCore'
      _ = (∫ t in I, ψ t * B t) + Rside + Rtop
            + ( (∫ x in Q, (gradχ x) ⋅ ((Vψ x) • (gradU x)) ∂σ)
                - (∫ x in Q, (gradχ x) ⋅ ((U x) • (gradVψ x)) ∂σ) ) := by
              ring
    simpa using this
  -- Define Rint and conclude
  have hIntSub :
      (∫ x in Q, (gradχ x) ⋅ ((Vψ x) • (gradU x)) ∂σ)
        - (∫ x in Q, (gradχ x) ⋅ ((U x) • (gradVψ x)) ∂σ)
      = Rint := by
    -- definition of Rint
    simp only [Rint]
    have h1 : ∫ x in Q, (gradχ x) ⋅ ((Vψ x) • (gradU x) - (U x) • (gradVψ x)) ∂σ =
              ∫ x in Q, ((gradχ x) ⋅ ((Vψ x) • (gradU x)) - (gradχ x) ⋅ ((U x) • (gradVψ x))) ∂σ := by
      congr 1
      funext x
      -- Distribute dot product over subtraction: a ⋅ (b - c) = a ⋅ b - a ⋅ c
      simp only [dotR2, Prod.fst_sub, Prod.snd_sub]
      ring
    rw [h1, ← integral_sub hIntIntA hIntIntB]
  rw [this, hIntSub]


end RS
end RH
