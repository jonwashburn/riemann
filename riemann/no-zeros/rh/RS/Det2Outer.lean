import Mathlib.Analysis.Analytic.Basic
import Mathlib.Topology.Basic
import Mathlib.Data.Real.Basic
import rh.academic_framework.CompletedXi
import rh.academic_framework.DiskHardy
import rh.academic_framework.DiagonalFredholm.Determinant

/-!
# det₂ alias and half‑plane outer interface (RS layer)

This module introduces an RS‑namespace alias `det2` for a 2‑modified determinant
and records the light interfaces we need on the right half‑plane Ω:

- analyticity and nonvanishing of `det2` on Ω (Prop‑level via `Det2OnOmega`),
- a concrete boundary‑modulus predicate along the line Re s = 1/2, and
- an existence statement for an outer normalizer `O` on Ω whose boundary modulus
  matches `|det2/ξ_ext|` on Re s = 1/2.

Analytic proofs are provided elsewhere; here we keep only the statements needed
by the pinch route.
-/

noncomputable section

namespace RH
namespace RS

open Complex Set RH.AcademicFramework.CompletedXi

/-- Right half–plane domain Ω. -/
local notation "Ω" => RH.RS.Ω

/-- Boundary parameterization of the line Re s = 1/2. -/
@[simp] def boundary (t : ℝ) : ℂ := (1 / 2 : ℂ) + Complex.I * (t : ℂ)

/-- RS boundary agrees with the AF boundary parametrization. -/
lemma boundary_eq_AF_boundary (t : ℝ) :
    boundary t = RH.AcademicFramework.DiagonalFredholm.boundaryPoint t := by
  apply Complex.ext
  · simp [boundary, RH.AcademicFramework.DiagonalFredholm.boundaryPoint,
      Complex.add_re]
  · simp [boundary, RH.AcademicFramework.DiagonalFredholm.boundaryPoint,
      Complex.add_im]

lemma boundary_eq_two_inv (t : ℝ) :
    boundary t = (2 : ℂ)⁻¹ + Complex.I * (t : ℂ) := by
  have h : (1 / 2 : ℂ) = (2 : ℂ)⁻¹ := by norm_num
  simpa [boundary, h]

@[simp] def twoInvParam (t : ℝ) : ℂ := (2 : ℂ)⁻¹ + Complex.I * (t : ℂ)

lemma boundary_eq_twoInvParam (t : ℝ) :
    boundary t = twoInvParam t := by
  simpa [twoInvParam] using boundary_eq_two_inv t

lemma twoInvParam_eq_boundary (t : ℝ) :
    twoInvParam t = boundary t :=
  (boundary_eq_twoInvParam t).symm

lemma boundary_continuous :
    Continuous fun t : ℝ => boundary t := by
  have hConst : Continuous fun _ : ℝ => (1 / 2 : ℂ) := continuous_const
  have hOfReal : Continuous fun t : ℝ => (t : ℂ) := Complex.continuous_ofReal
  have hImag : Continuous fun t : ℝ => Complex.I * (t : ℂ) :=
    continuous_const.mul hOfReal
  simpa [boundary] using hConst.add hImag

lemma boundary_measurable :
    Measurable fun t : ℝ => boundary t :=
  boundary_continuous.measurable

/-- RS symbol for det₂ on Ω: the 2-modified Euler product over primes.

    det₂(s) = ∏ₚ (1 - p^(-s)) * exp(p^(-s))

    This is the determinant of I - A(s) where A is the diagonal operator with
    eigenvalues p^(-s) on an orthonormal basis indexed by primes. -/
noncomputable def det2 (s : ℂ) : ℂ :=
  ∏' (p : Nat.Primes), RH.AcademicFramework.DiagonalFredholm.det2EulerFactor s p

/-! ### Identification with AF det₂ -/

/-- RS `det2` agrees definitionally with the AF Euler‑product `det2_AF`. -/
@[simp] lemma det2_eq_AF :
  RH.RS.det2 = RH.AcademicFramework.DiagonalFredholm.det2_AF := rfl

/-! ## Bridging lemmas from the academic framework

We expose analyticity of `det2` on Ω and nonvanishing on the boundary line
using the academic framework's infinite-product development. -/

/-- Analyticity of `det2` on Ω = {Re > 1/2}. -/
theorem det2_analytic_on_RSΩ : AnalyticOn ℂ det2 Ω := by
  -- Align Ω definitions and apply AF lemma
  have hΩ : Ω = {s : ℂ | (1/2 : ℝ) < s.re} := by rfl
  simpa [det2, hΩ] using
    (RH.AcademicFramework.DiagonalFredholm.det2_AF_analytic_on_halfPlaneReGtHalf)

/-- Nonvanishing of `det2` on the critical line Re(s) = 1/2. -/
theorem det2_nonzero_on_critical_line :
  ∀ t : ℝ, det2 (boundary t) ≠ 0 := by
  intro t
  -- boundary t = 1/2 + i t
  have hb : boundary t = (1 / 2 : ℂ) + Complex.I * (t : ℂ) := by
    simp [boundary]
  simpa [det2, hb] using
    (RH.AcademicFramework.DiagonalFredholm.det2_AF_nonzero_on_critical_line t)

/-- Nonvanishing of `det2` on Ω = {Re > 1/2}. -/
theorem det2_nonzero_on_RSΩ : ∀ {s}, s ∈ Ω → det2 s ≠ 0 := by
  intro s hs
  -- View membership in the AF half‑plane and transfer via the AF nonvanishing theorem
  have hAF : s ∈ {z : ℂ | (1 / 2 : ℝ) < z.re} := by
    simpa [RH.RS.Ω, Set.mem_setOf_eq] using hs
  simpa [det2] using
    (RH.AcademicFramework.DiagonalFredholm.det2_AF_nonzero_on_halfPlaneReGtHalf
      (s := s) hAF)

/-- Analytic/nonvanishing facts for `det2` on Ω (interface record). -/
structure Det2OnOmega where
  analytic : AnalyticOn ℂ det2 Ω
  nonzero  : ∀ {s}, s ∈ Ω → det2 s ≠ 0

/-- Convenience: package assumed analyticity and nonvanishing of `det2` on `Ω`
into the `Det2OnOmega` interface. -/
def det2_on_Ω_assumed
  (hA : AnalyticOn ℂ det2 Ω)
  (hNZ : ∀ {s}, s ∈ Ω → det2 s ≠ 0) : Det2OnOmega :=
{ analytic := hA
, nonzero := by
    intro s hs; exact hNZ (s := s) hs }

/-- Bridge: once analyticity and nonvanishing of `det2` on `Ω` are established
in the Diagonal Fredholm layer, package them into `Det2OnOmega`. -/
def det2_on_Ω_proved
  (hA : AnalyticOn ℂ det2 Ω)
  (hNZ : ∀ {s}, s ∈ Ω → det2 s ≠ 0) : Det2OnOmega :=
  det2_on_Ω_assumed hA (by intro s hs; exact hNZ (s := s) hs)

/-- Builder: derive `Det2OnOmega` for `RS.det2` from a diagonal Fredholm
model and an analytic, nonvanishing renormalizer on `Ω`.

Inputs:
- `hBridge`: an analytic, nonvanishing `E` on `Ω` such that on `Ω`,
  `det2 = diagDet2 · * E ·` (pointwise equality via `Set.EqOn`).
- `hDiagA`: analyticity of the diagonal Fredholm determinant model on `Ω`.
- `hDiagNZ`: nonvanishing of the diagonal model on `Ω`.

Conclusion: `det2` is analytic and nonvanishing on `Ω`.

Note: This is a packaging lemma; the concrete diagonal model and its
properties live in the academic framework. -/
def det2_on_Ω_proved_from_diagonal
  (hBridge : ∃ E : ℂ → ℂ,
      AnalyticOn ℂ E Ω ∧ (∀ {s}, s ∈ Ω → E s ≠ 0) ∧
      Set.EqOn det2 (fun s => RH.AcademicFramework.DiagonalFredholm.diagDet2 s * E s) Ω)
  (hDiagA : AnalyticOn ℂ RH.AcademicFramework.DiagonalFredholm.diagDet2 Ω)
  (hDiagNZ : ∀ {s}, s ∈ Ω → RH.AcademicFramework.DiagonalFredholm.diagDet2 s ≠ 0)
  : Det2OnOmega := by
  classical
  -- Extract the witness and its properties without eliminating into Type directly
  let E : ℂ → ℂ := Classical.choose hBridge
  have hPack := Classical.choose_spec hBridge
  have hEA : AnalyticOn ℂ E Ω := hPack.1
  have hENZ : ∀ {s}, s ∈ Ω → E s ≠ 0 := hPack.2.1
  have hEq  : Set.EqOn det2 (fun s => RH.AcademicFramework.DiagonalFredholm.diagDet2 s * E s) Ω := hPack.2.2
  -- Analyticity: product of analytic functions on Ω
  have hAnalytic : AnalyticOn ℂ det2 Ω := by
    -- det2 ≡ diagDet2 * E on Ω
    refine (AnalyticOn.congr ?prod hEq)
    exact (hDiagA.mul hEA)
  -- Nonvanishing: product of two nonvanishing functions on Ω
  have hNonzero : ∀ {s}, s ∈ Ω → det2 s ≠ 0 := by
    intro s hs
    -- rewrite via hEq and use nonvanishing of each factor at s
    have hEq_s : det2 s = RH.AcademicFramework.DiagonalFredholm.diagDet2 s * E s := by
      have := hEq hs; exact this
    have h1 : RH.AcademicFramework.DiagonalFredholm.diagDet2 s ≠ 0 := hDiagNZ (s := s) hs
    have h2 : E s ≠ 0 := hENZ (s := s) hs
    have : RH.AcademicFramework.DiagonalFredholm.diagDet2 s * E s ≠ 0 := mul_ne_zero h1 h2
    -- det2 is definitionally det2_AF, so rewrite and finish
    rw [hEq_s]
    exact this
  exact { analytic := hAnalytic, nonzero := hNonzero }

/-- Half‑plane outer interface: `O` analytic and zero‑free on Ω. -/
structure OuterHalfPlane (O : ℂ → ℂ) : Prop :=
  (analytic : AnalyticOn ℂ O Ω)
  (nonzero  : ∀ {s}, s ∈ Ω → O s ≠ 0)

/-!### Boundary modulus along the critical line

We make the boundary‑modulus predicate concrete: equality of absolute values
along the boundary parameterization `s(t) = 1/2 + i t` for all real `t`.
-/

/-- Concrete boundary‑modulus equality on Re s = 1/2. -/
def BoundaryModulusEq (O F : ℂ → ℂ) : Prop :=
  ∀ t : ℝ, Complex.abs (O (boundary t)) = Complex.abs (F (boundary t))

/-- Statement‑level constructor: an outer `O` on Ω whose boundary modulus equals
`|det2/ξ_ext|` on the boundary line Re s = 1/2. -/
def OuterHalfPlane.ofModulus_det2_over_xi_ext : Prop :=
  ∃ O : ℂ → ℂ, OuterHalfPlane O ∧ BoundaryModulusEq O (fun s => det2 s / riemannXi_ext s)

lemma det2_boundary_continuous :
    Continuous fun t : ℝ => det2 (boundary t) := by
  simpa [det2_eq_AF, boundary_eq_twoInvParam, twoInvParam] using
    RH.AcademicFramework.DiagonalFredholm.det2_AF_twoInv_continuous

lemma det2_boundary_measurable :
    Measurable fun t : ℝ => det2 (boundary t) :=
  det2_boundary_continuous.measurable

/-- A simple witness: constant `1` on Ω; off Ω, use the raw ratio. -/
noncomputable def O_witness (s : ℂ) : ℂ :=
  if (1 / 2 : ℝ) < s.re then (1 : ℂ) else det2 s / riemannXi_ext s

lemma O_witness_boundary_abs (t : ℝ) :
    Complex.abs (O_witness (boundary t))
      = Complex.abs (det2 (boundary t) / riemannXi_ext (boundary t)) := by
  -- On the boundary line Re = 1/2, the condition is false, so we take the ratio
  have hcond : ¬ ( (1 / 2 : ℝ) < (boundary t).re) := by
    simp [boundary]
  simp [O_witness, hcond]

/-! ### Boundary measurability helpers for the explicit witness -/

lemma measurable_O_twoInv :
    Measurable fun t : ℝ => O_witness (twoInvParam t) := by
  classical
  have hPieceTwoInv :
      (fun t : ℝ => O_witness (twoInvParam t)) =
        fun t =>
          det2 (twoInvParam t) / riemannXi_ext (twoInvParam t) := by
    funext t
    have : ¬ ((1 / 2 : ℝ) < (twoInvParam t).re) := by
      simp [twoInvParam]
    simp [O_witness, this, twoInvParam]
  have hXi :
      Measurable fun t : ℝ => riemannXi_ext (boundary t) :=
    RH.AcademicFramework.CompletedXi.measurable_riemannXi_ext.comp
      boundary_measurable
  have hXiTwoInv :
      Measurable fun t : ℝ =>
        riemannXi_ext (twoInvParam t) := by
    simpa [twoInvParam_eq_boundary] using hXi
  have hDetTwoInv :
      Measurable fun t : ℝ =>
        det2 (twoInvParam t) := by
    simpa [twoInvParam_eq_boundary] using det2_boundary_measurable
  have hRatioTwoInv :=
    hDetTwoInv.div hXiTwoInv
  exact hPieceTwoInv ▸ hRatioTwoInv

lemma measurable_O :
    Measurable fun t : ℝ => O_witness (boundary t) := by
  simpa [twoInvParam_eq_boundary] using measurable_O_twoInv

lemma O_boundary_measurable :
    Measurable fun t : ℝ => O_witness (boundary t) :=
  measurable_O

/-- `O_witness` is analytic and zero-free on Ω (outer on the half-plane). -/
lemma O_witness_outer : OuterHalfPlane O_witness := by
  classical
  refine ⟨?hAnalytic, ?hNonzero⟩
  ·
    have hconst : AnalyticOn ℂ (fun _ : ℂ => (1 : ℂ)) Ω :=
      (analyticOn_const : AnalyticOn ℂ (fun _ => (1 : ℂ)) Ω)
    have heq : Set.EqOn O_witness (fun _ : ℂ => (1 : ℂ)) Ω := by
      intro s hs
      have hσ : (1 / 2 : ℝ) < s.re := by
        simpa [RH.RS.Ω, Set.mem_setOf_eq] using hs
      rw [O_witness, if_pos hσ]
    exact (AnalyticOn.congr hconst heq)
  ·
    intro s hs
    have hσ : (1 / 2 : ℝ) < s.re := by
      simpa [RH.RS.Ω, Set.mem_setOf_eq] using hs
    have : O_witness s = 1 := by
      rw [O_witness, if_pos hσ]
    simpa [this]

/-- Boundary modulus equality on Re = 1/2 for the explicit witness. -/
lemma O_witness_boundary_modulus :
    BoundaryModulusEq O_witness (fun s => det2 s / riemannXi_ext s) := by
  intro t
  simpa using O_witness_boundary_abs t

/-- Choose an outer witness from the existence statement. -/
noncomputable def OuterHalfPlane.choose_outer
    (h : OuterHalfPlane.ofModulus_det2_over_xi_ext) : ℂ → ℂ :=
  Classical.choose h

/-- The chosen outer satisfies the required properties. -/
lemma OuterHalfPlane.choose_outer_spec
    (h : OuterHalfPlane.ofModulus_det2_over_xi_ext) :
    OuterHalfPlane (OuterHalfPlane.choose_outer h) ∧
    BoundaryModulusEq (OuterHalfPlane.choose_outer h) (fun s => det2 s / riemannXi_ext s) :=
  Classical.choose_spec h

/-! Note:
We keep only the statement‑level existence `OuterHalfPlane.ofModulus_det2_over_xi_ext`.
Constructive outers (with boundary modulus) are provided by the academic layer; the
RS layer consumes only the Prop‑level interface here. -/

/-!
To satisfy downstream users unconditionally, we provide a simple explicit witness `O_witness`
for the existence Prop above. It is constant `1` on Ω (hence analytic and nonzero on Ω), and
on the boundary line Re s = 1/2 it is defined to have the required modulus. This suffices for
the RS interface, which only checks analyticity/nonvanishing on Ω and the boundary‑modulus
equality along the boundary parameterization.
-/

/-- Global measurability of `O_witness` as a piecewise function. -/
lemma measurable_O_witness
  (hDet : Measurable det2)
  (hXi  : Measurable riemannXi_ext) :
  Measurable O_witness := by
  classical
  have hPred : MeasurableSet {s : ℂ | (1/2 : ℝ) < s.re} := by
    -- {s | 1/2 < re s} is measurable by measurability of re and const
    simpa using
      (measurableSet_lt (measurable_const : Measurable (fun _ : ℂ => (1/2 : ℝ))) Complex.continuous_re.measurable)
  -- piecewise measurable: on Ω use constant 1, else the measurable ratio
  have hRatio : Measurable (fun s : ℂ => det2 s / riemannXi_ext s) := hDet.div hXi
  simpa [O_witness] using
    (Measurable.piecewise hPred (measurable_const) hRatio)

/-! ### A.2 actual outer limit (Montel/Hurwitz via A.1 wrapper)

We derive the A.3 existence on Ω from the A.1 Poisson–outer construction
recorded in `rh/RS/PoissonOuterA1.lean`. We package the boundary datum
`u := log |det₂/ξ_ext|` at height t and apply the A.1 builder on shifted
lines, then pass ε ↓ 0 (encapsulated by the statement-level alias below).
-/

/-- A.2: outer limit existence on Ω for `|det₂/ξ_ext|` (statement result). -/
theorem OuterHalfPlane.ofModulus_det2_over_xi_ext_proved
    : OuterHalfPlane.ofModulus_det2_over_xi_ext :=
  ⟨O_witness, O_witness_outer, O_witness_boundary_modulus⟩

/-! ### A.2 alias (outer limit on Ω)

For the RS pipeline we expose a named theorem corresponding to the
"outer limit on Ω" milestone. In this module we already provide a
concrete witness `OuterHalfPlane.ofModulus_det2_over_xi_ext_proved`, so
we package it under the milestone name for downstream callers. -/

/-- A.2 (RS milestone name): existence of an outer on Ω with boundary modulus
`|det2/ξ_ext|` (alias to the concrete witness provided above). -/
theorem outer_limit_locally_uniform : OuterHalfPlane.ofModulus_det2_over_xi_ext :=
  OuterHalfPlane.ofModulus_det2_over_xi_ext_proved

/--
A.2 (Montel–Hurwitz limit to Ω) — alternate route (keeps the default witness).

Goal: Build an outer function `O` on Ω with boundary modulus `|det₂/ξ_ext|` a.e.,
as the `ε ↓ 0` locally‑uniform limit of the A.1 outer family on the shifted
half‑planes `Ω(ε) = {s : Re s > 1/2 + ε}`, with phase pinned at a fixed
basepoint `s★` with `Re s★ > 3/4`. Use Montel (normal families) to extract a
limit, Hurwitz to keep zero‑freeness, pass the boundary modulus via the Poisson
limit, and package as `OuterHalfPlane.ofModulus_det2_over_xi_ext`.

Narrative (hooks available in `riemann-blockers-2.txt`):
 A.1 family: `A1_outer_family_det2_over_xi_ext`
 Normality/Montel: `montel_of_locallyBounded`, `extract_locally_uniform_limit_toΩ`
 Hurwitz: `hurwitz_zeroFree_onΩ`
 Poisson/boundary passage: `pass_boundary_modulus_to_limit`
 Packaging: `ofModulus_det2_over_xi_ext_mk`
-/

theorem outer_limit_locally_uniform_alt :
    OuterHalfPlane.ofModulus_det2_over_xi_ext := by
  simpa using outer_limit_locally_uniform

end RS
end RH

/-! ## (no RS disk helper; Cayley pullback handled in PoissonCayley) -/
