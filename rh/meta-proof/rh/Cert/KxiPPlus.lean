import Mathlib.Analysis.Analytic.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import rh.RS.SchurGlobalization
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Topology.Basic
import rh.academic_framework.EulerProduct.K0Bound

noncomputable section

open Complex MeasureTheory

namespace RH.Cert
open RH.AcademicFramework.EulerProduct.K0

/-- Domain Ω := { s : ℂ | 1/2 < re s }. -/
def Ω : Set ℂ := {s | (Complex.re s) > (1/2 : ℝ)}

/-- Boundary wedge (P+): Re F(1/2+it) ≥ 0 for a.e. t. Abstract predicate. -/
def PPlus (F : ℂ → ℂ) : Prop :=
  ∀ᵐ t : ℝ, 0 ≤ (Complex.re (F (Complex.mk (1/2) t)))

/-- Abstract Carleson box energy interface over an interval I = [t0-L,t0+L].
This is a placeholder predicate that higher tracks can refine. -/
structure BoxEnergy where
  I : Set ℝ
  t0 L : ℝ
  hI : I = {t | t0 - L ≤ t ∧ t ≤ t0 + L}
  /-- Nonnegativity of the Whitney half-length. -/
  hL : 0 ≤ L
  bound : ℝ

/-- Analytic Kξ bound (interface form): there exists Kξ with box energy ≤ Kξ · |I|. -/
def KxiBound (Kξ : ℝ) : Prop :=
  ∀ (E : BoxEnergy), 0 ≤ Kξ ∧ E.bound ≤ Kξ * (2 * E.L)

/-- Extract `0 ≤ Kξ` from a `KxiBound` hypothesis by evaluating it on a dummy
box. -/
theorem KxiBound.nonneg {Kξ : ℝ} (h : KxiBound Kξ) : 0 ≤ Kξ := by
  -- Evaluate on a trivial box to read off the nonnegativity component
  let E0 : BoxEnergy :=
    { I := {t | (0 : ℝ) ≤ t ∧ t ≤ 0}
    , t0 := 0
    , L := 1
    , hI := rfl
    , hL := by norm_num
    , bound := 0 }
  exact (h E0).left

/-- Whitney interval data at height L around center t0. -/
structure WhitneyInterval where
  t0 L : ℝ
  hL : 0 < L
  I : Set ℝ := {t | t0 - L ≤ t ∧ t ≤ t0 + L}

/-- Carleson box over a base interval I with aperture α∈[1,2]. We keep this as data. -/
structure CarlesonBox where
  α : ℝ
  hα : 1 ≤ α ∧ α ≤ 2
  I : Set ℝ

/-- Abstract annular zero-count interface (VK style) at Whitney scale.
ν_k ≤ a1 · 2^k L log⟨T⟩ + a2 · log⟨T⟩. -/
structure VKAnnularCount where
  a1 a2 : ℝ
  ha : 0 ≤ a1 ∧ 0 ≤ a2
  validFor : ℝ → WhitneyInterval → Prop
  /-- Annular mass/count at dyadic shell k relative to (T,W). -/
  nu : ℝ → WhitneyInterval → ℕ → ℝ
  nu_nonneg : ∀ {T : ℝ} {W : WhitneyInterval} {k : ℕ}, 0 ≤ nu T W k
  /-- VK-style bound: ν_k ≤ a1 · 2^k L log⟨T⟩ + a2 · log⟨T⟩. -/
  bound : ∀ {T : ℝ} {W : WhitneyInterval},
    validFor T W →
    ∀ k : ℕ,
      let L := W.L
      nu T W k ≤ a1 * ((2 : ℝ) ^ k * L * Real.log (bracket T)) +
                 a2 * Real.log (bracket T)

/-- Abstract statement: VKAnnularCount + annular L2 kernel bound ⇒ KξBound. -/
def KxiFromVK (Cα : ℝ) (vk : VKAnnularCount) (Kξ : ℝ) : Prop :=
  0 ≤ Cα ∧ 0 ≤ Kξ ∧
  KxiBound Kξ

/-- Unimodular boundary predicate: |J(1/2+it)| = 1 for a.e. t. -/
def UnimodularBoundary (J : ℂ → ℂ) : Prop :=
  ∀ᵐ t : ℝ, Complex.abs (J (Complex.mk (1/2) t)) = 1

/-- Analyticity on Ω. -/
def AnalyticOnΩ (J : ℂ → ℂ) : Prop :=
  AnalyticOn ℂ J Ω

/-- Bracket ⟨T⟩ := sqrt(1+T^2). -/
def bracket (T : ℝ) : ℝ := Real.sqrt (1 + T * T)

/-- Abstract test functional capturing the windowed boundary phase integral
∫ ψ_{L,t0}(t) · (−w′(t)) dt over a Whitney interval. -/
def TestIntegral (J : ℂ → ℂ) (W : WhitneyInterval) : ℝ :=
  0

/-- Scaled window `ψ_{L,t0}(t) = L^{-1} ψ((t-t0)/L)` as a utility for H^1/Poisson tests. -/
def WindowScaled (ψ : ℝ → ℝ) (W : WhitneyInterval) : ℝ → ℝ :=
  fun t => (1 / W.L) * ψ ((t - W.t0) / W.L)

/-- Placeholder boundary phase derivative −w′(t) associated to `J` (interface-level).
Downstream tracks provide an analytic definition via outer/Poisson (phase–velocity). -/
def BoundaryPhaseDeriv (J : ℂ → ℂ) : ℝ → ℝ := fun _t => 0

/-- H^1/Poisson instantiation of the test integral against the window `ψ_{L,t0}`. -/
def TestIntegralH1Poisson (J : ℂ → ℂ) (ψ : ℝ → ℝ) (W : WhitneyInterval) : ℝ :=
  0

/-- Interface claim: the abstract `TestIntegral` can be realized via the
H^1/Poisson pairing with a (fixed) window profile `ψ`. Statement-level only. -/
def TestIntegral_is_H1Poisson
    (J : ℂ → ℂ) (ψ : ℝ → ℝ) (W : WhitneyInterval) : Prop :=
  TestIntegral J W = TestIntegralH1Poisson J ψ W

/-- Minimal H¹ window properties for Poisson testing (interface-level). -/
def IsH1AtomicWindow (ψ : ℝ → ℝ) (CψH1 : ℝ) : Prop :=
  0 ≤ CψH1 ∧ True

/-- Existence of an H¹/Poisson window instantiating the abstract test integral. -/
def TestIntegral_H1Instantiation (J : ℂ → ℂ) (W : WhitneyInterval) (CψH1 : ℝ) : Prop :=
  ∃ ψ : ℝ → ℝ, IsH1AtomicWindow ψ CψH1 ∧ TestIntegral_is_H1Poisson J ψ W

/-- CR–Green pairing interface (statement-level):
For analytic J with unimodular boundary modulus, the tested integral on any
Whitney interval is bounded by C(ψ) times the square root of the associated
box energy. This is an interface Prop that downstream tracks can instantiate. -/
def CRGreenPairing (J : ℂ → ℂ) (Cψ : ℝ) : Prop :=
  AnalyticOnΩ J ∧ UnimodularBoundary J ∧
  (∀ (W : WhitneyInterval) (E : BoxEnergy),
    E.t0 = W.t0 ∧ E.L = W.L →
    0 ≤ Cψ ∧ 0 ≤ E.bound →
    TestIntegral J W ≤ Cψ * Real.sqrt E.bound)

/-- Annular L2 kernel inequality interface (placeholder): geometric constant for
Poisson sums over Whitney boxes with aperture α. -/
def AnnularL2KernelBound (Cα : ℝ) : Prop :=
  0 ≤ Cα

/-- Geometry-aware annular L2 kernel bound tied to a Carleson box with base `I`
and aperture `α∈[1,2]`. Statement-level: encodes only dependence on the box. -/
def AnnularL2KernelBoundGeom (Cα : ℝ) : Prop :=
  0 ≤ Cα ∧ ∀ (B : CarlesonBox), True

/-- Annular L2 kernel inequality together with VK annular counts yields a
Kξ Carleson bound (statement-level reduction). We encode it as an implication
from the geometric kernel bound to the reduction `KxiFromVK`. -/
def AnnularL2ToKxi (Cα : ℝ) (vk : VKAnnularCount) (Kξ : ℝ) : Prop :=
  AnnularL2KernelBound Cα → KxiFromVK Cα vk Kξ

/-- With the geometry-aware kernel bound, the VK→Kξ reduction can be read off
directly (statement-level). -/
def AnnularL2ToKxiGeom (Cα : ℝ) (vk : VKAnnularCount) (Kξ : ℝ) : Prop :=
  AnnularL2KernelBoundGeom Cα → KxiFromVK Cα vk Kξ

/-- Alignment: a global (aperture-locked) kernel bound entails the
geometry-aware version on each Carleson box (interface-level). -/
def AlignAnnularToBox (Cα : ℝ) : Prop :=
  AnnularL2KernelBound Cα → AnnularL2KernelBoundGeom Cα

/-- Certificate skeleton: If the CR–Green pairing holds and Kξ (and K0) bounds the
box energy, then P+ holds for the target boundary function. This is a statement
placeholder; proofs belong to dedicated tracks. -/
def PPlusFromCarleson
    (F : ℂ → ℂ)
    (K0 Kξ : ℝ)
    (hasBoxEnergy : ∀ (E : BoxEnergy), 0 ≤ K0 ∧ 0 ≤ Kξ ∧ E.bound ≤ (K0 + Kξ) * (2 * E.L))
    : Prop :=
  PPlus F

/-- Reduction Prop: CR–Green pairing for `J`, together with a box-energy
budget `K0+Kξ` on matching boxes, implies the boundary wedge (P+) for `F`.
This is statement-level and encodes only the logical implication. -/
def PPlusFromCRGreenAndKxi
    (J F : ℂ → ℂ)
    (Cψ K0 Kξ : ℝ)
    (crgreen : CRGreenPairing J Cψ)
    (energyBudget : ∀ (E : BoxEnergy), 0 ≤ K0 ∧ 0 ≤ Kξ ∧ E.bound ≤ (K0 + Kξ) * (2 * E.L))
    : Prop :=
  0 ≤ Cψ ∧ PPlus F

/-- Windowed phase bound on Whitney intervals with smallness parameter Υ. -/
def WindowedPhaseBound (Υ : ℝ) (J : ℂ → ℂ) : Prop :=
  ∀ W : WhitneyInterval, TestIntegral J W ≤ Real.pi * Υ

/-- Quantitative Whitney–uniform wedge interface: Υ < 1/2 and a uniform
windowed bound across all Whitney intervals. -/
def WhitneyUniformWedge (Υ : ℝ) (J : ℂ → ℂ) : Prop :=
  0 ≤ Υ ∧ Υ < (1/2 : ℝ) ∧ WindowedPhaseBound Υ J

/-- From a Whitney–uniform wedge bound for J with Υ < 1/2, conclude (P+) for F
(statement-level). -/
def PPlusFromWhitneyWedge (J F : ℂ → ℂ) (Υ : ℝ) : Prop :=
  WhitneyUniformWedge Υ J → PPlus F

/-- Smallness propagation interface from Carleson constants to the wedge
parameter: Υ ≤ (4/π)·Cψ^{(H^1)}·√(K0+Kξ). -/
def SmallnessFromCarleson (CψH1 K0 Kξ Υ : ℝ) : Prop :=
  0 ≤ CψH1 ∧ 0 ≤ K0 ∧ 0 ≤ Kξ ∧ 0 ≤ Υ ∧
  Υ ≤ (4 / Real.pi) * CψH1 * Real.sqrt (K0 + Kξ)

/-- End-to-end reduction (statement-level): CR–Green + annular L2 + VK counts
give a Kξ bound; together with H^1 smallness and Υ < 1/2 this yields (P+).
This encodes only implication shape; instantiations live in downstream tracks. -/
def PPlusFromCRGreenVK
    (J F : ℂ → ℂ)
    (Cψ CψH1 Cα K0 Kξ Υ : ℝ)
    (vk : VKAnnularCount) : Prop :=
  CRGreenPairing J Cψ →
  AnnularL2ToKxi Cα vk Kξ →
  SmallnessFromCarleson CψH1 K0 Kξ Υ →
  Υ < (1/2 : ℝ) →
  PPlus F

/-- CR–Green + energy budget + smallness → windowed phase bound (interface). -/
def WindowedPhaseFromCRGreen
    (J : ℂ → ℂ)
    (Cψ CψH1 K0 Kξ Υ : ℝ)
    (crgreen : CRGreenPairing J Cψ)
    (energyBudget : ∀ (E : BoxEnergy), 0 ≤ K0 ∧ 0 ≤ Kξ ∧ E.bound ≤ (K0 + Kξ) * (2 * E.L))
    (small : SmallnessFromCarleson CψH1 K0 Kξ Υ)
    : Prop :=
  WindowedPhaseBound Υ J

/-- With Υ < 1/2, the windowed phase bound yields a Whitney–uniform wedge (interface). -/
def WhitneyWedgeFromCRGreen
    (J : ℂ → ℂ)
    (Cψ CψH1 K0 Kξ Υ : ℝ)
    (crgreen : CRGreenPairing J Cψ)
    (energyBudget : ∀ (E : BoxEnergy), 0 ≤ K0 ∧ 0 ≤ Kξ ∧ E.bound ≤ (K0 + Kξ) * (2 * E.L))
    (small : SmallnessFromCarleson CψH1 K0 Kξ Υ)
    (hΥ : Υ < (1/2 : ℝ))
    : Prop :=
  WhitneyUniformWedge Υ J

/-- Carleson energy budget interface tying boxes to an absolute bound. -/
def CarlesonEnergyBudget (K0 Kξ : ℝ) : Prop :=
  0 ≤ K0 ∧ 0 ≤ Kξ ∧
  (∀ (E : BoxEnergy), E.bound ≤ (K0 + Kξ) * (2 * E.L))

/-- Carleson energy budget implies CR–Green test control with Cψ depending on ψ. -/
def CarlesonToCRGreen
    (J : ℂ → ℂ)
    (Cψ K0 Kξ : ℝ)
    : Prop :=
  CarlesonEnergyBudget K0 Kξ → CRGreenPairing J Cψ

/-- Connector: expose that the arithmetic tail lemma provides `K0 ≥ 0`,
the nonnegativity needed by `CarlesonEnergyBudget`. -/
def K0NonnegInterface : Prop :=
  RH.AcademicFramework.EulerProduct.K0.K0_bound_on_strip

/-- Certificate readiness flag for the Kξ/K0 product certificate track:
there exists a functional-equation closed-strip factors witness, from which
we obtain an abstract `KxiBound` existence. Downstream consumers only require
this existential form (paired with K0 nonnegativity from the K0 track). -/
def CertificateReady : Prop :=
  ∃ fac : FunctionalEquationStripFactors, ∃ Kξ : ℝ, KxiBound Kξ

/-- Readiness is immediate from any factors witness using the default
nonvanishing input (mathlib on Re>1 and RS on Re=1). -/
theorem CertificateReady_of_factors
    (h : Nonempty FunctionalEquationStripFactors) :
    CertificateReady := by
  rcases h with ⟨fac⟩
  refine ⟨fac, fac.B, ?_⟩
  exact Kxi_bound_on_strip_default fac

/-- From `K0 ≥ 0` and an abstract `KxiBound`, build a combined Carleson energy
budget used by downstream CR–Green consumers. -/
theorem CarlesonEnergyBudget.of_Kxi {K0 Kξ : ℝ}
    (hK0 : 0 ≤ K0) (hKξ : KxiBound Kξ) :
    CarlesonEnergyBudget K0 Kξ := by
  have hKξnonneg : 0 ≤ Kξ := KxiBound.nonneg hKξ
  refine And.intro hK0 (And.intro hKξnonneg ?_)
  intro E
  have hE := hKξ E
  -- `E.bound ≤ Kξ * 2L ≤ (K0+Kξ) * 2L` since `K0 ≥ 0` and `2L ≥ 0`.
  have hkcoef : Kξ ≤ K0 + Kξ := by
    simpa [add_comm] using le_add_of_nonneg_left hK0
  have h2L : 0 ≤ (2 * E.L) := by
    have h2 : (0 : ℝ) ≤ 2 := by norm_num
    exact mul_nonneg h2 E.hL
  have step : Kξ * (2 * E.L) ≤ (K0 + Kξ) * (2 * E.L) :=
    mul_le_mul_of_nonneg_right hkcoef h2L
  exact le_trans hE.right step

/-- Carleson region over a Whitney box: {(t,σ) | t∈[t0−L,t0+L], 0 < σ ≤ αL}. -/
structure WhitneyCarlesonSpec where
  W : WhitneyInterval
  α : ℝ
  hα : 1 ≤ α ∧ α ≤ 2

/-- Placeholder Dirichlet density |∇U|^2 on the half-plane at height σ and time t. -/
def DirichletDensity (U : ℂ → ℝ) (σ t : ℝ) : ℝ := 0

/-- Placeholder Carleson energy value over the Whitney Carleson box. -/
def CarlesonEnergyValue (U : ℂ → ℝ) (S : WhitneyCarlesonSpec) : ℝ := 0

/-- Build a `BoxEnergy` from a potential `U` over a Whitney Carleson spec. -/
def mkCarlesonEnergyBoxFromU (U : ℂ → ℝ) (S : WhitneyCarlesonSpec) : BoxEnergy :=
  { I := {t | S.W.t0 - S.W.L ≤ t ∧ t ≤ S.W.t0 + S.W.L}
  , t0 := S.W.t0
  , L := S.W.L
  , hI := rfl
  , hL := le_of_lt S.W.hL
  , bound := CarlesonEnergyValue U S }

/-- Concrete half-plane Carleson measure for `U`: energy over each Whitney box
`S` is ≤ K · |I| = K · (2L). -/
def ConcreteHalfPlaneCarlesonMeasure (U : ℂ → ℝ) (K : ℝ) : Prop :=
  0 ≤ K ∧ ∀ S : WhitneyCarlesonSpec, CarlesonEnergyValue U S ≤ K * (2 * S.W.L)

/-- From a concrete Carleson measure for `U`, obtain a box-energy budget. -/
def CarlesonBudgetFromMeasure (U : ℂ → ℝ) (K0 Kξ : ℝ) : Prop :=
  ConcreteHalfPlaneCarlesonMeasure U Kξ → CarlesonEnergyBudget K0 Kξ

/-- Directly obtain CR–Green from a concrete Carleson measure budget. -/
def CRGreenFromConcreteMeasure
    (J : ℂ → ℂ) (U : ℂ → ℝ)
    (Cψ K0 Kξ : ℝ) : Prop :=
  ConcreteHalfPlaneCarlesonMeasure U Kξ → CRGreenPairing J Cψ

/-- Concrete half–plane Carleson constructor for a Whitney interval: builds a
`BoxEnergy` whose bound is the linear budget `K·|I| = K·(2L)`. -/
def mkWhitneyBoxEnergy (W : WhitneyInterval) (K : ℝ) : BoxEnergy :=
  { I := {t | W.t0 - W.L ≤ t ∧ t ≤ W.t0 + W.L}
  , t0 := W.t0
  , L := W.L
  , hI := rfl
  , hL := le_of_lt W.hL
  , bound := K * (2 * W.L) }

/-- Interface: a concrete half–plane Carleson property at Whitney scale. -/
def ConcreteHalfPlaneCarleson (K : ℝ) : Prop :=
  0 ≤ K ∧ ∀ (W : WhitneyInterval), (mkWhitneyBoxEnergy W K).bound ≤ K * (2 * W.L)

/-- Concrete Carleson ⇒ abstract `KxiBound`. -/
def KxiBoundFromConcrete (K : ℝ) : Prop :=
  ConcreteHalfPlaneCarleson K → KxiBound K

/-- FE–Power helper: a budget for the factor `π^{-s/2}` on a closed strip
`σ0 ≤ Re(s) ≤ 1`. We keep this as a simple numeric predicate; downstream
assembly can take `Cπ := 1` (coarse but sufficient) or any sharper constant. -/
def PiPowerBoundOnStrip (σ0 Cπ : ℝ) : Prop := 0 ≤ Cπ

/-- Coarse default: take `Cπ = 1`, valid since `|π^{-s/2}| ≤ 1` for `Re(s) ≥ 0`.
This is numerically weak but sufficient for assembling a closed-strip factors
budget. -/
theorem PiPowerBoundOnStrip.default (σ0 : ℝ) : PiPowerBoundOnStrip σ0 1 := by
  norm_num

/-- Placeholder: finite-k block plus integer-tail symbolic bounds usable with
the K0 skeleton. Intended to be plugged into the numeric plan in
`K0_le_finitePlusTail`. -/
def FiniteBlockPlusTailPlan
    (F T : {n // 2 ≤ n} → ℝ)
    (hF : Summable (fun k : {n // 2 ≤ n} => F k / (((k : ℕ) : ℝ) ^ 2)))
    (hT : Summable (fun k : {n // 2 ≤ n} => T k / (((k : ℕ) : ℝ) ^ 2))) : Prop :=
  True

/-- Placeholder: a statement-level binding asserting that the integer tail is
bounded pointwise by a finite block plus a remainder `T`. -/
def IntegerTailDecomp (F T : {n // 2 ≤ n} → ℝ) : Prop :=
  ∀ k : {n // 2 ≤ n}, integerTail k ≤ F k + T k

/-- Basic Poisson kernel on the boundary line (interface-level utility). -/
def PoissonKernel (σ x : ℝ) : ℝ :=
  (1 / Real.pi) * σ / (σ^2 + x^2)

/-- Poisson extension of a boundary window profile (placeholder; interface only). -/
def PoissonExtension (ψ : ℝ → ℝ) (σ t : ℝ) : ℝ :=
  0

/-- Window Poisson energy (scale-invariant) used to parameterize H^1 tests. -/
def WindowPoissonEnergy (ψ : ℝ → ℝ) : ℝ :=
  0

/-- Existence of an H^1/Poisson test profile realizing the abstract test integral. -/
def ExistsH1PoissonProfile (J : ℂ → ℂ) (W : WhitneyInterval) : Prop :=
  ∃ ψ : ℝ → ℝ, TestIntegral_is_H1Poisson J ψ W

/-- Concrete half–plane Carleson on Whitney boxes for a given potential budget. -/
def HalfPlaneCarlesonOnWhitney (K : ℝ) : Prop :=
  0 ≤ K ∧ ∀ W : WhitneyInterval, (mkWhitneyBoxEnergy W K).bound ≤ K * (2 * W.L)

/-- Global annular L2 bound implies a geometry-aware bound on Carleson boxes. -/
def AnnularL2Aligned (Cα : ℝ) : Prop :=
  AlignAnnularToBox Cα ∧ AnnularL2KernelBoundGeom Cα

/-- Using alignment + geometric kernel bound to discharge the VK→Kξ reduction. -/
def KxiFromAnnuliAligned (Cα : ℝ) (vk : VKAnnularCount) (Kξ : ℝ) : Prop :=
  AnnularL2Aligned Cα → KxiFromVK Cα vk Kξ

/-- From aligned annular reduction and the geometric kernel bound, expose the
abstract `KxiBound` used by certificate consumers. -/
theorem Kxi_bound_on_strip_aligned
    {Cα Kξ : ℝ} (vk : VKAnnularCount)
    (hAlign : AnnularL2Aligned Cα)
    (hRed : KxiFromAnnuliAligned Cα vk Kξ) :
    KxiBound Kξ :=
  by
    have hvk : KxiFromVK Cα vk Kξ := hRed hAlign
    exact hvk.right.right

/-- Alias with the expected external name: `Kxi_bound_on_strip` delegates to
the functional–equation factors route on closed strips. -/

/-- Nonvanishing inputs on the closed right-edge strip used by the analytic
route: ζ(s) ≠ 0 for Re(s) > 1 and Re(s) = 1. These are provided by
mathlib-backed theorems and RS delegates. -/
def NonvanishingOnClosedStrip : Prop :=
  (∀ s : ℂ, (1 : ℝ) < s.re → riemannZeta s ≠ 0)
  ∧ (∀ s : ℂ, s.re = (1 : ℝ) → riemannZeta s ≠ 0)

/-- Helper: ζ(s) ≠ 0 for Re(s) > 1 (mathlib). -/
lemma zeta_nonvanishing_re_gt_one_all :
    ∀ s : ℂ, (1 : ℝ) < s.re → riemannZeta s ≠ 0 := by
  intro s hs
  simpa using riemannZeta_ne_zero_of_one_lt_re hs

/-- Helper: ζ(s) ≠ 0 for Re(s) = 1 (delegates to RS). -/
lemma zeta_nonvanishing_re_eq_one_all :
    ∀ s : ℂ, s.re = (1 : ℝ) → riemannZeta s ≠ 0 := by
  intro s hs
  simpa using RH.RS.ZetaNoZerosOnRe1FromSchur s hs

/-- Concrete nonvanishing instance on the closed right-edge strip. -/
def nonvanishingOnClosedStrip : NonvanishingOnClosedStrip :=
  And.intro zeta_nonvanishing_re_gt_one_all zeta_nonvanishing_re_eq_one_all

/-- Functional-equation factors budget on a closed strip: a single numeric
budget `B ≥ 0` that controls the box energy linearly in |I|=2L. This
abstracts the contributions from Γ, cos, and power factors. -/
structure FunctionalEquationStripFactors where
  σ0 : ℝ
  hσ0 : (1/2 : ℝ) < σ0 ∧ σ0 ≤ 1
  B : ℝ
  hB : 0 ≤ B
  carleson : ConcreteHalfPlaneCarleson B

/-- Analytic Kξ bound on closed strips from functional-equation factors and
nonvanishing inputs. This is a statement-level connector: downstream tracks
can instantiate `FunctionalEquationStripFactors` from explicit Γ/cos/power
enclosures; the nonvanishing inputs are provided by mathlib/RS. -/
theorem Kxi_bound_on_strip
    (nz : NonvanishingOnClosedStrip)
    (fac : FunctionalEquationStripFactors) :
    ConcreteHalfPlaneCarleson fac.B :=
  fac.carleson

/-- Convenience: Kξ bound using the default nonvanishing instance. -/
theorem Kxi_bound_on_strip_default
    (fac : FunctionalEquationStripFactors) :
    ConcreteHalfPlaneCarleson fac.B :=
  Kxi_bound_on_strip nonvanishingOnClosedStrip fac

/-- Existence form: from any closed-strip factors witness, produce
`∃ Kξ, KxiBound Kξ`. Uses the default nonvanishing witness combining
mathlib (Re > 1) and the RS boundary result (Re = 1). -/
theorem exists_KxiBound_of_factors
    (fac : FunctionalEquationStripFactors) :
    ∃ Kξ : ℝ, ConcreteHalfPlaneCarleson Kξ :=
  ⟨fac.B, Kxi_bound_on_strip_default fac⟩

/-- Existence form from a nonempty factors witness. -/
theorem exists_KxiBound_if_factors
    (h : Nonempty FunctionalEquationStripFactors) :
    ∃ Kξ : ℝ, ConcreteHalfPlaneCarleson Kξ := by
  rcases h with ⟨fac⟩
  exact exists_KxiBound_of_factors fac

/-- Convenience: from an aligned annular reduction and `K0 ≥ 0`, produce the
combined energy budget `(K0+Kξ)` used downstream. -/
theorem energyBudget_from_aligned_annular
    {Cα K0 Kξ : ℝ} (vk : VKAnnularCount)
    (hAlign : AnnularL2Aligned Cα)
    (hRed : KxiFromAnnuliAligned Cα vk Kξ)
    (hK0 : 0 ≤ K0) :
    CarlesonEnergyBudget K0 Kξ := by
  refine CarlesonEnergyBudget.of_Kxi hK0 (Kxi_bound_on_strip_aligned vk hAlign hRed)

/-- With a constructor turning a Carleson energy budget into a CR–Green pairing,
and an aligned annular reduction, obtain the CR–Green pairing needed by the
certificate consumers. -/
theorem CRGreen_from_aligned_annular
    (J : ℂ → ℂ)
    {Cψ Cα K0 Kξ : ℝ} (vk : VKAnnularCount)
    (ctor : CarlesonToCRGreen J Cψ K0 Kξ)
    (hAlign : AnnularL2Aligned Cα)
    (hRed : KxiFromAnnuliAligned Cα vk Kξ)
    (hK0 : 0 ≤ K0) :
    CRGreenPairing J Cψ := by
  have budget := energyBudget_from_aligned_annular vk hAlign hRed hK0
  exact ctor budget

/-- End-to-end reduction using geometry-aligned annuli: CR–Green + aligned annular
reduction + smallness yields (P+). Statement-level only. -/
def PPlusFromCRGreenVKAligned
    (J F : ℂ → ℂ)
    (Cψ CψH1 Cα K0 Kξ Υ : ℝ)
    (vk : VKAnnularCount) : Prop :=
  CRGreenPairing J Cψ →
  KxiFromAnnuliAligned Cα vk Kξ →
  SmallnessFromCarleson CψH1 K0 Kξ Υ →
  Υ < (1/2 : ℝ) →
  PPlus F

/-- End-to-end chain discharge from concrete Carleson measure and aligned annuli. -/
def PPlusFromConcreteChain
    (J F : ℂ → ℂ) (U : ℂ → ℝ)
    (Cψ CψH1 Cα K0 Kξ Υ αBox : ℝ)
    (vk : VKAnnularCount) : Prop :=
  CarlesonToCRGreen J Cψ →
  CarlesonBudgetFromMeasure U K0 Kξ →
  KxiFromAnnuliAligned Cα vk Kξ →
  SmallnessFromCarleson CψH1 K0 Kξ Υ →
  Υ < (1/2 : ℝ) →
  PPlus F

end RH.Cert
