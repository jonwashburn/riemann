import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import rh.Cert.KxiPPlus
import rh.RS.BoundaryWedge
import rh.RS.CRGreenOuter
import rh.RS.PoissonPlateau
import rh.RS.TentShadow

/-!
RS bridge: Concrete Carleson ⇒ (P+).

We implement the *analytic* bridge requested:

* Use the CR–Green pairing inequality together with the Whitney remainder
  control (from `CRGreenOuter`) to obtain the boundary pairing bound with a
  square‑root Carleson right‑hand side on each Whitney rectangle.
* Use the uniform Poisson test‑energy bound and the fixed plateau window with a
  strictly positive lower constant `c₀` (from `PoissonPlateau`) to feed the
  H¹–BMO window criterion.
* Push the Carleson box‑energy budget `Kξ` through the above to conclude the
  Whitney wedge `(P+)` and then the a.e. boundary wedge.

This file exposes two names that downstream code already depends on:

* `PPlus_of_ConcreteHalfPlaneCarleson` — the non‑existence‑level form.
* `PPlusFromCarleson_exists_proved`     — the existence‑level bundle
   `(∃ Kξ ≥ 0, Carleson Kξ) → (P+)`.

No axioms and no `sorry`.
-/

noncomputable section

open Complex

namespace RH
namespace RS

/-- Analytic local wedge from a concrete nonnegative half–plane Carleson budget.

This packages the CR–Green pairing/remainder machinery and the Poisson plateau
window into the Whitney local→global wedge alias
`localWedge_from_WhitneyCarleson (F := F)`.

Cross-link: the H¹–BMO window step is provided by
`RH.RS.H1BMOWindows.windowed_phase_bound_of_carleson`, consumed via the façade
`localWedge_from_pairing_and_uniformTest`. -/
theorem localWedge_from_CRGreen_and_Poisson
    (F : ℂ → ℂ)
    (hex : ∃ Kξ : ℝ, 0 ≤ Kξ ∧ RH.Cert.ConcreteHalfPlaneCarleson Kξ) :
    localWedge_from_WhitneyCarleson (F := F) hex := by
  classical
  rcases hex with ⟨Kξ, hKξ0, hCar⟩
  -- Plateau window and positive Poisson lower constant.
  obtain ⟨ψ, _hψ_even, _hψ_nonneg, _hψ_comp, _hψ_mass1,
          ⟨c0, hc0_pos, hPlateau⟩⟩ := RH.RS.poisson_plateau_c0
  -- Feed CR–Green pairing + Whitney remainder packaging, pushed through the Carleson budget.
  -- The H¹–BMO window criterion (in `H1BMOWindows`) is consumed behind the façade
  -- lemma exported by the glue layer.
  --
  -- Concretely, we use the adapter
  -- `local_pairing_bound_from_Carleson_budget` (from `BoundaryWedge`)
  -- as the `pairing` ingredient, and the plateau witness `⟨c0, …⟩` as the
  -- positivity ingredient for the Poisson transport on the boundary.
  --
  -- The `localWedge_from_pairing_and_uniformTest` façade (from `BoundaryWedge`)
  -- wraps the H¹–BMO windows argument, so using it here completes the local wedge.
  -- Package the Carleson existence into a named variable for reuse below
  let hKxiVar : ∃ Kξ : ℝ, 0 ≤ Kξ ∧ RH.Cert.ConcreteHalfPlaneCarleson Kξ := ⟨Kξ, hKξ0, hCar⟩
  exact
    localWedge_from_pairing_and_uniformTest
      (α := (1 : ℝ)) (ψ := ψ) (F := F)
      (hKxi := hKxiVar)
      (pairing :=
        fun {lenI : ℝ}
            (U : ℝ × ℝ → ℝ) (W : ℝ → ℝ) (_ψ : ℝ → ℝ) (χ : ℝ × ℝ → ℝ)
            (I : Set ℝ) (α' : ℝ)
            (σ : MeasureTheory.Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ))
            (gradU gradChiVpsi : (ℝ × ℝ) → ℝ × ℝ) (B : ℝ → ℝ)
            (Cψ_pair Cψ_rem : ℝ)
            (hPairVol :
              |∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ|
                ≤ Cψ_pair * Real.sqrt (RS.boxEnergy gradU σ Q))
            (Rside Rtop Rint : ℝ)
            (hEqDecomp :
              (∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ)
                = (∫ t in I, _ψ t * B t) + Rside + Rtop + Rint)
            (hSideZero : Rside = 0) (hTopZero : Rtop = 0)
            (hRintBound :
              |Rint| ≤ Cψ_rem * Real.sqrt (RS.boxEnergy gradU σ Q))
            (hCψ_nonneg : 0 ≤ Cψ_pair + Cψ_rem)
            (hEnergy_le : RS.boxEnergy gradU σ Q ≤ (Classical.choose hKxiVar) * lenI) =>
          -- recover the Carleson witness for (Classical.choose hKxiVar)
          have hCar' : RH.Cert.ConcreteHalfPlaneCarleson (Classical.choose hKxiVar) :=
            (Classical.choose_spec hKxiVar).2
          RS.local_pairing_bound_from_IBP_and_Carleson
            (Kξ := Classical.choose hKxiVar) (lenI := lenI) (hCar := hCar')
            U W _ψ χ I α' σ Q gradU gradChiVpsi B Cψ_pair Cψ_rem
            (hPairVol := hPairVol)
            (Rside := Rside) (Rtop := Rtop) (Rint := Rint)
            (hEqDecomp := hEqDecomp)
            (hSideZero := hSideZero) (hTopZero := hTopZero)
            (hRintBound := hRintBound)
            (hCψ_nonneg := hCψ_nonneg)
            (hEnergy_le := hEnergy_le))
      (plateau := ⟨c0, hc0_pos, hPlateau⟩)

/-- Analytic local wedge with Poisson AI: use the AI-based coercivity lemma. -/
theorem localWedge_from_CRGreen_and_Poisson_AI
    (F : ℂ → ℂ)
    (hex : ∃ Kξ : ℝ, 0 ≤ Kξ ∧ RH.Cert.ConcreteHalfPlaneCarleson Kξ)
    (hAI : ∀ᵐ x : ℝ,
      Filter.Tendsto (fun b : ℝ => RH.RS.poissonSmooth F b x)
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (RH.RS.boundaryRe F x))) :
    localWedge_from_WhitneyCarleson (F := F) hex := by
  classical
  rcases hex with ⟨Kξ, hKξ0, hCar⟩
  -- Plateau window and strictly positive lower bound
  obtain ⟨ψ, _hψ_even, _hψ_nonneg, _hψ_comp, _hψ_mass1,
          ⟨c0, hc0_pos, hPlateau⟩⟩ := RH.RS.poisson_plateau_c0
  -- Pairing ingredient via CR–Green + Carleson budget
  have pairing :
      ∀ {lenI : ℝ}
        (U : ℝ × ℝ → ℝ) (W : ℝ → ℝ) (_ψ : ℝ → ℝ) (χ : ℝ × ℝ → ℝ)
        (I : Set ℝ) (α' : ℝ)
        (σ : MeasureTheory.Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ))
        (gradU gradChiVpsi : (ℝ × ℝ) → ℝ × ℝ) (B : ℝ → ℝ)
        (Cψ_pair Cψ_rem : ℝ)
        (hPairVol :
          |∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ|
            ≤ Cψ_pair * Real.sqrt (RS.boxEnergy gradU σ Q))
        (Rside Rtop Rint : ℝ)
        (hEqDecomp :
          (∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ)
            = (∫ t in I, _ψ t * B t) + Rside + Rtop + Rint)
        (hSideZero : Rside = 0) (hTopZero : Rtop = 0)
        (hRintBound : |Rint| ≤ Cψ_rem * Real.sqrt (RS.boxEnergy gradU σ Q))
        (hCψ_nonneg : 0 ≤ Cψ_pair + Cψ_rem)
        (hEnergy_le : RS.boxEnergy gradU σ Q ≤ Kξ * lenI),
        |∫ t in I, _ψ t * B t|
          ≤ (Cψ_pair + Cψ_rem) * Real.sqrt (Kξ * lenI) :=
    by
      intro lenI U W _ψ χ I α' σ Q gradU gradChiVpsi B Cψ_pair Cψ_rem hPairVol Rside Rtop Rint hEqDecomp hSideZero hTopZero hRintBound hCψ_nonneg hEnergy_le
      exact
        RS.local_pairing_bound_from_IBP_and_Carleson
          (Kξ := Kξ) (lenI := lenI) (hCar := hCar)
          U W _ψ χ I α' σ Q gradU gradChiVpsi B Cψ_pair Cψ_rem
          (hPairVol := hPairVol)
          (Rside := Rside) (Rtop := Rtop) (Rint := Rint)
          (hEqDecomp := hEqDecomp)
          (hSideZero := hSideZero) (hTopZero := hTopZero)
          (hRintBound := hRintBound)
          (hCψ_nonneg := hCψ_nonneg)
          (hEnergy_le := hEnergy_le)
  -- Coercivity ⇒ (P+) via AI route
  have hCoercive : RH.Cert.PPlus F :=
    whitney_carleson_coercivity_aepos_AI
      (ψ := ψ) (F := F) (Kξ := Kξ) (c0 := c0)
      (hKξ0 := hKξ0) (hCar := hCar) (hc0 := hc0_pos)
      (pairing := pairing)
      (hPlat := by
        intro b x hb hb1 hx
        simpa using (hPlateau (b := b) (x := x) hb hb1 hx))
      (hAI := hAI)
      (ε := (1/2 : ℝ)) (κ := (1/4 : ℝ)) (M := (8 : ℝ))
      (hε := by constructor <;> norm_num)
      (hκ := by constructor <;> norm_num)
      (hM := by norm_num)
  -- Local wedge alias is `(P+)`
  exact hCoercive



/-- Concrete‑constant form: from a nonnegative concrete half–plane Carleson
budget `Kξ` for the boundary field `F`, deduce the boundary wedge `(P+)`. -/
theorem PPlus_of_ConcreteHalfPlaneCarleson
    (F : ℂ → ℂ) {Kξ : ℝ}
    (hKξ0 : 0 ≤ Kξ) (hCar : RH.Cert.ConcreteHalfPlaneCarleson Kξ) :
    RH.Cert.PPlus F := by
  -- Build the local Whitney wedge from CR–Green + plateau + Carleson…
  have hLoc :
      localWedge_from_WhitneyCarleson (F := F) ⟨Kξ, hKξ0, hCar⟩ :=
    localWedge_from_CRGreen_and_Poisson (F := F) ⟨Kξ, hKξ0, hCar⟩
  -- …and apply the a.e. upgrade to obtain the boundary wedge `(P+)`.
  exact ae_of_localWedge_on_Whitney (F := F) ⟨Kξ, hKξ0, hCar⟩ hLoc

/-- Existence‑level bundle: `(∃Kξ ≥ 0, Carleson Kξ) → (P+)`.

This is the statement‑level bridge that downstream code consumes. -/
theorem PPlusFromCarleson_exists_proved
    (F : ℂ → ℂ) : RH.Cert.PPlusFromCarleson_exists F := by
  intro hex
  -- Local wedge via CR–Green + plateau + Carleson:
  have hLoc :
      localWedge_from_WhitneyCarleson (F := F) hex :=
    localWedge_from_CRGreen_and_Poisson (F := F) hex
  -- A.e. upgrade to `(P+)`.
  exact ae_of_localWedge_on_Whitney (F := F) hex hLoc

/-- Existence‑level bundle with Poisson AI: `(∃Kξ ≥ 0, Carleson Kξ) → (P+)`. -/
theorem PPlusFromCarleson_exists_proved_AI
    (F : ℂ → ℂ)
    (hAI : ∀ᵐ x : ℝ,
      Filter.Tendsto (fun b : ℝ => RH.RS.poissonSmooth F b x)
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (RH.RS.boundaryRe F x)))
    : RH.Cert.PPlusFromCarleson_exists F := by
  intro hex
  -- Local wedge via CR–Green + plateau + Carleson + AI
  have hLoc :
      localWedge_from_WhitneyCarleson (F := F) hex :=
    localWedge_from_CRGreen_and_Poisson_AI (F := F) hex hAI
  -- A.e. upgrade to `(P+)`.
  exact ae_of_localWedge_on_Whitney (F := F) hex hLoc

end RS
end RH
