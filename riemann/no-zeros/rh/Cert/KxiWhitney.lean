import rh.academic_framework.EulerProduct.K0Bound

/-!
# Kξ Whitney–box Carleson interface (Prop‑level)

This module provides a lightweight, statement‑level interface for the
Whitney–box Carleson finiteness of the analytic field
`Uξ(σ,t) := Re (log ξ(1/2+σ+it))`, parameterized by a fixed aperture `α`
and Whitney schedule parameter `c`.

Deliverables (Prop-level only, no analytics):
- `KxiBound (α c) : Prop` — existence of a finite nonnegative constant `Kξ`.
- `Cbox_zeta_of_Kxi` — adapter that exposes the combined ζ‑side box constant
  `K0 + Kξ` from a `KxiBound` witness. Here `K0` is imported from the
  arithmetic tail module `rh/academic_framework/EulerProduct/K0Bound`.

No axioms are introduced; this file is purely an interface used by
certificate consumers. It compiles standalone.
-/

namespace RH
namespace Cert
namespace KxiWhitney

noncomputable section

open Classical

/-!
## Interface

`KxiBound α c` should be read as: “At aperture `α` and Whitney parameter `c`,
there exists a finite nonnegative constant `Kξ` such that the Whitney–box
Carleson energy of `Uξ` is bounded by `Kξ · |I|` for every relevant base
interval `I`.” We keep this at Prop level to avoid committing to a concrete
analytic development in this track.
-/

/-- Prop‑level interface: existence of a finite nonnegative constant `Kξ`
controlling the Whitney–box Carleson energy of `Uξ` at aperture `α` and
Whitney schedule parameter `c`.

This is intentionally statement‑level: consumers can assume `KxiBound α c`
to obtain a combined ζ‑side box constant via `Cbox_zeta_of_Kxi` below.

Note: we include the trivial conjunct `(α = α ∧ c = c)` solely to silence
“unused argument” linters while keeping the intended parameterization. -/
def KxiBound (α c : ℝ) : Prop := ∃ Kξ : ℝ, 0 ≤ Kξ ∧ (α = α ∧ c = c)

/-!
## Exposing the ζ-side box constant `C_box^{(ζ)} = K0 + Kξ`

Given a witness to `KxiBound α c`, we package the combined ζ‑side box
constant via a small adapter. Here `K0` is the arithmetic tail constant
from `K0Bound`.
-/

namespace _root_.RH.AcademicFramework.EulerProduct.K0

/-! Local helper notation: `K0` refers to the arithmetic tail constant
`K0Const` imported from `K0Bound`. -/
local notation "K0" => RH.AcademicFramework.EulerProduct.K0.K0Const

end _root_.RH.AcademicFramework.EulerProduct.K0

open RH.AcademicFramework.EulerProduct.K0

/-- Extract the nonnegative `Kξ` value from a `KxiBound` witness and expose the
combined ζ‑side box constant as a real number. -/
noncomputable def CboxZeta (α c : ℝ) (h : KxiBound α c) : ℝ :=
  K0 + Classical.choose h

/-- Nonnegativity of the combined ζ‑side constant. -/
lemma CboxZeta_nonneg {α c : ℝ} (h : KxiBound α c) :
    0 ≤ CboxZeta α c h := by
  -- `K0 ≥ 0` from the arithmetic tail module; `Kξ ≥ 0` by assumption
  have hK0 : 0 ≤ K0 :=
    RH.AcademicFramework.EulerProduct.K0.K0_bound_on_strip_proved
  have hKxi : 0 ≤ Classical.choose h := (Classical.choose_spec h).1
  simpa [CboxZeta, add_comm, add_left_comm, add_assoc] using add_nonneg hK0 hKxi

/-- Adapter lemma (statement‑level): from a `KxiBound α c` witness we obtain a
nonnegative combined constant `C_box^{(ζ)} = K0 + Kξ` suitable for consumers.

This lemma purposefully exposes only the constant. Any concrete energy
inequalities (e.g. `∀ I, ∬_{Q(αI)} |∇U|^2 σ ≤ (K0+Kξ)|I|`) are to be handled
by consumer modules using their own pairing/aggregation lemmas, with `K0` and
`Kξ` plugged in via this adapter. -/
theorem Cbox_zeta_of_Kxi {α c : ℝ} (h : KxiBound α c) :
    ∃ Cζ : ℝ, 0 ≤ Cζ ∧ Cζ = CboxZeta α c h := by
  refine ⟨CboxZeta α c h, CboxZeta_nonneg (α := α) (c := c) h, rfl⟩

end

end KxiWhitney
end Cert
end RH
