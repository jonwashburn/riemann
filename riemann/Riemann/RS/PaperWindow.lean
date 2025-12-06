import Mathlib.Data.Real.Basic

/-!
# Paper Window ψ (non-sealed)

This module provides a lightweight, axiom-free definition of the paper window `ψ`.
It preserves the interface name `psi_paper` without depending on sealed modules.

Properties such as smoothness are not required by downstream code paths that only
use `ψ` as a bounded, compactly supported weight in boundary integrals.
-/

namespace RH
namespace RS
namespace PaperWindow

open Real

/-- A simple even, compactly supported window with a plateau on [-1,1] and linear
ramps on [1,2] and [-2,-1]. Values are in [0,1]. -/
noncomputable def psi_paper (t : ℝ) : ℝ :=
  if |t| ≤ 1 then 1
  else if |t| ≥ 2 then 0
  else if 1 < t then 2 - t
  else t + 2

end PaperWindow
end RS
end RH
