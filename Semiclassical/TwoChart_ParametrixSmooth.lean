/******************************************************************************
  TwoChart_ParametrixSmooth

  This file is the smooth-variant wrapper around `TwoChart_ParametrixRecursion`.

  The core recursion in `TwoChart_ParametrixRecursion.lean` is formulated using a
  hypothesis `MixedComm a`, which was introduced only to avoid pulling in heavy
  multivariable smoothness machinery.

  After the upgrade in `TwoChart_SmoothUpgrade.lean`, we can express the
  same recursion under a more standard hypothesis: `ContDiffOn` of the symbol on
  `Y ×ˢ univ`, and we derive `MixedComm` from it.
*******************************************************************************/

import TwoChart_ParametrixRecursion
import TwoChart_SmoothUpgrade

open scoped BigOperators

namespace TwoChart

variable {Y : Set ℝ} {λ : ℝ}

/-!
## Smooth recursion data

We mirror `TwoChart.RecData` but replace the `MixedComm` field by a `ContDiffOn`
smoothness field.
-/

structure RecDataSmooth (Y : Set ℝ) (λ : ℝ) where
  a : ℝ → ℝ → ℝ → ℂ
  m : ℝ
  ha : SmLambda a m Y λ
  hEll : EllipticOp a m Y λ
  hsmooth : SmoothOn Y a

namespace RecDataSmooth

variable {d : RecDataSmooth Y λ}

noncomputable def toRecData (d : RecDataSmooth Y λ) : RecData (Y := Y) (λ := λ) :=
  { a := d.a
    m := d.m
    ha := d.ha
    hEll := d.hEll
    hComm := (SmoothOn.mixedComm (Y := Y) d.hsmooth) }

theorem toRecData_a : (toRecData (Y := Y) (λ := λ) d).a = d.a := rfl
theorem toRecData_m : (toRecData (Y := Y) (λ := λ) d).m = d.m := rfl

end RecDataSmooth

/-!
## Parametrix symbol under smoothness

All symbol-level conclusions are inherited by conversion to `RecData`.
-/

noncomputable def parametrixSymbolSmooth
    (d : RecDataSmooth Y λ) (N : ℕ) : ℝ → ℝ → ℝ → ℂ :=
  TwoChart.parametrixSymbol (d := d.toRecData) N

theorem parametrixSymbolSmooth_mem
    (d : RecDataSmooth Y λ) (N : ℕ) :
    SmLambda (parametrixSymbolSmooth (Y := Y) (λ := λ) d N) (-d.m) Y λ := by
  -- This is exactly `parametrixSymbol_mem` for `d.toRecData`.
  simpa [parametrixSymbolSmooth, RecDataSmooth.toRecData_m]
    using (TwoChart.parametrixSymbol_mem (d := d.toRecData) N)

end TwoChart
