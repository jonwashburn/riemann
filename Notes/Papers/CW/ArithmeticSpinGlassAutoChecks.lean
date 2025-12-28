import Notes.Papers.CW.ArithmeticSpinGlass
import Notes.Papers.CW.AutoFormalizer

/-!
# AutoFormalizer protocol checks for `ArithmeticSpinGlass.lean`

This file is meant to be built in CI, e.g.

`lake build Notes.Papers.CW.ArithmeticSpinGlassAutoChecks`
-/

namespace ArithmeticSpinGlassAutoChecks

/-! A tiny diamond-shaped inheritance graph to exercise `#diamond_check`. -/
namespace DiamondSmoke

class A where
  a : Nat

class B extends A where
  b : Nat

class C extends A where
  c : Nat

class D extends B, C where
  d : Nat

#diamond_check D

end DiamondSmoke

/-!
Run the oracle on structures/classes that `ArithmeticSpinGlass.lean` actually depends on.

In particular, the main theorem uses the Gaussian Hilbert model assumptions `IsGaussianHilbert`.
-/
open _root_.PhysLean.Probability.GaussianIBP

#diamond_check IsGaussianHilbert
#diamond_check HasModerateGrowth

end ArithmeticSpinGlassAutoChecks
