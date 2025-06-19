import Lake
open Lake DSL

package «riemann-hypothesis» where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.10.0"

lean_lib «RiemannHypothesis» where
  -- add library configuration options here

lean_lib «RH» where
  srcDir := "rh"
  roots := #[`Placeholders, `Common, `Infrastructure, `DiagonalArithmeticHamiltonian, `FredholmDeterminant,
             `DeterminantProofsFinal, `FredholmVanishingEigenvalue, `DiagonalOperatorComponents,
             `PrimeRatioNotUnity, `EigenvalueStabilityComplete, `DeterminantIdentityCompletion,
             `ZetaFunctionalEquation, `FredholmDeterminantProofs, `DiagonalArithmeticHamiltonianProof1,
             `DiagonalArithmeticHamiltonianProof2Simple, `DeterminantProofsFinalComplete,
             `DeterminantIdentityCompletionProof, `EigenvalueStabilityCompleteProof,
             `FredholmVanishingEigenvalueProof, `PrimeRatioNotUnityProofs]

@[default_target]
lean_exe «riemann-hypothesis» where
  root := `Main
