import Lake
open Lake DSL

package riemann where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.13.0"

-- Build everything with v4.13.0
@[default_target]
lean_lib rh where
  roots := #[
    `rh.Proof.Main,
    `rh.RS.SchurGlobalization,
    `rh.Cert.KxiWhitney,
    `rh.RS.OffZerosBridge,
    `rh.RS.Cayley,
    `rh.RS.PinchCertificate,
    `rh.RS.RouteB_Final,
    `rh.RS.RouteBPinnedRemovable,
    `rh.RS.CertificateConstruction,
    `rh.RS.PinchIngredients,
    `rh.RS.XiExtBridge,
    `rh.RS.Domain,
    `rh.RS.Det2Outer,
    `rh.RS.PoissonAI,
    `rh.RS.CRGreenOuter,
    `rh.RS.WhitneyGeometryDefs,
    `rh.RS.WhitneyAeCore,
    `rh.Cert.KxiPPlus,
    `rh.academic_framework.EulerProductMathlib,
    `rh.academic_framework.EulerProduct.K0Bound,
    `rh.academic_framework.EulerProduct.PrimeSeries,
    `rh.academic_framework.ZetaFunctionalEquation,
    `rh.academic_framework.CompletedXi,
    `rh.academic_framework.CompletedXiSymmetry,
    `rh.academic_framework.ComplexAlgebraNorms,
    `rh.academic_framework.DiskHardy,
    `rh.academic_framework.DiagonalFredholm.Determinant,
    `rh.academic_framework.DiagonalFredholm.WeierstrassProduct,
    `rh.academic_framework.HalfPlaneOuterV2,
    `rh.academic_framework.MeasureHelpers,
    `rh.academic_framework.GammaBounds,
    `rh.academic_framework.ConstructiveOuter,
    `rh.academic_framework.PoissonCayley,
    `rh.academic_framework.CayleyAdapters,
    `rh.Compat
  ]

-- Minimal active track: just the top assembly module
lean_lib «rh_active» where
  roots := #[`rh.Proof.Active]

lean_lib test where
  globs := #[.submodules `test]
