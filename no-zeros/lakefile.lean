import Lake
open Lake DSL

package «riemann» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]
  -- Build optimizations for performance
  buildType := BuildType.release
  -- Parallel compilation (uncomment and adjust for your CPU cores)
  -- moreLeanArgs := #["-j8"] -- Enable if you have 8+ CPU cores
  -- Enable incremental compilation
  -- moreGlobalServerArgs := #["--worker-pool-size=8"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.13.0"

-- Local dependency on no-mathlib-core removed since it was moved to archive

@[default_target]
lean_lib «rh» where
  -- Restrict build to certificate-route modules and their AF support to reduce build surface
  globs := #[
    -- Academic framework core
    `rh.academic_framework.CompletedXi,
    `rh.academic_framework.CayleyAdapters,
    `rh.academic_framework.DiskHardy,
    `rh.academic_framework.PoissonCayley,
    `rh.academic_framework.HalfPlaneOuterV2,
    -- RS layer used by certificate route
    `rh.RS.Cayley,
    `rh.RS.Det2Outer,
    `rh.RS.OffZerosBridge,
    `rh.RS.XiExtBridge,
    `rh.RS.SchurGlobalization,
    `rh.RS.PinchWrappers,
    `rh.RS.PinchIngredients,
    `rh.RS.RouteB_Final,
    `rh.RS.CertificateConstruction,
    -- Proof entry
    `rh.Proof.Main,
    `rh.Proof.Export,
    `rh.Proof.DOI
  ]

-- Test library for verification and validation
lean_lib «test» where
  globs := #[.submodules `test]
