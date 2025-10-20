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
  -- Build certificate-route modules only (CR-outer route excluded due to Whitney errors)
  globs := #[
    .submodules `rh.academic_framework,
    .submodules `rh.RS,
    .submodules `rh.Cert,
    .submodules `rh.Proof
  ]
  excludedModules := #[
    `rh.RS.WhitneyGeometryDefs,
    `rh.RS.WhitneyAeCore,
    `rh.RS.CRGreenOuter
  ]

-- Test library for verification and validation
lean_lib «test» where
  globs := #[.submodules `test]
