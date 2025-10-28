import Lake
open Lake DSL

package «riemann» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]
  buildType := BuildType.release

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.12.0"

lean_lib «rh» where
  globs := #[
    .submodules `rh.academic_framework,
    .submodules `rh.RS,
    .submodules `rh.Cert,
    .submodules `rh.Proof
  ]

lean_lib rh_export where
  roots := #[
    -- keep export closure minimal and guard-friendly
    `rh.Proof.Export
  ]

@[default_target]
lean_lib rh_routeb_dev where
  roots := #[
    `rh.Compat,
    `rh.academic_framework.CayleyAdapters,
    `rh.academic_framework.PoissonCayley,
    `rh.RS.WhitneyAeCore,
    `rh.RS.PinchWrappers
  ]

-- Optional: full export surface including the unconditional wrapper. Not built by default.
lean_lib rh_export_unconditional where
  roots := #[
    `rh.Proof.Export
  ]
