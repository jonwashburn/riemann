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
-- Export-only default target (keeps CI surface minimal)
@[default_target]
lean_lib rh where
  -- keep minimal to avoid CRGreenOuter in default build
  roots := #[`rh.Proof.Export]

-- Route B dev target builds the unconditional track
lean_lib rh_routeb_dev where
  -- ensure Route B deps like PinchWrappers are compiled
  roots := #[
    `rh.academic_framework.CayleyAdapters,
    `rh.academic_framework.PoissonCayley,
    `rh.RS.WhitneyAeCore,
    `rh.RS.PinchWrappers,
    `rh.RS.RouteB_Final
  ]

-- Minimal active track: just the top assembly module
lean_lib «rh_active» where
  roots := #[`rh.Proof.Active]

lean_lib test where
  globs := #[.submodules `test]
