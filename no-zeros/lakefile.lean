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
  globs := #[
    .one `rh.Compat,
    .submodules `rh.academic_framework,
    .submodules `rh.RS,
    .submodules `rh.Cert,
    .submodules `rh.Proof
  ]

lean_lib test where
  globs := #[.submodules `test]
