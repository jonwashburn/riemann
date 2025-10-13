import Lake
open Lake DSL

package «sandbox_det2» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.13.0"

@[default_target]
lean_lib «sandbox_det2» where
  globs := #[.submodules `sandbox_det2]
