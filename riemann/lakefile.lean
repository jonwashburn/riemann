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
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.13.0"

@[default_target]
lean_lib «rh» where
  srcDir := "no-zeros"
  roots := #[
    `rh.RS.RouteBPinnedRemovable,
    `rh.RS.RouteB_Final,
    `rh.RS.CertificateConstruction
  ]
