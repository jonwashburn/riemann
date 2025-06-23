import Lake
open Lake DSL

package riemann where
  -- add any package configuration options here

@[default_target]
lean_lib «riemann» where
  -- set the root module to Main.lean and include Common
  roots := #[`Main, `CommonShim]

lean_lib «RH» where
  -- set the root module for the RH library
  globs := #[.submodules `rh]

-- Add no-mathlib-core as a local library
lean_lib «NoMathlibCore» where
  srcDir := "no-mathlib-core"
  roots := #[`Main, `RecognitionScience, `Core, `Foundations]
  globs := #[.submodules `Core, .submodules `Foundations]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.12.0"
