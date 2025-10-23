#!/bin/bash

# Test versions systematically
versions=("v4.0.0" "v4.1.0" "v4.2.0" "v4.3.0" "v4.4.0" "v4.5.0" "v4.6.0" "v4.7.0" "v4.8.0" "v4.9.0" "v4.10.0" "v4.11.0" "v4.12.0")

for ver in "${versions[@]}"; do
    echo "========================================="
    echo "Testing mathlib $ver"
    echo "========================================="
    
    # Update lean-toolchain
    echo "leanprover/lean4:$ver" > lean-toolchain
    
    # Update lakefile
    cat > lakefile.lean << EOF
import Lake
open Lake DSL

package «riemann» where
  leanOptions := #[
    ⟨\`pp.unicode.fun, true⟩,
    ⟨\`pp.proofs.withType, false⟩,
    ⟨\`autoImplicit, false⟩,
    ⟨\`relaxedAutoImplicit, false⟩
  ]
  buildType := BuildType.release

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "$ver"

@[default_target]
lean_lib «rh» where
  globs := #[
    .submodules \`rh.academic_framework,
    .submodules \`rh.RS
  ]
EOF
    
    # Update dependencies
    rm -f lake-manifest.json
    if ! lake update 2>&1 | tail -3; then
        echo "FAILED to update for $ver"
        continue
    fi
    
    # Test WeierstrassProduct
    echo "Testing WeierstrassProduct..."
    if lake build rh.academic_framework.DiagonalFredholm.WeierstrassProduct 2>&1 | grep -q "^error:"; then
        echo "✗ $ver: WeierstrassProduct FAILED"
    else
        echo "✓ $ver: WeierstrassProduct SUCCEEDED"
        echo "$ver" > working_version.txt
        exit 0
    fi
done

echo "No working version found"
