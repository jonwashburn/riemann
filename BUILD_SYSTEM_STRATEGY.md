# Build System Configuration Issue - Strategy & Resolution

**Date:** 2025-10-20  
**Issue:** `rh.RS.PinchCertificate` not building despite being imported

## Root Cause Analysis

### Problem Identified
Looking at `/Users/jonathanwashburn/Projects/zeros/no-zeros/lakefile.lean`:

**PinchCertificate is NOT in the globs list!**

```lean
lean_lib «rh» where
  globs := #[
    ...
    `rh.RS.PinchWrappers,
    `rh.RS.PinchIngredients,
    ...
  ]
```

But `rh.RS.PinchCertificate` is **missing** from this explicit list.

### Why This Happens
Lake's default behavior depends on the `globs` configuration:
- **With explicit globs**: Only listed modules are built
- **Without globs** (or `#[.submodules `rh]`): All modules are auto-discovered

The lakefile uses **explicit globs** to "restrict build to certificate-route modules" (line 25), but `PinchCertificate` was not added to this restricted list.

### Evidence
1. ✅ `lake env lean rh/RS/PinchCertificate.lean` compiles successfully
2. ❌ `lake build rh.RS.PinchCertificate` returns "unknown target"
3. ❌ `.lake/build/lib/rh/RS/PinchCertificate.olean` does not exist
4. ✅ Other RS modules in the globs list DO have .olean files

## Resolution Strategy

### Option 1: Add PinchCertificate to Globs (RECOMMENDED)

**Pros:**
- Minimal change
- Maintains explicit build control
- Fast rebuild (only adds one module)
- Preserves existing architecture

**Cons:**
- None

**Implementation:**
```lean
lean_lib «rh» where
  globs := #[
    ...
    `rh.RS.Cayley,
    `rh.RS.Det2Outer,
    `rh.RS.OffZerosBridge,
    `rh.RS.XiExtBridge,
    `rh.RS.SchurGlobalization,
    `rh.RS.PinchCertificate,        -- ADD THIS LINE
    `rh.RS.PinchWrappers,
    `rh.RS.PinchIngredients,
    ...
  ]
```

### Option 2: Use Submodule Glob for RS

**Pros:**
- Auto-discovers all RS modules
- Won't miss future additions

**Cons:**
- May build unwanted modules
- Slower initial build
- Goes against stated intent (line 25: "restrict build")

**Implementation:**
```lean
lean_lib «rh» where
  globs := #[
    -- Academic framework core (explicit)
    `rh.academic_framework.CompletedXi,
    ...
    -- RS layer (auto-discover all)
    .submodules `rh.RS,
    -- Proof entry (explicit)
    `rh.Proof.Main,
    ...
  ]
```

### Option 3: Remove Globs Entirely

**Pros:**
- Never miss modules again
- Simplest configuration

**Cons:**
- Builds entire codebase (including placeholders, experiments)
- Much slower builds
- Not suitable for focused development

## Recommended Action Plan

### Step 1: Add Missing Module (5 seconds)
Add `rh.RS.PinchCertificate` to the globs array in lakefile.lean

### Step 2: Verify Dependencies (30 seconds)
Check if any other modules are missing:
```bash
# Find all imported modules
grep -r "^import rh.RS" no-zeros/rh/{RS,Proof,Cert}/*.lean | \
  sed 's/.*import //' | sort -u

# Compare with lakefile globs
```

### Step 3: Clean Build (2 minutes)
```bash
lake clean
lake build rh.Proof.Export
```

### Step 4: Verify Success (30 seconds)
```bash
# Check .olean exists
ls .lake/build/lib/rh/RS/PinchCertificate.olean

# Run axiom checker
lake env lean --run rh/Proof/AxiomsCheckLite.lean
```

## Additional Missing Modules to Check

Based on imports in the codebase, these may also be missing:
- `rh.RS.CRGreenOuter` (used by several files)
- `rh.RS.PoissonAI` (imported by HalfPlaneOuterV2)
- `rh.RS.Det2Outer` (already in globs ✓)
- `rh.academic_framework.DiagonalFredholm.*` (may need sub-modules)
- `rh.academic_framework.CompletedXiSymmetry`
- `rh.academic_framework.ZetaFunctionalEquation`
- `rh.academic_framework.Theta`
- `rh.academic_framework.GammaBounds`
- `rh.academic_framework.EulerProductMathlib`
- `rh.academic_framework.MellinThetaZeta`

## Why This Wasn't Caught Earlier

1. **Lake's error message is misleading**: Says "object file does not exist" rather than "module not in build configuration"
2. **File compiles individually**: `lake env lean` works, suggesting code is fine
3. **Globs are restrictive**: Easy to forget to add new dependencies

## Prevention Strategy

### For Future Development

1. **Use submodule globs for active directories**:
   ```lean
   .submodules `rh.RS,  -- Auto-discover all RS modules
   ```

2. **Add CI check** to detect import/glob mismatches:
   ```bash
   #!/bin/bash
   # Check all imported modules are in lakefile
   ```

3. **Document glob policy** in lakefile comments

4. **Regular dependency audit**: After adding new files, verify they're in globs

## Time Estimate

- **Diagnosis**: ✅ Complete
- **Fix**: ~5 seconds (edit lakefile)
- **Rebuild**: ~2 minutes (clean + build)
- **Verify**: ~30 seconds (axiom check)
- **Total**: ~3 minutes

## Risk Assessment

- **Risk**: ZERO - This is a pure configuration fix
- **Code changes**: NONE - No Lean code modified
- **Breaking changes**: NONE - Only enables building
- **Technical debt**: NONE - Fixes architectural gap

---

**Next Action:** Add `rh.RS.PinchCertificate` to lakefile.lean globs array and rebuild.

