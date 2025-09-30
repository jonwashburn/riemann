# ACTION 5: Certificate Construction - Final Action!

**Status**: Ready to begin  
**Goal**: Wire all components → `RiemannHypothesis_unconditional`  
**Estimated**: 3-5 days → **Will break into bite-sized pieces**

---

## 🎯 What ACTION 5 Does

**Purpose**: Wire everything together to produce the final theorem

**Components available** (from ACTIONS 1-4):
- ✅ J_CR with outer normalization (ACTION 2)
- ✅ c₀(ψ) > 0 (ACTION 3)
- ✅ (P+) boundary wedge (ACTION 4)
- ✅ Interior positivity (ACTION 4)

**Need to produce**: Zero-argument `RiemannHypothesis` theorem

---

## Bite-Sized Decomposition

### **Piece 5.1**: Review Main.lean Wiring (30 min)

**Task**: Understand what's already there

**File**: `rh/Proof/Main.lean`

**Review**:
- Existing `RH_from_pinch_certificate` theorem
- Certificate requirements
- Wiring structure

---

### **Piece 5.2**: Connect (P+) to Certificate (1 hour)

**Task**: Wire `PPlus_from_constants` → certificate requirements

**What's needed**:
```lean
-- From ACTION 4
theorem interior_positive_from_constants :
  ∀ z ∈ Ω, 0 ≤ ((2·J) z).re

-- Needed for certificate
theorem interior_positive_off_zeros :
  ∀ z ∈ (Ω \ {ξ=0}), 0 ≤ ((2·J) z).re
```

**Proof**: Restriction (YOUR reasoning - must prove)

---

### **Piece 5.3**: Removable Extension (1 hour)

**Task**: Package pinned removable data

**Standard**: Removable singularity theory  
**Can admit**: The u-trick data

---

### **Piece 5.4**: Build Concrete Certificate (2 hours)

**Task**: Construct actual `PinchCertificateExt` witness

**Using**:
- Outer from ACTION 2
- Interior positivity from Piece 5.2
- Removable data from Piece 5.3

---

### **Piece 5.5**: Main Theorem (1 hour)

**Task**: Prove `RiemannHypothesis_unconditional`

**Should be**:
```lean
theorem RiemannHypothesis_unconditional : RiemannHypothesis :=
  RH concrete_certificate
```

---

### **Piece 5.6**: Final Verification (1 hour)

**Task**: Verify axioms, build, documentation

---

## Total: 7 hours in bite-sized pieces

**Each piece**: 30 min - 2 hours  
**Can do over**: Several sessions  
**Approach**: Same as ACTIONS 1-4

---

## What's Standard vs RH

### **Can Admit**:
- Removable singularity u-trick
- Restriction to off-zeros set
- Pinned limit data

### **Must Prove**:
- Restriction reasoning (YOUR logic)
- Certificate assembly (YOUR wiring)
- Final composition

**Mostly wiring** - components are ready!

---

## Ready to Begin

**All prerequisites complete**:
- ✅ J_CR implemented
- ✅ (P+) proven
- ✅ Interior positivity available
- ✅ Main.lean structure exists

**Just need**: Wire them together!

---

*ACTION 5 decomposed and ready. Can start anytime!*
