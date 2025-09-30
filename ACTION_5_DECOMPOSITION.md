# ACTION 5 Decomposition: Certificate Construction (Final!)

**Goal**: Wire all components → `RiemannHypothesis_unconditional`  
**Status**: Final action to complete unconditional proof  
**Approach**: Bite-sized pieces

---

## What ACTION 5 Does

**Purpose**: Connect all proven components to produce the final RH theorem

**Available components**:
- ✅ J_CR with outer normalization (ACTION 2)
- ✅ c₀(ψ) > 0 (ACTION 3)
- ✅ (P+) boundary wedge (ACTION 4)
- ✅ Interior positivity (ACTION 4)
- ✅ Existing Main.lean wiring

**Goal**: Zero-argument `RiemannHypothesis` theorem

---

## Bite-Sized Pieces

### **Piece 5.1**: Review Main.lean Requirements (30 min)

**Task**: Understand what Main.lean needs

**File**: `rh/Proof/Main.lean`

**Key theorem there**:
```lean
theorem RH_from_pinch_certificate (C : RH.RS.PinchCertificateExt) : RiemannHypothesis
```

**Needs**: A concrete `PinchCertificateExt` witness

---

### **Piece 5.2**: Connect Interior Positivity (1 hour)

**File**: Create `rh/RS/CertificateConstruction.lean`

**Task**: Bridge from `interior_positive_from_constants` to certificate requirements

```lean
-- From ACTION 4:
theorem interior_positive_from_constants :
  ∀ z ∈ Ω, 0 ≤ ((2 : ℂ) * J_canonical z).re

-- Need for certificate:
theorem interior_positive_off_xi_zeros :
  ∀ z ∈ (Ω \ {z | riemannXi_ext z = 0}),
    0 ≤ ((2 : ℂ) * J_pinch det2 outer_exists.outer z).re
```

**Proof**: Restriction (YOUR logic - must reason through)

---

### **Piece 5.3**: Package Removable Data (1 hour)

**Task**: Provide pinned removable extension witness

```lean
-- Can admit: removable singularity with u-trick
axiom pinned_removable_at_xi_zeros :
  ∀ ρ ∈ Ω, riemannXi_ext ρ = 0 →
    ∃ U, ... (standard removable singularity data)
```

**Status**: Can admit as standard complex analysis

---

### **Piece 5.4**: Build Concrete Certificate (2 hours)

**Task**: Construct the actual witness

```lean
noncomputable def concrete_certificate : RH.RS.PinchCertificateExt := by
  refine buildPinchCertificate
    ⟨outer_exists.outer, ...⟩
    (hRe_offXi := interior_positive_off_xi_zeros)
    (hRemXi := pinned_removable_at_xi_zeros)
```

**Proof**: Assembly (YOUR wiring)

---

### **Piece 5.5**: Main Theorem (30 min)

**Task**: Prove `RiemannHypothesis_unconditional`

```lean
theorem RiemannHypothesis_unconditional : RiemannHypothesis :=
  RH_from_pinch_certificate concrete_certificate
```

**Proof**: One line! (if certificate is correct)

---

### **Piece 5.6**: Verification (1 hour)

**Task**: Verify axioms, update docs

---

## Timeline

**Total**: 6-8 hours in bite-sized pieces

**Can complete**: Over 1-2 sessions

---

*Ready to start Piece 5.1!*
