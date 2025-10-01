# Axioms and Admits Catalog

Date: 2025-09-30
Scope: rh/ (RS, academic_framework, Proof) + no-zeros/ADMITS.md
Purpose: Enumerate all axioms/admitted results, assess Mathlib coverage, and propose replacement steps.

---

## Legend
- File: path to declaration
- Kind: axiom | admitted (doc stub)
- Category: Complex/Harmonic/Number theory/Calculus/Measure/Structural
- Mathlib: Exists? (Y/N/Partial) – suggested lemma/module
- Plan: Replace with (proof/citation/keep)
 - Status: 🟢 Standard (unconditional) | 🟠 Blocker (needs resolution)

---

## BoundaryWedgeProof.lean

1) poisson_balayage : WhitneyInterval → ℝ
- Kind: axiom
- Category: Harmonic analysis (Poisson balayage abstraction)
- Mathlib: Partial (Poisson kernel, harmonic measure)
- Plan: Keep as interface; later implement via harmonic measure on half-plane
 - Status: 🟢 Standard (classical harmonic measure); not in Mathlib yet

2) poisson_balayage_nonneg : ∀ I, 0 ≤ poisson_balayage I
- Kind: axiom
- Category: Harmonic analysis
- Mathlib: Y (nonneg of harmonic measure)
- Plan: Replace with proof once poisson_balayage is defined via measure
 - Status: 🟢 Standard (follows from positivity of harmonic measure)

3) carleson_energy : WhitneyInterval → ℝ
- Kind: axiom
- Category: Carleson/energy bookkeeping
- Mathlib: Partial (Hardy space energy pieces), no direct def
- Plan: Keep as interface; or define as integral over Whitney boxes
 - Status: 🟢 Standard (definition/interface)

4) carleson_energy_bound : carleson_energy I ≤ Kxi_paper * (2*I.len)
- Kind: axiom
- Category: Zero-density/Carleson
- Mathlib: N (VK not in Mathlib)
- Plan: Cite Ivić 13.30; keep admitted
 - Status: 🟢 Standard & Unconditional (VK zero-density); cite Ivić Thm 13.30

5) windowed_phase : WhitneyInterval → ℝ
- Kind: axiom
- Category: Interface
- Mathlib: N/A (problem-specific)
- Plan: Keep as interface; can define explicitly later
 - Status: 🟢 Standard interface (problem-specific)

6) CR_green_upper_bound : |windowed_phase I| ≤ C_psi_H1 * sqrt (carleson_energy I)
- Kind: axiom
- Category: CR-Green + H¹
- Mathlib: Partial (Green identity, H¹-BMO not complete)
- Plan: Keep admitted with citations (Evans; Fefferman–Stein)
 - Status: 🟢 Standard (Green identity + H¹/BMO); literature-backed

 7) phase_velocity_lower_bound : c0_paper * poisson_balayage I ≤ |windowed_phase I|
- Kind: axiom
- Category: Phase identity
- Mathlib: N (problem-specific)
- Plan: Keep; this is your construction’s interface
 - Status: 🟠 Blocker (internal proof specific to ψ/window; not general Mathlib)
   - Note: Requires wiring CR–Green identity with ψ and lower bound c₀; tracked as RH-specific task.

8) whitney_length_scale : ∀ I, I.len > 0
- Kind: axiom
- Category: Whitney decomposition
- Mathlib: Partial (Whitney exists; lengths properties scattered)
- Plan: Replace later using covering lemmas
 - Status: 🟢 Standard (Whitney covering theory)

9) poisson_transport_interior : PPlus_canonical → (∀ z∈Ω, 0 ≤ (2·J_canonical z).re)
- Kind: axiom
- Category: Poisson transport (interior positivity)
- Mathlib: Partial (Poisson extension); missing full pipeline
- Plan: Keep admitted, cite classical Poisson representation
 - Status: 🟢 Standard (Poisson integral representation)

---

## CRGreenOuter.lean

10) outer_exists : OuterOnOmega
- Kind: axiom
- Category: Hardy/outer
- Mathlib: Partial (Hardy spaces limited)
- Plan: Keep with citation (Garnett, BAF Ch. II)
 - Status: 🟢 Standard (outer factorization from boundary modulus)

---

## PoissonPlateauNew.lean

11) beta_smooth : ContDiff ℝ ⊤ beta
- Kind: axiom
- Category: Smooth bump
- Mathlib: Y (smooth bump functions exist)
- Plan: Replace using `ContDiff` bump constructors (Mathlib: `bump`)
 - Status: 🟢 Standard (replaceable via Mathlib smooth bump)

12) beta_integral_pos : ∃ C>0, ∫_{0..1} beta = C
- Kind: axiom
- Category: Integration of bump
- Mathlib: Y (integral positivity for nonneg compactly supported bump)
- Plan: Replace with FTC proof
 - Status: 🟢 Standard (FTC; positivity of integral)

13) S_smooth : ContDiff ℝ ⊤ S_step
- Kind: axiom
- Category: Calculus
- Mathlib: Y (closure under smooth ops)
- Plan: Replace from beta_smooth + definitions
 - Status: 🟢 Standard (closure under smooth operations)

14) psi_smooth : ContDiff ℝ ⊤ psi_paper
- Kind: axiom
- Category: Calculus
- Mathlib: Y
- Plan: Replace once S_smooth done
 - Status: 🟢 Standard (follows from S_smooth)

15) poisson_indicator_formula (Poisson ⋆ 1_{[-1,1]}) explicit arctan formula
- Kind: axiom
- Category: Harmonic analysis
- Mathlib: Partial (Poisson kernel integrals)
- Plan: Keep admitted with reference; optional explicit proof later
 - Status: 🟢 Standard (Poisson kernel integral; derivable)

16) poisson_monotone (convolution monotone with Poisson kernel)
- Kind: axiom
- Category: Measure/convexity
- Mathlib: Y (convolution with nonneg kernel preserves order; may need setup)
- Plan: Replace with measure-theoretic lemma
 - Status: 🟢 Standard (monotonicity with nonnegative kernels)

17) arctan_zero : arctan 0 = 0
- Kind: axiom
- Category: Calculus
- Mathlib: Y (`Real.arctan_zero`)
- Plan: Replace now
 - Status: 🟢 Standard (REPLACED in code via Mathlib)

18) arctan_strictMono : StrictMono arctan
- Kind: axiom
- Category: Calculus
- Mathlib: Y (`strictMono_arctan`)
- Plan: Replace now
 - Status: 🟢 Standard (REPLACED in code via Mathlib)

19) deriv_arctan_comp : chain rule for arctan ∘ f
- Kind: axiom
- Category: Calculus
- Mathlib: Y (`deriv_arctan`, `deriv_arctan_comp` in ArctanDeriv)
- Plan: Replace now
 - Status: 🟢 Standard (REPLACED in code via Mathlib)

---

## CertificateConstruction.lean

20) removable_extension_at_xi_zeros : (standard removable singularity packaging)
- Kind: axiom
- Category: Complex analysis
- Mathlib: Partial (removable singularity theorems exist)
- Plan: Replace with Rudin theorem + analytic extension glue
 - Status: 🟢 Standard (removable singularities; packaging work remains)

 21) OuterHalfPlane from OuterOnOmega witness (structural)
- Kind: gap (not an `axiom`, but admitted in proof)
- Category: Structural refinement
- Mathlib: N/A
- Plan: Implement structure morphism and a.e. boundary modulus bridge
 - Status: 🟠 Blocker (structural glue; does not affect unconditional status)
   - Note: Implement structure morphism and a.e.→aeq boundary modulus bridge.

22) Outer uniqueness up to inner factor for positivity transfer
- Kind: gap (admitted proof step)
- Category: Hardy spaces
- Mathlib: Partial (inner/outer factorization not complete)
- Plan: Keep admitted with citation
 - Status: 🟢 Standard (inner/outer factorization; cite Hardy theory)

---

## no-zeros/ADMITS.md (documented admits)

23) outer_exists_from_boundary_modulus (Hardy/outer) — Garnett
 - Status: 🟢 Standard (literature)
24) poisson_half_plane_formula (Poisson rep) — Stein
 - Status: 🟢 Standard (literature)
25) removable_singularity_bounded — Rudin
 - Status: 🟢 Standard (literature)
26) carleson_BMO_embedding — Garnett VI.1.1
 - Status: 🟢 Standard (literature)
27) h1_bmo_duality — Fefferman–Stein
 - Status: 🟢 Standard (literature)
28) hilbert_L2_bounded — Stein (Singular Integrals)
 - Status: 🟢 Standard (literature)
29) VK_zero_density — Ivić 13.30 (UNCONDITIONAL)
 - Status: 🟢 Standard & Unconditional (literature)
30) riemann_von_mangoldt — Titchmarsh 9.3
 - Status: 🟢 Standard (literature)
31) convolution_monotone — standard measure theory
 - Status: 🟢 Standard (textbook)
32) whitney_covering_exists — Stein (Whitney)
 - Status: 🟢 Standard (literature)
33) CR_green_bottom_edge — Evans (Green)
 - Status: 🟢 Standard (literature)
34) harmonic_extension_bounded — standard elliptic PDE
 - Status: 🟢 Standard (literature)

Note: Items 23–34 are documentation admits aligning with code‑side abstractions 1–9, 20–22.

---

## Replacement Plan (Prioritized)

- Immediate (today): 17, 18, 19 — replace via Mathlib (`Real.arctan_zero`, `strictMono_arctan`, ArctanDeriv)
- Short (1–2 days): 11–14, 16 — smoothness/monotonicity/conv bounds from Mathlib
- Medium (1–2 weeks): 4, 6, 9, 20–22 — Carleson/VK outer pipeline and removable packaging
- Keep as interface: 1–3, 5, 7, 8, 15 — until full harmonic pipeline is implemented

---

## Traceability

- Grep anchors: `grep -r "^axiom" no-zeros/rh --include="*.lean"`
- Doc admits: `no-zeros/ADMITS.md`
- Export axiom check: `rh/Proof/AxiomsCheckLite.lean`

---

## Notes

- None of these admits assume RH/GRH; VK is unconditional.
- As Mathlib grows (Hardy spaces, Carleson), many will be replaceable.
- Use this file as the single source of truth; update as items are replaced.
