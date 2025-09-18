Purpose: six concrete tickets to complete the CR–Green route (P+) and the Kξ witness, enabling a zero-argument RH export. Each ticket lists files, exact lemmas/theorems, acceptance, and blocker protocol.

1) CR–Green windows: test energy and cutoff pairing
- Files: rh/Cert/KxiPPlus.lean (or keep test-energy defs here; pairing result here)
- Implement:
  - AdmissibleWindow class (atom-safe, mass 1, flat plateau, holes at atoms).
  - uniform_test_energy: ∬_{Q(α′I)} (|∇Vφ|^2 + |∇χ|^2|Vφ|^2) σ ≤ Aψ (scale-invariant; independent of I,t0, holes).
  - cutoff_pairing_bound: ∫ φ(−w′) ≤ Crem ⋅ (⊔_{Q(α′I)} |∇U|^2 σ)^{1/2}, Crem depends only on (α,ψ).
- Acceptance: mathlib only; no axioms/sorry; constants independent of I,t0, holes.
- Escalation: If Poisson test-energy or cutoff step is missing in mathlib, add one line to BLOCKERS.md: “Missing: uniform Poisson test-energy for admissible windows (holes allowed)” or “Missing: CR–Green cutoff pairing bound.”

2) CR–Green ⇒ (P+) from Carleson budget
- Files: rh/Cert/KxiPPlus.lean (use existing CarlesonSystem/PairingSystem scaffolding; or rh/Cert/CarlesonPairingInstances.lean)
- Implement:
  - PPlusFromCarleson_exists (F : ℂ → ℂ): constant Ctest = Crem√Aψ√Cζ; conclude ∫ φ(−w′) ≤ Ctest √|I|.
  - Specialize to F := fun s => (2:ℂ) * J s.
- Acceptance: theorem present and builds; no axioms/sorry.
- Escalation: If a minor inequality is missing, record a one-liner.

3) Poisson off-support square bound (Whitney)
- File: rh/RS/CRGreenOuter.lean
- Implement:
  - poisson_square_whitney_offsupport:
    For I=[T−L,T+L], 0<σ≤αL, and |x−T|≥2^{k−1}L,
    ∫_I Kσ(t−x)^2 dt ≤ |I| · σ^2 / (((2^{k−1}L)^2+σ^2)^2),
    hence ∫_0^{αL}∫_I Kσ^2 σ ≤ |I|(α^4/4)4^{−k}.
- Acceptance: no axioms/sorry. Use ∫_I f ≤ |I| sup_I f and ∫_0^{αL} σ^3.
- Escalation: If interval integral helper is missing, record:
  “Missing: interval sup bound ∫_I f ≤ |I|·sup_I f (finite interval, Lebesgue).”

4) Annular Poisson L^2 with linear ν_k
- File: rh/RS/CRGreenOuter.lean
- Implement:
  - annular_balayage_L2:
    ∬_{Q(α I)} (∑_{γ∈A_k} Kσ(t−γ))^2 σ ≤ (α^4/2)|I|4^{−k}ν_k.
  - Proof: center S = ∑(Kσ(·−γ) − Kσ(·−T)); apply (3) to each term; row-sum to keep linear ν_k.
- Acceptance: no axioms/sorry; explicit dependence Cα≲α^4.
- Escalation: If centered row-sum is missing, record:
  “Missing: centered balayage row-sum (Schur/Bessel) to keep linear ν_k.”

5) VK to annulus counts (monotone telescope)
- File: rh/Cert/KxiWhitney_RvM.lean
- Implement:
  - structure ZeroCountAPI (N : ℝ → ℝ → ℝ, mono_R).
  - VK_bound α c Z: on R∈[L,αL], N(T,R) ≤ a1 R log⟨T⟩ + a2 log⟨T⟩.
  - annulus_counts_of_VK: ν_k ≤ a1(α) 2^k L log⟨T⟩ + a2(α) 2^{−k} log⟨T⟩.
- Acceptance: no axioms/sorry; constants depend only on α (and inputs).
- Escalation: If averaging lemma is missing, record:
  “Missing: monotone telescope to average the VK constant term over [2^k L, 2^{k+1} L] gaining 2^{−k}.”

6) Sum to Kξ and expose Cert witness
- File: rh/Cert/KxiWhitney_RvM.lean
- Implement:
  - kxi_whitney_carleson_of_rvm (α c : ℝ) : RH.Cert.KxiWhitney.KxiBound α c.
  - Use ∑_k 4^{−k}2^k=1/7, ∑_k 4^{−k}2^{−k}=1/15; Kξ(α,c) = (α^4/2)(a1/7 + a2/15)c.
- Acceptance: builds; no axioms/sorry; Kξ nontrivial.
- Escalation: If (4) or (5) is not yet available, reference those blockers.

Shared rules
- No new axioms. No sorry. Edit only listed files.
- If blocked, add exactly one line to BLOCKERS.md naming the first missing lemma and stop.
- Keep constants independent of (T,L) and hole placements; dependence on α (and c) explicit.
- Reference: math blueprint snippets are in Riemann-active-13-FINAL-abs-concl-CLEAN2v12.tex (sections: CR–Green pairing, Whitney annulus L^2, VK counts), and comments in rh/RS/CRGreenOuter.lean and rh/Cert/KxiWhitney_RvM.lean mark targets.

Reference notes: see docs/CRGreen-Kxi-Notes.md for constants and intended proofs for items (3), (4), (6).


