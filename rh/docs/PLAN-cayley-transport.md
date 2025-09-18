# Plan: Half-plane transport via Cayley (Hardy–Smirnov route)

## Goal
Make the boundary route unconditional by supplying classical complex-analysis inputs at the academic layer, then reuse the RS façade:
- Disk Poisson/Herglotz representation (positivity) ⇒ half-plane representation via Cayley
- Disk outer existence with prescribed boundary modulus ⇒ half-plane outer via Cayley
- RS pipeline: (P+) ⇒ interior nonnegativity ⇒ Schur off zeros ⇒ removability/pinch

## Steps
1) Survey mathlib for disk theorems
- Disk Poisson/Herglotz: Poisson representation of Re F̃ and positivity
- Disk outer existence: outer with |Ō|=g a.e. (log g ∈ L¹)

2) Add Cayley adapters (AF layer)
- Define φ: Ω→𝔻 and φ⁻¹; record boundary parametrization and kernel covariance
- Disk representation ⇒ HasHalfPlanePoissonRepresentation F
- Disk outer ⇒ ExistsOuterWithBoundaryModulus on Ω

3) Implement transport
- Use HasHalfPlanePoissonRepresentation ⇒ HasHalfPlanePoissonTransport (already in AF)
- Export pinch specialization: HasHalfPlanePoissonTransport_Jpinch

4) Verify RS chain builds
- PPlusFromCarleson_exists F (facade) → transport → Cayley → Schur off Z(ξ) → pinch

5) Optional: Kξ formalization
- Keep KxiBound as interface for now; later formalize VK/RvM → Whitney Carleson

## Deliverables
- AF adapters and transport lemmas (mathlib-only)
- If disk theorems are missing, proceed with alternative AF adapters or defer that subtask; do not create blocker logs.
- No changes to RS/CRGreen/PoissonPlateau/H1BMOWindows modules needed

## Exit criteria
- Build succeeds with transport wired to AF theorems.
- RS pipeline compiles and the route is explicit about remaining external inputs
