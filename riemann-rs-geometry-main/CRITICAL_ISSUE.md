# Critical Issue: Phase Bound Requires Upper Bound on Interval Width

## Discovery

The phase bound `|phaseChange ρ a b| ≥ L_rec` does NOT hold in general when:
- γ > 0 (or γ < 0 by symmetry)
- σ ∈ (a, b) (mixed-sign case)
- The interval (a, b) is much wider than |γ|

## Mathematical Analysis

For the mixed-sign case with σ ∈ (a, b) and γ > 0:

```
|phaseChange ρ a b| = 2(π - Δ)

where Δ = arctan((b-σ)/γ) + arctan((σ-a)/γ)
```

For the bound to hold:
```
2(π - Δ) ≥ L_rec
⟺ Δ ≤ π - L_rec/2 ≈ 2.87
```

But Δ can exceed 2.87 when the interval is wide:
- If (b-a)/γ = 100 and σ is at midpoint
- Then (b-σ)/γ ≈ 50 and (σ-a)/γ ≈ 50
- arctan(50) ≈ 1.55
- Δ ≈ 3.10 > 2.87
- |phaseChange| ≈ 0.08 < L_rec ≈ 0.55

**The phase bound FAILS for wide intervals!**

## Required Fix

Add UPPER bound constraint to phase_bound lemmas:

```lean
lemma phase_bound_from_arctan (ρ : ℂ) (a b : ℝ) (hab : a < b)
    (hγ_lower : a ≤ ρ.im) (hγ_upper : ρ.im ≤ b)
    (hσ : 1/2 < ρ.re) (hγ_pos : 0 < ρ.im)
    (h_width_lower : b - a ≥ ρ.im)    -- ← Current: lower bound
    (h_width_upper : b - a ≤ K * ρ.im) -- ← NEW: upper bound (K ≈ 2-3)
    : |phaseChange ρ a b| ≥ L_rec
```

## Implications

1. **Whitney covering must be modified** to produce intervals with controlled width
2. Current construction may not satisfy upper bound
3. All phase bound sorries (lines 243, 550, 571, 687, 697, 699) need this fix

## Alternative Approach

Instead of bounding by interval width:
- The Recognition Geometry argument works because Whitney intervals are dyadic
- Dyadic intervals have specific geometric properties
- May need to use dyadic structure directly rather than generic width constraints
