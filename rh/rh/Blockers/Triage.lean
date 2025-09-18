/-!
Blockers triage (placeholder).

This file previously imported mathlib modules that are unavailable in the
current toolchain and declared statements using them. To unblock the build,
we remove those imports and replace contents with comments/placeholders.

This module no longer references external blocker logs; proceed within the track with statement-level interfaces as needed.
-/

namespace RH.Blockers

/-
Placeholders for:
 - Trivial zeros classification on Re(s) ≤ 0
 - Convenience wrappers for trivial zeros at negative even integers
 - Nonvanishing of ζ on Re(s) = 1 (delegated to RS globalization)

These are intentionally omitted here until the required mathlib support is
confirmed. The project compiles with statement-level interfaces in the interim.
-/

end RH.Blockers
