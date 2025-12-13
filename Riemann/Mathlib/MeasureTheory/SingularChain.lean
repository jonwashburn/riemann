

import Mathlib.AlgebraicTopology.SingularSet

/-!
# Smooth singular chains (deferred)

The earlier iterations of this repository attempted to build a "smooth singular chain" complex
at the same time as developing integration on simplices.

Following mathlib API guidance (see the accompanying Zulip notes), this approach is postponed:
we first want a correct and lean integration-on-simplex story (and a local Stokes wrapper around
the divergence theorem), *then* we can revisit whether a smooth singular chain complex is needed
for the intended downstream theorems.

Accordingly, this file currently only re-exports mathlib's singular simplicial set machinery.
No additional definitions or theorems are introduced here.
-/

-- Intentionally empty.
