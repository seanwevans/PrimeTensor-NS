# Genuine Z³ Galerkin: unrestricted strong-solution overlap (2026-11-17)

**Parent:** `4343e465131289be234038fa86efb0b824878edb` (overlap uniqueness within the analytic window).

## Mathematical content

For each finite Fourier set S and each real viscosity μ, the complete projected finite
Leray field F_S is real C¹. Its restriction to a compact coefficient ball is Lipschitz.
Any two exact strong solutions on a compact shared interval have compact images.
The union of their images fits within one finite coefficient ball, allowing the
prior compact-ball ODE uniqueness theorem to apply **without assuming a radius**.

This gives:

1. A common finite state radius for any two exact strong paths on [a,b].
2. Unrestricted same-initial-value uniqueness on [a,b].
3. Unrestricted uniqueness on [a,b), by applying (2) separately to [a,t] for t<b.
4. Compatibility for *different* endpoint times b and c on [a,min(b,c)).
5. A longer exact solution segment automatically witnesses strong right extendibility of the
   shorter one; agreement is a conclusion, not a new premise.

No positivity of μ, smallness of initial analytic mass, or restriction by τ is required.
No global Lipschitz estimate of the quadratic Leray field is claimed.

## Next obstruction

Use compatibility to define a canonical trajectory by selecting a solution segment
above each interior time in the directed family of all local Picard continuations.
Prove that the trajectory solves the exact ODE locally and that its maximal
endpoint admits the previously proved analytic restart. The current module
**does not** construct that maximal trajectory or assert cutoff-independent existence.

Lean compilation remains unverified locally; the pinned v4.34.0-rc1 mathlib build
is the required certification step.
