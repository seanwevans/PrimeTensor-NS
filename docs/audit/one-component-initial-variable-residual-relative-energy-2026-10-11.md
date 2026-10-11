# Variable-coefficient initial relative energy with time-dependent residuals

Parent checkpoint: `be4078ca` (vanishing scalar relative-energy defects).

## New abstraction

For the physical old-minus-selected difference `D(t)` write `e(t) = ‖D(t)‖²`.
The approximation can now carry an index-dependent coefficient `κₙ` and a
physical-time-dependent error profile `ρₙ(t)`:

    e(t) ≤ κₙ ∫₀ᵗ e(s) ds + ρₙ(t),     0 ≤ t ≤ b.

It suffices to have one finite comparison coefficient `K`, a vanishing
scalar error budget `δₙ`, and the uniform inequalities

    κₙ ≤ K,     ρₙ(t) ≤ δₙ,     δₙ → 0.

The relative-energy primitive is nonnegative, so replacing `κₙ` by `K`
can only increase the right-hand side. The residual budget then bounds
`ρₙ(t)` by `δₙ`, and the prior `be4078ca` theorem yields the exact scalar
energy inequality. This discharges the comparison without fixing the actual
approximating coefficient or residual profile in advance.

The new file includes the reverse adapter from the previous contract,
the initial physical and weak-test consequences, and the conditional
full-time transverse estimate.

## Explicit remaining obligations

The approximate relative-energy inequality, the common upper coefficient
bound, the vanishing residual budget, and closed-initial-interval scalar
energy continuity are **PDE inputs**, not theorems from open-time
Navier--Stokes admissibility. They must not be supplied circularly from
old/selected equality. The terminal actual-vorticity endpoint also remains
independent. This patch does not establish unconditional global regularity.

The file has no `sorry`, `admit`, or new axioms, but requires the user's
pinned Lean/mathlib toolchain for compilation.
