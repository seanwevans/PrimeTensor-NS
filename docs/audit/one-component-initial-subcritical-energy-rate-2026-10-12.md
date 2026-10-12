# Initial projected RHS from subcritical H³ energy growth

Base checkpoint: `34183d42` — derive initial projected RHS integrability from H3 energy.

## New proof increment

The preceding patch took `IntervalIntegrable (velocityH3EnergyAt u) volume 0 b`
as its scalar energy assumption. This patch directly establishes the *actual*
physical projected-source Bochner integral from a concrete near-zero energy rate:

`velocityH3EnergyAt u s ≤ M * s ^ (-α)` for `0 < s ≤ b`, `0 ≤ α < 1`, `M ≥ 0`.

Mathlib's `intervalIntegral.intervalIntegrable_rpow'` proves integrability of
`s ^ (-α)` at the origin. The existing source norm bounds imply

`‖D(s) - N(s)‖ ≤ (3 + C_L) * M * s ^ (-α)`

and prior positive-time reconstructed-source continuity supplies strong
measurability. The zero-extended source vanishes at time zero, permitting the
existing generic domination theorem on the closed initial interval.

The patch yields a quantitative initial projected-source mass estimate,
finite physical L² and order-zero kinetic right limits under old temporal
joint-continuity, and transfers the unchanged residual contract to compact
weak comparison and initial physical L²/upper H³ trace consequences.

## Remaining independent assumptions

- The subcritical energy rate itself is not derived from H³ admissibility.
- Old pointwise temporal-derivative joint spacetime continuity is not closed.
- Vanishing relative-energy residual remains a distinct PDE input.
- No terminal actual-vorticity endpoint theorem or global regularity result
  follows unconditionally.

## Validation

This ZIP contains Lean source and documentation; it has not been locally
Lean-compiled. Use `lake build <module>`, `lake env lean`, and full `lake build`
in the user's Rocky Linux repository before committing.
