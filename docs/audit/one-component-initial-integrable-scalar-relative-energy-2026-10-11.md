# Initial right-zero scalar energy from integral comparison

Baseline: `22ff081b` (positive-time scalar continuity plus an independently required right-zero trace).

New module: `PrimeTensor/Fluid/Vorticity/Continuation/H3/Audit/OneComponentInitialIntegrableScalarRelativeEnergy.lean`.

The integrable-energy interface replaces the direct right-zero-trace hypothesis with initial-interval integrability of the scalar physical old-minus-selected relative energy. The already established epsilon-residual comparison gives an exact inequality `0 ≤ e(t) ≤ K * ∫₀ᵗ e(s) ds`. Since the primitive of an interval-integrable scalar density is continuous at zero and equals zero there, the right scalar-energy limit is zero. This combines with positive-time continuity to recover closed-interval continuity and the existing canonical comparison result.

This does **not** prove that the original open-time Navier--Stokes solution has integrable relative energy or epsilon-accurate PDE inequalities. Those are independently checkable, PDE-facing inputs. The terminal strong-H³ vorticity endpoint remains separate. No new axioms, `sorry`, or equality assumptions are introduced.
