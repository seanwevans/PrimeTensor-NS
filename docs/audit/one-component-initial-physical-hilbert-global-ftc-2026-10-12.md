# Physical positive-time Hilbert momentum FTC

Checkpoint: `d7e037b8` — `derive strong physical Hilbert momentum evolution`.

The preceding module gives a strong physical L² derivative for the actual
preterminal old velocity at every positive time, conditional on the old
spacetime temporal-derivative joint continuity premise. The present file
closes the **global two-time integral consequence** of that derivative.

## Declarations

- `h3Audit_initialActualProjectedRHS_continuousOn_positiveTime` proves continuity of the actual diffusion-minus-Leray L² source over all `(0,T)`, from existing spectral velocity continuity; old joint continuity is not needed for this fact.
- `h3Audit_initialActualProjectedRHS_intervalIntegrable_between_positiveTimes` supplies Bochner integrability over every ordered or unordered positive time pair. An enclosing compact strict interval avoids separate coincident-endpoint arguments.
- `h3Audit_initialOldJoint_implies_physicalHilbertFTC_between_positiveTimes` gives `F(t) - F(s) = ∫_s^t G(r)dr`, using the strong derivative already proved at `d7e037b8` and the Mathlib unordered-interval Banach FTC.
- `h3Audit_initialOldJoint_implies_physicalHilbertEvolution_between_positiveTimes` gives the equivalent basepoint evolution formula.
- `h3Audit_initialOldJoint_implies_physicalHilbertDifferentiableOn_positiveTime` packages strong interior differentiability.

## Independent analytic frontiers

The old temporal-derivative spacetime joint-continuity property is **still assumed** for the physical evolution and derivative theorems. Their proof does not derive that regularity from admissibility. Integrability of the physical source from time zero, the initial relative-energy comparison residual, and the independent terminal actual-vorticity endpoint also remain open. No statement of unconditional global regularity is asserted.

The full Rocky Linux `lake env lean` and `lake build` are required before a commit; this environment lacks the Lean toolchain and the project dependencies.
