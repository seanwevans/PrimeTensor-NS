# Initial physical projected-RHS integrability to kinetic right trace

Base checkpoint: `d117a63d` (`derive global positive-time physical Hilbert momentum FTC`).

## New bridge

`OneComponentInitialProjectedRHSKineticTrace.lean` identifies the existing abstract initial Bochner temporal derivative with the **actual** old physical Hilbert momentum source: physical spectral Laplacian minus physical Leray forcing. This is justified by the strong derivative theorem proved in `d7e037b8` and the global two-time FTC in `d117a63d`.

The new theorems establish: (1) a finite strong physical `L²` right limit when that actual source is Bochner-integrable over an interval starting at zero; (2) a finite right limit of the physical order-zero kinetic energy; and (3) a direct conversion of a concrete projected-RHS/old-joint/residual contract to the previously proved initial relative-energy comparison and physical zero-jet plus H³-energy upper trace.

## Precisely retained assumptions

- `H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous` remains an **independent hypothesis**; positive-time Hilbert differentiability alone does not imply jointly continuous pointwise-in-space temporal derivatives.
- `IntervalIntegrable (fun s => physicalLaplacian s - physicalLeray s) volume 0 b` is a **new, explicit near-zero source bound**. The `d117a63d` source continuity only yields integrability between positive times, not on `0..b`.
- The initial relative-energy comparison inequality with arbitrarily small residual remains independent. A finite kinetic right limit does **not** identify its limit with the initial data by itself.
- No terminal actual-vorticity endpoint is proved, and no unconditional global Navier--Stokes regularity is asserted.

No `sorry`, `admit`, or custom axioms are used. Local `lake env lean` and `lake build` have **not** been performed in this artifact environment. Run the user's Rocky Linux proof verification before committing.
