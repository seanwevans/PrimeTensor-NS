# Initial uniqueness from positive-time integrated residual inequalities

Checkpoint: `5b7ff2f1`.

Module: `PrimeTensor/Fluid/Vorticity/Continuation/H3/Audit/OneComponentInitialPositiveTimeResidualRelativeEnergy.lean`.

## Improvement to the PDE interface

The prior `H3AuditInitialCanonicalIntegrableScalarRelativeEnergyData` imposed
an approximate comparison inequality on `[0,b]`. The new
`H3AuditInitialCanonicalPositiveTimeResidualRelativeEnergyData` imposes it
only on `(0,b]`, the portion where the open-time Navier--Stokes equations
and selected mild evolution actually apply. At `t=0` the relative-energy
comparison is definitionally anchored at zero; the interval integrals also
vanish at zero. The theorem
`h3Audit_initialPositiveRelativeEnergy_extend_to_zero` recovers the closed
inequality without continuity, time differentiability, or new PDE input.

Arbitrarily small integrated residuals then provide the exact inequality;
existing `L¹` scalar comparison integrability yields the right-zero trace,
and positive-time continuity gives the closed-interval scalar Gronwall result.
The physical compact weak comparison, actual initial `L²`/`H³` trace and
conditional two-component full-time transverse estimate follow by the
existing verified chain.

## Remaining actual PDE obligations

Initial-time integrability of the physical old/selected scalar comparison,
positive-time scalar continuity, and arbitrarily small integrated residual
estimates are still hypotheses, **not derived** from the current open-time
`LoggedPreterminalH3PathAdmissible` predicate. The independent terminal
actual-vorticity strong-`H³` endpoint is unchanged.

No `sorry`, `admit`, or new axioms are introduced. The file requires a local
Lean build and project audit to verify elaboration and all dependencies.
