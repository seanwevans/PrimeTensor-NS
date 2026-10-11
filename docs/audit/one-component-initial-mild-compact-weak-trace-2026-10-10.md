# Initial H³ mild compatibility from compact smooth weak initial data

Base: `77ad3df2` (`close initial mild compatibility from weak physical L2 trace`).

## Improvement

The previous initial weak trace hypothesis quantified over *all* physical
`H3ScalarL2` Hilbert test vectors. In the presence of a genuine continuous
initial old physical spectral mild path, a strong decoded `L²` right limit
already exists. The project has proved
`denseRange_h3WeakTestFunctionPhysicalL2_orderOne`, i.e. compact smooth scalar
weak tests are dense in physical scalar `L²`. Strong convergence lets us
pass inner products to the limit for every compact smooth test; equality on
that dense family identifies the limit with the actual physical `u(0)`.

The new interface `H3AuditInitialPhysicalEnergyMildCompactWeakTraceData`
requires only weak convergence against those compact smooth test functions,
not all `L²` vectors, no Bochner temporal source, and no initial energy FTC.

## Main theorems

- `h3Audit_initialHilbertStrongAndCompactWeakLimit_identify`
- `h3Audit_initialMildStrongTrace_and_compactWeakInitial_implies_physicalL2Trace`
- `h3Audit_initialMildCompactWeakTrace_implies_L2TraceData`
- `h3Audit_initialMildCompactWeakTrace_implies_weakTraceData`
- `h3Audit_initialMildCompactWeakTrace_identifies_initialSpectral`
- `h3Audit_initialMildCompactWeakTrace_energyRightLimit`
- `h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialMildCompactWeakTrace`

## What remains conditional

- Actual-old mild spectral representation, and equality of that representation
  with the genuine positive-time old Navier–Stokes velocity.
- The *compact smooth test* initial condition, not supplied by open-time PDE
  admissibility (0 is excluded).
- The independent physical vorticity strong-H³ terminal endpoint.

Do not confuse reduction of the initial-value test class with a proof of the
old/mild initial overlap or unconditional 3D Navier–Stokes regularity.

## Verification

Archive syntax, file inventory and no `sorry` / `admit` / new axiom audit
are checked by package creation. Lean compilation is to be performed using
the pinned toolchain in the user's PrimeTensor-NS checkout.
