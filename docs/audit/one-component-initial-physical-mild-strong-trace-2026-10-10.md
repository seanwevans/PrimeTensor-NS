# Initial full H³ right trace from the actual old physical mild path

Checkpoint: `fb147451` (`reduce initial H3 trace to physical and energy continuity`).

The prior continuity-only theorem requires equality between the original
field's specified value at t=0 and its positive-time trace. The open-time
classical Navier--Stokes predicate imposes no such equality; changing the
value of u at t=0 does not affect the equation on `(0,T)`.

This module records a second, independent route. The earlier
`H3AuditInitialPhysicalEnergyMildDataAt` gives a bounded continuous spectral
H³ path P on `[0,R]`, with `P(0)=U₀`, and identifies P at positive times
with the actual old Fourier velocity. Normalize and extend P to real time,
use its continuity at 0, and transfer its strong trace to the real old path.
The proof does not need to assume right continuity of the old physical L²
velocity at the separately specified t=0 value.

The derived energy right limit is `1 + h3SpectralVelocitySquareEnergy U₀`.
To identify this with `velocityH3EnergyAt u 0`, one must separately assume
compatibility of the physical zero-time value with U₀.

Main declarations:
- `h3Audit_initialPhysicalEnergyMildDataAt_fullStrongH3Trace`
- `h3Audit_initialPhysicalEnergyMildData_fullStrongH3Trace`
- `h3Audit_initialPhysicalEnergyMildDataAt_energyRightLimit`
- `h3Audit_initialPhysicalEnergyMildDataAt_energyRightLimit_of_compatibleZero`

No `sorry`, `admit`, or new axioms. Initial physical mild representation,
initial value identity and the physical energy ceiling remain hypotheses of
the earlier physical mild data contract. Terminal strong vorticity endpoint
and unconditional global regularity are not established by this result.
