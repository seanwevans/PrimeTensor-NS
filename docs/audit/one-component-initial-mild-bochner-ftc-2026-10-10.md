# Initial mild datum identified using Bochner L1 temporal source

Base checkpoint: `673e2de9` (`identify initial mild H3 datum from physical L2 trace`).

Module: `PrimeTensor/Fluid/Vorticity/Continuation/H3/Audit/OneComponentInitialMildBochnerFTC.lean`

## New dependency reduction

A **single** initial physical interval `(0,b)` with an `H3ScalarL2`-valued,
interval-integrable temporal source `V j` and the exact old-velocity FTC
identity is enough to yield the real physical `L²` right trace, by strong
continuity at the left endpoint of the Bochner primitive.

There is **no** initial uniform bound `‖V j s‖ ≤ C`, no `O(t)` estimate, and no
initial scalar H³ energy FTC or signed transport upper bound. The prior
`H3AuditInitialPhysicalEnergyMildDataAt` already yields a strong H³ spectral
trace (conditional on a genuine old mild representation). Combining this
with the real physical `L²` right trace forces its initial datum to equal
the actual time-zero H³ spectral encoder. The H³ energy right limit follows
by spectral continuity.

## Declarations

- `h3Audit_initialBochnerPrimitive_tendsto_zero`
- `h3Audit_initialBochnerFTC_implies_physicalL2RightTrace`
- `H3AuditInitialPhysicalEnergyMildBochnerFTCData`
- `h3Audit_initialMildBochnerFTC_implies_L2TraceData`
- `h3Audit_initialMildBochnerFTC_identifies_zeroSpectralDatum`
- `h3Audit_initialMildBochnerFTC_energyRightLimit`
- `h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialMildBochnerFTC`

## Still assumed

1. An actual initial Fourier-compatible H³ physical snapshot.
2. An actual initial physical-time mild path for the old solution (with its
   identity to the positive-time physical velocity).
3. The **exact** physical zeroth-velocity Bochner FTC identity, including
   integrability down to the initial endpoint. Merely having smooth PDE
   evolution for positive times does not prove this boundary identity.
4. For the two-component full-time implication, the independent actual
   strong terminal vorticity endpoint.

This is not an unconditional NS regularity result or a proof of the old
initial mild equation from the open-time classical PDE.

The source is not Lean-compiled in the assistant environment; use
`lake env lean` and the repository audit script on Rocky Linux.
