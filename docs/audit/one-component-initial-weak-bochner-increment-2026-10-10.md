# Initial weak L² trace and positive-time Bochner increments

Parent: `befb7f37` (`derive initial physical L2 trace from Bochner FTC`).

This module eliminates the **initial-endpoint Bochner FTC identity** from the
previous contract. Instead, it assumes the actual velocity's two-point
Bochner evolution law between *strict positive times*, an integrable temporal
source on one fixed initial interval, and an initial **weak** physical L²
trace to the old solution's prescribed initial datum.

Write `P(t)=∫₀ᵗ V(s) ds`, choose `q=b/2`, and use the two-time law and the
interval-integral subtraction theorem to show `F(t)=C+P(t)` for every
`0<t<b`, where `C=F(q)-P(q)`. Since `V` is Bochner integrable, `P(t)→0`
strongly as `t↓0`, so `F(t)→C` strongly. The weak initial trace tests
against `C−L₀` and forces `‖C−L₀‖²=0`. Thus `F(t)→L₀` strongly, without
assuming norm continuity at zero or a zero-anchored FTC identity.

## Main declarations

- `h3Audit_weakInitialTrace_strong_of_positiveBochnerIncrements`
- `h3Audit_initialWeakBochnerIncrement_implies_physicalL2RightTrace`
- `H3AuditInitialPhysicalEnergyMildWeakBochnerIncrementData`
- `h3Audit_initialMildWeakBochnerIncrement_implies_L2TraceData`
- `h3Audit_initialMildWeakBochnerIncrement_identifies_initialSpectral`
- `h3Audit_initialMildWeakBochnerIncrement_energyRightLimit`
- `h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialMildWeakBochnerIncrement`

## Assumptions still outstanding

The actual old-velocity mild representation remains explicit, as do the
positive-time Bochner two-point identity, temporal L¹ integrability and weak
physical initial condition. The auxiliary integrability on `0..t` is stated
separately in the Lean interface to support the interval-subtraction lemma.
The independent physical terminal-vorticity H³ endpoint is still assumed.
This is **not** a proof of global 3D Navier–Stokes regularity.

No `sorry`, `admit`, or new axioms are used. Lean compilation must be verified
against the project's toolchain.
