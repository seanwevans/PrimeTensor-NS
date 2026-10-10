# Initial physical time-modulus criterion

Parent checkpoint: `f4fa73bc` — derive initial H3 trace from physical zero-time L2 velocity.

## New reduction

A single right-vanishing modulus `ω : ℝ → ℝ`, with `ω(t) → 0` as `t ↓ 0`, controls:

1. the excess of the actual H³ energy over its value at zero;
2. the physical `L²` distance of each actual velocity coordinate from its initial L² jet.

The new generic metric theorem converts eventual distance control by `ω` to a right strong limit. A scalar companion converts eventual energy control by `ω` into the one-sided energy inequality. Their physical application supplies both remaining assumptions of the previous initial zero-jet H³ theorem, and derives full strong H³ trace for the actual velocity.

A `C*t` specialization exposes concrete short-time PDE estimates as the next target (e.g., by integrating a bounded physical velocity `L²` derivative and an H³ energy derivative). **Neither derivative estimate is established here.**

## Exported declarations

- `h3Audit_tendstoRight_of_eventualDistanceLe_modulus`
- `h3Audit_rightUpperEnergy_of_eventualModulus`
- `h3Audit_eventually_initialStrictPhysicalTime`
- `H3AuditInitialPhysicalZeroJetTimeModulusData`
- `h3Audit_initialPhysicalTimeModulus_implies_zeroJetL2Data`
- `h3Audit_initialPhysicalTimeModulus_implies_strongH3Trace`
- `H3AuditInitialPhysicalZeroJetLinearRateData`
- `h3Audit_linearTimeModulus_tendstoRight_zero`
- `h3Audit_initialPhysicalLinearRate_implies_timeModulusData`
- `h3Audit_initialPhysicalLinearRate_implies_strongH3Trace`
- `h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialPhysicalTimeModulus`

## Logical boundary

These are conditional functional-analytic and initial-data reductions, not a derivation of an initial physical rate from the open-time PDE class. The terminal vorticity endpoint and external continuation criterion are separate assumptions. No `sorry`, `admit` or new `axiom` statements. Authoring environment lacks Lean compilation; validate with the local Rocky Linux `lake` toolchain.
