# Actual physical initial-time derivatives imply the FTC-control contract

Parent checkpoint: `9ad5ab94` — `derive initial physical H3 modulus from temporal FTC bounds`.

## What is proved

`OneComponentInitialPhysicalDifferentiatedFTC.lean` constructs an initial-anchored physical zeroth-velocity L² path equal to the **actual old velocity** at strict physical times and to the actual initial L² jet at zero. Under `ContinuousOn` at `[0,t]`, a strong Banach-space `HasDerivAt` source on `(0,t)` and interval integrability, Mathlib's `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` proves the physical L²-valued FTC identity.

For H³ energy, `H3OrderEnergyDerivativeIdentities u s` supplies `HasDerivAt (velocityH3EnergyAt u) (velocityH3FormalDerivativeAt u s) s`. This and the matching continuity/integrability supply the scalar energy FTC with the *actual canonical* source. The inherited bounded sources yield the prior linear modulus, the actual initial H³ Fourier trace, and, with the independent terminal vorticity hypothesis, full-time L²_t Ḣ^(3/2)_x for the transverse components.

## New declarations

- `h3AuditInitialPhysicalZeroJetAnchored`
- `h3AuditInitialPhysicalZeroJetAnchored_eq_at`
- `h3AuditInitialPhysicalZeroJetAnchored_eq_zero`
- `h3Audit_initialPhysicalZeroJet_FTC_of_hasDerivAt`
- `h3Audit_initialPhysicalH3Energy_FTC_of_orderwiseDerivatives`
- `H3AuditInitialPhysicalZeroJetDifferentiatedFTCData`
- `h3Audit_initialPhysicalDifferentiatedFTC_implies_FTCControlData`
- `h3Audit_initialPhysicalDifferentiatedFTC_implies_strongH3Trace`
- `h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialDifferentiatedFTC`

## Honest boundary

The initial anchored continuity, strong physical L² derivatives, source integrability/boundedness, and the orderwise energy derivatives on intervals reaching zero are **explicit hypotheses**, not inferred from the open-time NS admissibility class. Therefore this is an FTC identification step, not closure of the initial-value PDE frontier. The independent terminal strong-vorticity endpoint and external continuation implication are still unresolved in this branch. No `sorry`, `admit`, or new axioms.
