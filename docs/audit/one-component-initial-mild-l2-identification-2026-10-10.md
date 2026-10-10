# Initial physical mild data: identify zero value from L² right trace

Checkpoint: `b4f97cfe`, “bridge initial mild H3 trace to physical zero-time data” (2026-10-10).

## Analytic reduction

The previous `H3AuditInitialPhysicalEnergyMildZeroCompatibleData` assumed an exact equality between the spectral mild datum `U₀` and the original field's independent time-zero H³ spectral encoding. This new module proves that equality from the actual physical `L²` right trace of all three velocities, **given** the strong H³ right trace produced by the existing actual physical mild path.

The proof combines Plancherel, raw Fourier/H³ deweighting continuity, `tendsto_nhds_unique`, and `h3SpectralScalarRawFourierL2_injective`. A symmetric equivalence theorem establishes the exact logical relationship.

## New declarations

- `h3Audit_initialStrongH3Trace_identifies_initialSpectral_of_physicalL2`
- `h3Audit_initialSpectralCompatibility_iff_physicalL2RightTrace`
- `H3AuditInitialPhysicalEnergyMildL2TraceData`
- `h3Audit_initialMildL2Trace_implies_zeroCompatibleData`
- `h3Audit_initialMildL2Trace_energyRightLimit`
- `h3Audit_initialMildL2Trace_implies_physicalL2AndEnergyUpper`
- `h3Audit_initialMildL2Trace_strongH3Trace`
- `h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialMildL2Trace`

## Still unproved

The strong physical `L²` right trace to the specified old datum and the actual initial old-solution mild equation remain independent hypotheses. Open-time H³ path admissibility alone does not provide either. The strong actual terminal vorticity endpoint remains independent and is not deduced here. No unconditional global regularity or finite-time blowup conclusion is claimed.

## Verification

Source checked mechanically for `sorry`, `admit`, `axiom` declarations; ZIP integrity verified. Lean compilation must be performed on the user's Lean 4.34.0-rc1 environment.
