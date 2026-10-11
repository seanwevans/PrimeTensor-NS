# Automatic old physical L² temporal measurability on (0,T)

**Base commit:** `4896cf7c` (`derive initial energy ceiling from independent right trace`).

New Lean module: `PrimeTensor/Fluid/Vorticity/Continuation/H3/Audit/OneComponentInitialAutomaticOldTimeMeasurability.lean`.

## Change to the proof frontier

The previous initial-relative-energy criterion required a separate `AEStronglyMeasurable` proof for the old physical Hilbert velocity on `(0,b₀)`. This module derives it from `LoggedPreterminalH3PathAdmissible u T` without reference to the initial-time energy comparison, using:

1. `h3Audit_actualPositivePhysicalZeroJet_eq_spectralRealDecode` to identify actual physical L² velocity with real Fourier decoding of its actual spectral state.
2. `h3Audit_preterminalSpectral_continuousOnElapsed_of_h3Path` to obtain strong spectral continuity on strict local restart windows.
3. `continuous_h3SelectedPhysicalL2HilbertDecode` to transfer continuity to the complete three-component physical Hilbert state.
4. The same local-to-global interval reasoning already audited for homogeneous Sobolev time densities in `OneComponentGlobalTimeMeasurability.lean`.

The resulting public theorem `h3Audit_initialOldPhysicalHilbert_aestronglyMeasurableOnInitial` removes the old-velocity measurability field from `H3AuditInitialCanonicalRightEnergyTraceNoMeasurabilityData`. Conditional compact weak-test agreement and initial physical trace then follow via the previously checked right-energy-trace criterion.

## Still independent

The finite right actual H³ energy trace, zero-data compatibility, coefficient upper bound, and vanishing-residual Navier–Stokes weak–strong comparison are **not** derived from `LoggedPreterminalH3PathAdmissible`. Nor is the terminal strong-H³ actual-vorticity condition. There is no unconditional Navier–Stokes regularity claim.

## Local verification

Run `lake env lean PrimeTensor/Fluid/Vorticity/Continuation/H3/Audit/OneComponentInitialAutomaticOldTimeMeasurability.lean`, `lake build`, `python3 proof/generate_index.py`, and `bash tools/audit/baseline.sh --reuse-build`. Lean compilation has not been executed in the artifact preparation environment.
