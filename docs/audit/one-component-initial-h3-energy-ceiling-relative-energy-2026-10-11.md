# Initial old physical L² ceiling from actual H³ energy

Base checkpoint: `b32c8d70` — derive initial comparison bounds from physical kinetic energy.

The previous initial comparison assumed an old physical L² kinetic bound. This module uses the **actual positive-time spectral H³ encoder** and the existing exact physical Fourier decoder to prove

`‖h3AuditInitialOldPhysicalHilbertTotal hH3 t‖ ≤ 3 * sqrt (velocityH3EnergyAt u t)`

for every strict physical time `t ∈ (0,T)`. Consequently any uniform upper ceiling `velocityH3EnergyAt u t ≤ E` on `(0,b)` gives an old physical kinetic norm ceiling `3 * sqrt E`; the selected canonical mild path is already bounded by `6 * A`.

The new `H3AuditInitialCanonicalH3EnergyCeilingRelativeEnergyData` contract retains initial H³ snapshot compatibility, old physical Hilbert time measurability, an actual **uniform early-time H³ energy bound**, continuous approximate comparison coefficients, and arbitrarily small integrated absolute PDE residuals. The energy ceiling, measurability, and PDE relative-energy inequality are **not** derived from open-time admissibility here.

### New declarations

- `h3Audit_initialOldPhysicalHilbert_norm_le_sqrtH3Energy`
- `h3Audit_initialOldPhysicalHilbert_norm_le_of_H3EnergyCeiling`
- `H3AuditInitialCanonicalH3EnergyCeilingRelativeEnergyData`
- `h3Audit_initialH3EnergyCeiling_implies_oldKineticData`
- `h3Audit_initialH3EnergyCeiling_implies_compactWeakComparisonData`
- `h3Audit_initialH3EnergyCeiling_implies_physicalZeroJetAndEnergyUpper`
- `h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialH3EnergyCeiling`

The full-time two-component result still requires a separate actual-vorticity strong-H³ terminal endpoint; no unconditional Navier–Stokes global-regularity conclusion is claimed.
