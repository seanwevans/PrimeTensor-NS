# Initial strong H³ trace from scalar energy and three correlations

Parent: `91e82084` — derive initial strong H3 trace from weak pairings and norm.

## New, nontrivial Hilbert-space reduction

The preceding `OneComponentInitialRightWeakNormTrace` assumed, for *each*
selected velocity component, convergence against *every* complex H³ test
and convergence of the component H³ norm. In contrast, this module uses:

1. one limit of the *total physical* normalized H³ energy
   `velocityH3EnergyAt u t -> 1 + Σ_j ‖U₀ j‖²` as `t -> 0+`;
2. precisely three real pairings
   `Re ⟪U_j(t), U₀_j⟫ -> ‖U₀_j‖²`, one for each velocity coordinate.

The exact weighted Fourier encoder identity
`1 + h3SpectralVelocitySquareEnergy (U(t)) = velocityH3EnergyAt u t`
is invoked at actual strict times. Polarization then proves

    Σ_j ‖U_j(t) - U₀_j‖² -> 0,

and positivity of every summand proves each strong H³ trace. This requires no
individual component norm convergence and no quantified tests against all
spectral Hilbert states. It supplies both transverse actual physical
`L²_t dot H^(3/2)_x` criteria under the previously explicit strong terminal
vorticity endpoint.

## New declarations

- `h3Audit_rightSpectralVelocity_tendsto_of_totalSquareEnergy_and_initialPairings`
- `h3AuditActualSpectralVelocityTotal`
- `h3AuditActualSpectralVelocityTotal_eq_at`
- `h3AuditActualSpectralVelocityTotal_energy_exact`
- `H3AuditInitialRightTotalEnergyAndThreePairings`
- `h3Audit_initialRightTotalEnergyPairings_implies_strongVelocityTrace`
- `h3Audit_initialRightTotalEnergyPairings_rightComplementTrace`
- `h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialTotalEnergyPairings`

## Unresolved PDE inputs

Neither right continuity of the total physical H³ energy nor the three
correlations is inferred from `LoggedPreterminalH3PathAdmissible`. Those are
meaningful initial-data questions. No local strong-solution existence,
Liu--Zhang continuation theorem, or unconditional global Navier--Stokes
regularity is formalized here.

The assistant-side environment lacks Lean/lake; the local `lake env lean` and
full project build are the required final compiler verification.
