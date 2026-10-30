# Spectral-energy gate for all-orders critical canonical PDE windows

Base commit: `2ee9db44` — generalize sharp critical physical H3 energy cost to all higher radial orders.

For a fixed m and on the exact original first-crossing windows, the prior conditional result states

    R^(16m+3) <= (512 eps²)^4 (2304 E3(t) S² + 1)^4 D^5.

The actual three-component weighted Fourier state U3 has E3(t) <= 1+3||U3(t)||² on strict physical time intervals (previously established `h3AuditActualSpectralVelocityTotal_energy_exact` and `h3Path_spectralSquareEnergy_le_threeSupSquare244`). Therefore, on the SAME selected physical anchors:

    R^(16m+3) <= (512 eps²)^4 [2304 (1+3||U3(t)||²) S²+1]^4 D^5.

Since v is strictly increasing, R³ tends to infinity. For R>=1, R³ <= R^(16m+3). A general scalar theorem proves that any inequality R^(16m+3) <= A (1+B E)^4 eventually, with A,B>=0 and nonnegative E, forces E to tend to infinity. Existing `h3Path_scalar_energyEscape_forces_threeSpectralEscape244` then transfers this to ||U3|| at the same anchors. The scalar theorem allows B=0; in that case its premises are inconsistent for cofinal R, without assuming strict positivity of the source threshold.

The physical theorem still explicitly assumes each higher-order physical radial-moment envelope F, eventual intrinsic source ceiling C<=S, critical outer-frequency cap, noncompressed weighted terminal clock and a sufficiently small fixed eps. These do NOT follow from finite H3 dissipation. This result is a conditional quantitative spectral-cost bridge, not a positive energy-growth rate estimate, not proof of integrability/nonintegrability of derivative of E3, and not a smooth continuation theorem.

Declarations:
- `h3Path_higherBudget_energyFourth_to_spectralFourth244`
- `h3Path_scalar_higherSharpEnergyCost_forces_energyEscape244`
- `h3Path_noL2Trace_exactAnchor_allOrdersCriticalBudget_spectralEnergyGate244`

The existing canonical exact energy/dissipation balance is not strengthened; positive normalized growth-rate integrability remains the separate PDE frontier.

Offline package checks only. Run the exact pinned Lean/mathlib Lake build locally.

## Local Lean correction (fix1)

The `add_le_add_right` step at the spectral-energy transfer produced
`1+x ≤ 1+y`, while the goal is `x+1 ≤ y+1`. A direct
`linarith only [hScaled]` closes the correct additive orientation.
The scalar escape argument now proves `0 ≤ R k` from the existing
`1 ≤ R k` before supplying the nonnegative multiplier `(R k)^3`;
`positivity` could not infer that fact unaided. No theorem statements,
constants or assumptions have changed.
