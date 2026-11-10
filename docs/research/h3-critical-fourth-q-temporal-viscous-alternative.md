# Critical H³ fourth-Q source: physical temporal or heat expenditure

**Base HEAD:** `ecea88c90359ec4609d8bda6ad9fd04c6488159e`.

## Mathematical content

The accepted `FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalFourthQHighpassCharge` constructs one actual near-critical dyadic net-growth time `r` that works for every subsequently chosen frequency cutoff. Its upper charge contains the *true* physical fourth-Q Fourier Leray forcing square mass:

    A(r) < C_low(rho) + rho^(-2) sum_j ||F4Q_j(r)||_2^2,
    A(r) = [K + Phi5(r) + Phi_phase(r)] D3(r),
    C_low(rho) = 3 (2 pi)^6 L_rho(E0(b)).

The already-proved exact strict-time physical fourth-radial PDE identity is

    F4Q_j(r) = - (d/dr) V4_j(r) - Q3_j(r).

Here `V4_j` is the actual fourth-radial velocity Hilbert path and `Q3_j` the physical *third-Q heat/velocity state*; this state carries an extra spatial derivative beyond the fifth-order viscous velocity mass. It must **not** be silently identified with that fifth-order mass.

The elementary Hilbert square estimate and the finite three-coordinate sum give

    sum_j ||F4Q_j||^2 <= 2 (T4(r) + Q3(r)),
    T4(r) = sum_j ||(d/dr) V4_j||^2,
    Q3(r) = sum_j ||Q3_j||^2.

Consequently, for every rho>0, at the **same** physical time `r`,

    A(r) < C_low(rho) + 2 rho^(-2) (T4(r) + Q3(r)),

and at least one of

    A(r) < C_low(rho) + 4 rho^(-2) T4(r),
    A(r) < C_low(rho) + 4 rho^(-2) Q3(r)

must hold. No order-eight raw Fourier velocity moment or terminal-uniform bound is newly assumed.

## What this does **not** prove

This is an exact physical PDE *alternative* and an explicit fourth-Q source upper estimate. It does **not** establish a bound of `T4` or `Q3` by fifth-order velocity dissipation. The `Q3` state involves one higher derivative than that natural dissipation; a genuine solenoidal commutator estimate, negative-order time smoothing, or further frequency localization is still required to close the critical source-versus-viscosity inequality. It does not solve the Navier--Stokes regularity problem.

## Lean declarations

- `thirdFullPhysical_fourthQSquare_le_temporalThirdQCost244`
- `thirdFullPhysical_fourthQSumSquares_le_temporalThirdQCost244`
- `thirdFullPhysical_nearCriticalAnchor_forces_fourthQTemporalThirdQBudget244`
- `thirdFullPhysical_nearCriticalAnchor_forces_temporalOrThirdQ244`
