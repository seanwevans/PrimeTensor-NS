# The net physical H³ dyadic source peak and the fifth/phase highpass deficit

Base: `379162a69fc12aad46452c542bfc69295cfc25ba`.

## Why gross cubic forcing was insufficient

The accepted `379162a69` adaptive-cutoff theorem selected one genuine cubic-source
peak before quantifying over all Fourier cutoffs. Its charged quantity was
`K * D3(r)`. However the exact Navier–Stokes balance subtracts the normalized
fifth-order viscous loss and the nonnegative Fourier-phase defect. A large
*gross* source can support no top-H³ growth if these losses are equally large.

## New physical mathematical consequence

On a last-half terminal window `T-s = 2(T-t)`, suppose `D3>0` throughout,

    1 <= B*(T-t)^8*D3(t)^3,
    log B + 8 log(T-s) + 3 log D3(s) < 8 log 2 - 3 K (t-s).

The previously proved exact integrated physical action identity yields

    log D3(t) - log D3(s) > K (t-s).

Because the actual signed logarithmic rate is the derivative of `log D3`,
the ordinary mean-value inequality forces **one genuine interior time**
`r in (s,t)` with

    K < (log D3)'(r).

The Navier–Stokes identity at precisely that time is

    M3(r)/D3(r) = (log D3)'(r) + Phi5(r) + PhiPhase(r),

with `Phi5` and `PhiPhase` the repository's genuine normalized fifth and
phase action rates, both nonnegative at positive top dissipation.

For **every** (possibly subsequently selected) cutoff `rho >= 0`, the H³-native
kinetic-low/highpass forcing estimate therefore gives the strict bound

    [K + Phi5(r) + PhiPhase(r)] D3(r)
       < 2*(2*pi)^6 * [3*L_rho(E0(b)) + H_rho(r)],

where `L_rho` is the previously established low-band kinetic bound and
`H_rho` is the exact squared norm sum of the three order-three highpass
Leray forcing states. No raw velocity order-eight assumption is introduced.

If the low-frequency budget fails to pay half this true joint source charge,
namely

    6*(2*pi)^6 * L_rho(E0(b))
       <= [K + Phi5(r) + PhiPhase(r)] D3(r) / 2,

then the same time and cutoff necessarily satisfy

    [K + Phi5(r) + PhiPhase(r)] D3(r)
       < 4*(2*pi)^6 * H_rho(r).

This is stronger than the gross-peak theorem because the physical highpass
must account for **actual viscous and phase loss** as well as logarithmic
growth. The witness `r` is selected independently of all cutoff values.

## Exact frontier after this checkpoint

This result does **not** give a terminal-uniform highpass forcing upper bound
or rule out cubic-rate saturation. It isolates the remaining analytic problem:
show that solenoidal Fourier geometry, viscosity, and the critical H³ kinetic
budget make the required net highpass production impossible or sufficiently
small on some near-critical dyadic window. That estimate cannot be inserted
as an assumption disguised as an H³ consequence.

## Lean declarations

- `thirdFullPhysical_nearCriticalAnchor_forces_netSignedLogPeak244`
- `thirdFullPhysical_signedLogPlusFifthPhase_le_kineticLowHigh244`
- `thirdFullPhysical_nearCriticalAnchor_forces_adaptiveJointHighpassCharge244`
- `thirdFullPhysical_nearCriticalAnchor_forces_viscousPhaseHighpassDefect244`

No `sorry`, `admit`, or new axioms. The machine doing the canonical project
build must verify the new Lean file and its full registration audit.
