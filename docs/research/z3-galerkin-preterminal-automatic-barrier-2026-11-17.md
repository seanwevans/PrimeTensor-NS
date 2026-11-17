# Z³ Galerkin preterminal automatic barrier and endpoint analytic trace

**Base**: `012e4ae831ca51c81e580d52207a7dccbabd58d6`.

## Mathematical obstruction resolved

An arbitrary preterminal strong finite Galerkin solution previously required
explicit analytic ball and derivative-speed certificates before the endpoint
trace theorem applied. This module derives both certificates from the genuine
ODE and the strict analytic initial ball, by localizing the existing
cutoff-independent persistence result to each compact interval `[a,t]`,
where `t < b`.

For every finite `s`, `0 <= mu <= 1/10`, `b-a <= tau`, and genuine strong
Galerkin solution `alpha` on `[a,b)`, if

    W_log(2)(alpha(a)) < 100,
    tau = (log 2 - log(9/5))/100,

then every `t` in `[a,b)` satisfies

    W_{log(2)-100(t-a)}(alpha(t)) <= 100,
    W_log(9/5)(alpha(t)) <= 100,
    ‖alpha(t)‖_Pi <= 100,
    ‖F_s(alpha(t))‖_Pi <= 51000.

This implies the preterminal 51000-Lipschitz bound. For every Cauchy
sequence `times n` in `[a,b)` *converging to b*, the complete finite state
space supplies an endpoint state `x_b`, with

    alpha(times n) -> x_b,
    ‖x_b‖_Pi <= 100,
    W_log(9/5)(x_b) <= 100,
    ‖F_s(x_b)‖_Pi <= 51000,
    dist(alpha(t),x_b) <= 51000 * dist(t,b)  for all t < b.

The final distance inequality proves uniqueness of the endpoint state among
all such sequences, and gives a rate independent of the number of modes.
The time trace must be formed using a sequence approaching `b` rather than
an arbitrary Cauchy sequence: otherwise it could merely converge to an
interior time.

## Formal dependencies

- `thirdFullThreeBand_z3MovingBall_cutoffFreePersistence244`
- `thirdFullThreeBand_z3GalerkinFiniteODE_coordinate_{continuousAt,hasDerivAt}244`
- `thirdFullThreeBand_z3MovingRadius_highBall244`
- `thirdFullThreeBand_z3GalerkinFiniteState_norm_le_of_Wiener244`
- `thirdFullThreeBand_z3GalerkinFiniteField_norm51000_100Ball244`
- `thirdFullThreeBand_z3GalerkinFiniteODE_{preterminalLipschitz51000_,endpointSequence_nonescape}244`

The new lemma `thirdFullThreeBand_z3GalerkinFiniteWienerMass_continuous244`
transfers the fixed-radius analytic ball to the trace by finite-sum
continuity, without any infinite-frequency compactness premise.

## What remains unproved

This module does **not** construct a maximal solution, establish ODE solution
uniqueness for all overlapping preterminal intervals, or restart and glue a
Picard solution at the endpoint. To obtain a cutoff-independent **existence
interval** `[a,a+tau]`, the remaining work is to form the maximal finite
ODE trajectory, use this automatic nonescape trace when a candidate maximal
endpoint lies before `a+tau`, restart at that state, and contradict maximality.
It also does not address arbitrary H³ data on R³: the analytic strict ball
and periodic Z³ geometry remain explicit.

## Validation

The source must be compiled with the repository's pinned Lean/mathlib. The
Python audit and source-registration checks are *not* proof certification.
