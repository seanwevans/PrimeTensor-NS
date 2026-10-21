# Genuine Navier–Stokes signed Fourier excess and terminal-width forcing

Base checkpoint: `12dbc4c2` — exact physical Fourier-variance secants.

## From formal energy rates to the actual momentum PDE

The preceding module identifies a real mean-value point where

    X(r)/(E0(r)*D3(r))^2 = (R(s)-R(t))/(t-s),
    R = 1 - E2^2/(E0*D3),

and `X` uses the formal order-zero/order-two energy rates, plus an actual
fourth-radial Hilbert inner-product formula for `D3'`. The repository's
`velocityH3FormalDerivative0At_eq_pde` and
`velocityH3FormalDerivative2At_eq_pde` already identify those two formal
coefficients with genuine preterminal momentum-equation pairings:

    E0' = velocityH3PDEDerivative0At u p r,
    E2' = velocityH3PDEDerivative2At u p r.

This patch packages the exact PDE signed excess

    X_PDE = 2 E2 E2'_PDE E0 D3
          - E2^2 (E0'_PDE D3 + E0 D3'_Hilbert)

with `D3'_Hilbert` the already-proven sum of fourth-radial pairings.
An explicit `PreterminalNavierStokes3` proof for the named pressure field
provides the two substitution identities at all strict class times; there is
no new differentiability assumption.

## Sharp Young forcing, now in physical PDE variables

The previous normalized sharp Young estimate is

    R(t) ≤ 256 δ/(27 K^4 E0(t))

for a positive `K`, positive physical kinetic/top-dissipation masses,
and sharp Young deficit at `t` at most `δ`. Therefore for any `s<t`,
the exact physical mean-value theorem provides an `r ∈ (s,t)` with

    X_PDE(r)/(E0(r) D3(r))^2
       ≥ [R(s) - 256 δ/(27 K^4 E0(t))]/(t-s).

If the earlier positive variance is at least `η>0` and the normalized
later Young upper bound is at most `η/2`, then

    X_PDE(r)/(E0(r) D3(r))^2 ≥ η/[2(T-s)].

The terminal-width inequality uses only `s<t<T`; the witness is still
strictly inside `(s,t)`. The use of `T-s` removes dependence on the exact
later sampling time and exposes the reciprocal terminal-width burden of a
fixed fractional variance loss. One cannot conclude unconditional rate
blowup from this inequality without a lower bound on `η/(T-s)` along an
approaching-terminal family of anchors.

## Remaining analytic work

The PDE pairings contain diffusion, pressure, and signed transport. The
difficult task is a quantitative comparison of these terms (including the
fourth-radial derivative) that rules out the necessary signed PDE production.
The present theorem does not control that sign, establish any rate ceiling,
or imply Navier–Stokes continuation.

## Audit

The registrar adds the module to the root and central triad audit, registers
`#check` and `#print axioms` for two definitions and four theorems, and is
idempotent. Run proof-index generation and fragment checks, module build,
central audit build, full build, and baseline audit before committing.
