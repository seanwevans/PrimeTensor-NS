# Terminal H3 minimal first-crossing carrier and attained physical source

**Baseline:** `6a349bce4c2ca3140621e87588d742ce7c2fe272`

The prior terminal H3 nontrace theorem constructs an arbitrarily high physical
high-radial dissipation snapshot, but its finite-annulus outer cutoff may be
unnecessarily large. In the linear/quadratic PDE rate coefficients that could
manufacture apparent outer-frequency amplification.

## Minimal first crossing

At each actual strict time `t`, for each positive requested height `A`,
choose the **least** natural number `N >= n` such that the real physical
annular H3 viscous dissipation

    B_N(t) = D_low(N+1,t) - D_low(n+1,t)

is greater than `A/2`. For each `n <= m < N`, `B_m(t) <= A/2`.
The existing fixed-band continuity and physical Hilbert FTC arguments yield
the same actual anchored PDE clock, but now at this first crossing.
The projected momentum source coefficient is the **attained** maximum

    C(t) = max_{s in [t,(t+T)/2]} ||Delta u(s) - P(u . grad u)(s)||_(L2).

The width is exactly

    delta = min((T-t)/4, 1,
                (B_N(t)-A/4)/(2*(Lambda+Xi+1))).

The persistence floor is `A/4` and its real viscous charge is integrated
on the same physically selected annulus.

## Occupied carrier shells

The last shell `m=N-1` has **strictly positive raw Fourier kinetic mass**.
The correct quantitative inequality charges only the crossing overshoot:

    B_N(t)-A/2 <= 4*(N+2)^8 * RawMass_[m+1,N+1](t).

The overshoot can be arbitrarily small. We do not assert a positive
frequency-independent mass floor for the last shell.

A bandwidth-averaging argument gives **some** (possibly different) shell
`n <= j < N` such that

    A/2 < (N-n) * 4*(j+3)^8 * RawMass_[j+1,j+2](t).

This is an actual physical raw-kinetic Fourier carrier, not just a nonzero
weighted H3 dissipation integral.

## Cofinal terminal alternative

For **any** `M_n > 0`, `M_n -> infinity`, no strong H3 terminal trace and
finite total full H3 dissipation produce cofinal pairwise-disjoint physical
windows preserving the exact minimal outer cutoff, canonical attained source,
positive last shell, width-averaged occupied shell, and summable charge

    sum_k delta_(v(k)) * M_(v(k))/4 < infinity.

On the same sequence, the previous genuine physical rate alternative remains:

    (T - tau_k)*M_k < 4, or
    M_k^2 < 384*K_k*C_k*((Q_k+1)^5+(R_k+1)^5)+8, or
    M_k^2 < 576*C_k^2*((Q_k+1)^8+(R_k+1)^8)+8.

The `C_k > S` alternative is witnessed at an actual physical time on the
compact half-terminal source interval, without ceiling-efficiency assumptions.

## What remains open

Minimality prevents inflating Q by arbitrary choice, but does not bound Q/R.
The occupied last-shell mass has no uniform positive floor; a far shell
might carry extremely little raw mass while paying high derivative viscosity.
Also terminal-clock compression and physical-source growth remain possible.
No Navier-Stokes global regularity theorem is asserted.

## Verification

The registrar checks the new declarations and scans for proof placeholders.
Lean compilation itself must run in the user's repository; no local Lean
compiler is provided by this execution environment.
