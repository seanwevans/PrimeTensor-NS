# Finite-radius actual annular deficit slope and common physical clock

Base commit: `70451352e66ff42e28bdf50767ea97aad1cb34fc`.

## Analytic advance

The previous module proved the exact two-time factorization

\[
D_{\rho,\sigma}(s)-D_{\rho,\sigma}(x)
 = (M_\rho(s)-M_\rho(x))\,
 [wa(a(M_\rho(s)+M_\rho(x))-2B_\rho)-(Y_{\rho,\sigma}(x)+wP_a)]
 -M_\rho(s)(Y_{\rho,\sigma}(s)-Y_{\rho,\sigma}(x)).
\]

Here `a=(rho²+sigma²)/2`, `w=rho⁶`, `M` is the **actual physical sharp-highpass kinetic mass**, `Y` is the **exact cubic-weighted nonlinear Young residual plus velocity-width cost**, `B` is the **kinetic Fourier-ball projected source**, and `P` is the **zero-viscosity physical outer budget**.

The present module bounds the slope in brackets uniformly on every family `0 ≤ rho ≤ sigma ≤ R`, provided `|M_rho(s)-M_rho(x)| ≤ 1`. The coefficient is **explicitly constructed** from:

- the actual snapshot H³ spectral state `U_x`, and its three genuine Leray anti-heat residual Fourier-L² norms;
- the actual snapshot physical L² Hilbert velocity `V_x`;
- the genuine kinetic source ceiling `S(R,E)` where `E = velocityH3Energy0At u b`;
- the already defined zero-viscosity outer budget evaluated at `R²`.

One admissible explicit slope ceiling is

\[
C_R=(R^6R^2)[R^2(2(\|V_x\|_2^2+1))+2B_R]+Y_R+R^6P_R,
\]

where `B_R=3 sqrt(E) S(R,E)`, `P_R=P(u,b,R²)`, and

\[
Y_R = 2\sum_{j<3} (2R^3\|G_j(U_x)\|_2)^2
       +2R^{10}\sum_{j<3}(2\|U_x\|_{H^3})^2.
\]

The frequency-ball monotonicity holds for **real cutoffs**, rather than only natural-index radii. No surrogate Fourier profile, `H^4` or `H^6` assumption, or unproved uniform-supremum premise appears.

## Simultaneous physical window

For a *fixed finite* `R` and a nondegenerate annular family
`0 < radiusMin ≤ rho ≤ sigma ≤ R`, suppose that at one strict physical time `x`:

1. the exact kinetic excess has uniform margin `2 margin > 0`;
2. the exact actual kinetic deficit has uniform floor `2 epsilon > 0`.

The theorem constructs **one** interval `[x,x+delta]` with `delta > 0` and `x+delta < T` such that, for every annulus in the family and every time in that interval:

- the kinetic excess retains margin `margin`;
- the actual kinetic deficit remains at least `epsilon`.

The construction chooses time-error tolerances from the proven `C_R`, not from a separately hypothesized slope bound. Existing cap-free PDE gates then give, simultaneously,

\[
\frac{\epsilon}{\operatorname{CapClockFactor}(u,b,\rho,\epsilon)}
  \leq \operatorname{velocityH3DissipationAt}(u,s),
\]

and, if the total physical dissipation is interval-integrable,

\[
\delta\frac{\epsilon}{\operatorname{CapClockFactor}(u,b,\rho,\epsilon)}
 \leq \int_a^T \operatorname{velocityH3DissipationAt}(u,s)\,ds.
\]

These are **conditional on the uniform strict snapshot margins**. The proof does not derive such margins from terminal noncontinuation, does not bound `delta` below as `R→∞`, and does not solve the Navier–Stokes global regularity problem. No new axiom or proof placeholder is introduced.
