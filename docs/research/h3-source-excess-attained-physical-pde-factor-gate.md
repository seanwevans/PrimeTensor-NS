# Fivefold source clock: attained physical PDE maxima

**Base:** `87ebe75e` — resolved cofinal H³ quartic PDE factors into physical source and viscosity.

## The actual issue with arbitrary ceilings

The previous accepted cofinal theorem selects a compact interval `[x,x+w]` and
nonnegative real ceilings `C` and `E` such that, throughout this interval,

    ||ProjectedMomentumSource(s)|| <= C,
    ||SpectralVelocity(s)|| <= E.

A large chosen ceiling need not be an actual physical observation. However,
the same repository already proves **strong time continuity** of both actual
paths on strictly preterminal intervals:

- `h3Path_actualProjectedMomentumSource_continuousOnStrict244`;
- `h3Audit_initialActualSpectralVelocity_continuousOn`.

By compactness, both norm functions attain maxima, at real (possibly
different) times `sSource` and `sState` in the ORIGINAL `[x,x+w]`.
These genuine values can be passed as the tight local coefficients to the
already accepted fivefold calibrated peak theorem. Hence

    A = 3 + C_L*(||SpectralVelocity(x)|| + ||SpectralVelocity(sState)||),
    B = 12*||ProjectedMomentumSource(sSource)||^2 + 2*(D(x)+H).

No free ceiling slack remains, although the maximizing times may not lie
in the shorter calibrated subwindow `[x,x+delta]`.

## Exact physical alternative

For each cofinal selected peak let

    H = M(v(k)) + q(v(k))/(3*(3+C_L)) > 0,
    J = velocityH3EnergyAt(x) - 1,
    S = max(1,sigma(v(k)))+1,
    P = 4*q(v(k)).

The result carries the following exhaustive alternatives:

1. An actual `H < K sqrt(E(s)) E(s)` Riccati-energy observation on the
   short calibrated source window;
2. `w <= J/H` (geometric compression);
3. `H <= 16 J S^4` (cutoff-paid cost);
4. `S < 3 + 2*C_L*||SpectralVelocity(sState)||` (ACTUAL spectral state spike);
5. `P^2 < 24*||ProjectedMomentumSource(sSource)||^2` (ACTUAL projected source spike);
6. `P^2 < 8*D(x)` (actual instantaneous H³ viscous dissipation);
7. `P^2 < 8*H` (source floor itself pays the scale).

The quantitative H³ viscosity floor and its integrated disjoint-window charge
inequality remain explicit in the returned cofinal witnesses. The real
maximizing times stay inside the original strictly preterminal windows.

## What this does NOT establish

This makes the fourth and fifth alternatives genuine **pointwise** physical
concentration instead of growth of an arbitrary loose bound, but does not
force those alternatives to hold. Geometric compression, Riccati energy,
cutoff growth, the viscous peak, and the enhanced source-floor branch remain.
Neither the integral of viscosity on the terminal interval nor the positive
lower bound on all window durations is assumed.

## Lean declarations

- `h3Critical_actualSourceSpectral_attainedCompactMaxima`
- `h3Critical_fivefoldWindow_attainedPhysicalFourWay`
- `h3Critical_noL2Trace_cofinalFivefold_attainedPhysicalPDEFactorGate`

The registrar records three checks and three axiom inspections. This archive
must be elaborated with the pinned local Lean/mathlib toolchain; static
validation does not establish successful elaboration.
