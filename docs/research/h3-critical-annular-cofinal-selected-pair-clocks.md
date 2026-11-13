# Selected-pair annular excess, aperture margin, and cofinal clocks

Base commit: `7b75cc318f75870bf4a005aecaad1d49c931eda8`

## Repairing the mathematical obstruction

The preceding `thirdFullPhysical_boundedAnnularUniformExcess_impossible244`
proved that a strict excess margin on *every* annulus with
`rhoMin <= rho <= sigma <= R` is impossible, since the family contains
`rho = sigma`. Hence conditional downstream theorems relying on that premise
do not by themselves provide a useful PDE obstruction.

This module changes the assumption to one **selected pair** `(rho k, sigma k)`
at each cofinal physical snapshot `x k`. No universal rectangular-family
strict-excess hypothesis remains. The annular Young-width and deficit are
the original nonlinear physical quantities.

## Quantitative necessary geometry

Put `E = velocityH3Energy0At u b`, `M = actualSharpHighMass(t,rho)`,
`S = thirdFullPhysicalKineticLowBandSourceCeiling244 rho E`. The accepted
physical estimates give `S >= rho² sqrt(E)` and `M <= E`. Therefore

    sqrt(E) * 3*S + margin <= (rho² + sigma²)/2 * M

implies the explicit *margin-sensitive* aperture inequality

    2*margin <= E * (sigma² - 5*rho²).

If `margin > 0`, the already-proved anchor positivity and separation
lemmas give `E > 0` and `sigma² > 5*rho²`. The condition is necessary,
not sufficient for existence of the full annular deficit.

If, in addition, `rho > 0` and `sigma <= K*rho` for `K >= 0`, then

    6*E <= (1 + K²)*M.

Thus strict excess of bounded aspect cannot coexist with a sequence for
which the *actual selected highpass kinetic mass* tends to zero. The
vanishing-highpass hypothesis is kept explicit; a future result must bridge
the existing physical terminal L² trace to a moving real-radius highpass.

## Cofinal selected-pair window extraction

For each index `k` assume only one actual annulus `(rho k, sigma k)`
satisfying positive strict excess margin and positive original kinetic
deficit at snapshot time `x k`, with strictly increasing `x k -> T`.
The earlier fixed-annulus continuity/persistence theorem (which already
removes any separate Young-width continuity hypothesis) provides one
positive window `d0 k`. Select

    delta k = min (d0 k) ((x (k+1) - x k)/2).

It preserves the genuine excess and deficit floors on disjoint intervals.
Existing physical disjoint-clock summability and terminal-tail lemmas give

    Sum_k delta(k) * epsilon(k)/CapClockFactor(b,rho(k),epsilon(k)) < infinity
    delta(k) * epsilon(k)/CapClockFactor(...) <= integral_[x(k),T] D_H3
    integral_[x(k),x(k)+delta(k)] D_H3 -> 0.

The theorem also retains the exact aperture margin at every selected pair.
It does **not** establish existence of the snapshot margin or deficit from
Navier–Stokes, positivity of a radius-independent persistence width, or H³
continuation.

## Declarations

- `thirdFullKinetic_selectedExcess_apertureMargin_scalar244`
- `thirdFullPhysical_selectedAnnularExcess_apertureMargin244`
- `thirdFullKinetic_selectedExcess_boundedAspect_massFraction_scalar244`
- `thirdFullPhysical_selectedExcess_boundedAspect_highpassFraction244`
- `thirdFullPhysical_selectedBoundedAspect_noHighpassTightness244`
- `thirdFullPhysical_cofinalSelectedAnnularSnapshots_disjointClocks244`
