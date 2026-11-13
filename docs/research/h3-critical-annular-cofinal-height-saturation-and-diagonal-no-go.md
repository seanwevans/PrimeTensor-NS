# The saturated inner-annular clock and the diagonal excess obstruction

Base: `a8a0f834697ae47d373ab5058dac4966ee454dd2`.

## Decisive correction to the previous cofinal argument

The accepted finite-radius annular window theorems require a strict kinetic
excess margin *for every* `rhoMin <= rho <= sigma <= R`. **This premise is
impossible**, because the rectangular family includes `sigma = rho`. The
new Lean theorem `thirdFullPhysical_boundedAnnularUniformExcess_impossible244`
formalizes that incompatibility for the actual physical quantities, rather
than propagating a vacuous hypothesis any further.

Let `E_b = velocityH3Energy0At u b`, `M_rho(t)` be the actual sharp physical
highpass kinetic mass and

    S_rho(E_b) = rho^2 * sqrt(E_b)
      + sqrt(volume(B_rho) * (18*rho*E_b)^2).

Already-proved physical estimates are

    0 <= M_rho(t) <= E_b,      S_rho(E_b) >= rho^2*sqrt(E_b).

Consequently the strict excess condition

    sqrt(E_b)*3*S_rho(E_b) + margin
      <= ((rho^2+sigma^2)/2) * M_rho(t), margin>0

forces `E_b>0` and then

    3*rho^2*E_b + margin <= ((rho^2+sigma^2)/2)*E_b,

so that **`sigma^2 > 5*rho^2`**. In particular `sigma=rho` is impossible.

A nonvacuous replacement must restrict the family to separated annuli
(`sigma^2 > 5*rho^2`) or pass to individually selected annular witnesses.
No existence of such witnesses is assumed or proved here.

## Saturation of the physical cap-normalized height

The exact cap slope in the repository is

    slope(H) = 12*kappa^2*(1+6*E_b) + 18*kappa^2*H,
    kappa = 3+h3AuditInitialLerayEnergyCoefficient > 0.

Thus, for `E_b>0`, `rho>0`, and `H>=0`, the self-calibrated height obeys

    H/max(1, E_b*rho^6*slope(H))
      <= 1/(18*E_b*rho^6*kappa^2).

The RHS is *independent of H*. It is the saturation barrier to using
arbitrarily large deficit thresholds to produce critical inverse-terminal
heights.

If `x_k -> T`, `x_k < T`, `rho_k >= rhoFloor>0`, `H_k>0`, then

    (T-x_k) * H_k/CapClockFactor(b,rho_k,H_k) -> 0

without invoking finite H3 dissipation or positive clock widths. The same
conclusion follows if a sequence of actual, **selected** annular strict-excess
witnesses supplies the kinetic-anchor positivity. Unlike the old rectangular
hypotheses, selected witness hypotheses are not algebraically contradictory.

## Research status

This module does not establish three-dimensional Navier--Stokes continuation.
It exposes two independent limits of the previous approach: the full-family
margin assumption is empty, and the self-calibrated clock cannot produce a
critical inverse-terminal height at positive lower inner radius. The next
mathematical step must work with genuinely separated annuli and a different
physical mechanism for noncompressing charge.

## Registered declarations

- `thirdFullPhysicalAnnularClockSaturationCeiling244`
- `thirdFull_scalar_affineCapHeight_saturation244`
- `thirdFullPhysical_annularClockSaturationCeiling_pos244`
- `thirdFullPhysical_annularClockHeight_le_saturation244`
- `thirdFullPhysical_annularClockHeight_le_fixedInnerSaturation244`
- `thirdFullPhysical_strictAnnularExcess_forces_anchor_pos244`
- `thirdFullPhysical_cofinalClockHeight_autoSubcritical244`
- `thirdFullPhysical_cofinalClockHeight_noCriticalFloor244`
- `thirdFullPhysical_strictAnnularExcess_forces_radialSeparation244`
- `thirdFullPhysical_strictAnnularExcess_noDiagonal244`
- `thirdFullPhysical_boundedAnnularUniformExcess_impossible244`
- `thirdFullPhysical_cofinalSelectedExcess_autoSubcritical244`
