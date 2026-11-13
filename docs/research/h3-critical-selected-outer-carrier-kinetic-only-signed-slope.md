# Selected outer H³ carriers — kinetic-only signed slope cancellation

Expected base: `7a69b0d85`, containing `OuterCarrierOneSidedYoung`.

## The new analytic point

The established early-anchored identity is

    G(x) - G(s) = (M_x - M_s) * Q_x(x,s) + M_s * (Y_s - Y_x),
    Q_x(x,s) = w a [a(M_x+M_s)-2B] - (Y_x + w P).

Here `a=(rho²+sigma²)/2`, `w=(rho²)^3`, `B>=0` is the fixed
physical low-band source ceiling, `P>=0` the viscous baseline, `M>=0`
the sharp highpass kinetic square mass and `Y>=0` the ORIGINAL nonlinear
annular Young-width cost. The selected snapshot has `M_x>0`, kinetic
excess `E_x=a M_x-B>=0` and annular deficit `G(x)>=0`.

### 1. The signed cancellation (no H³ Young envelope)

If `M_s<=M_x`, then

    Q_x <= w a [a(M_x+M_s)-2B] <= 2 w a E_x.

Thus its positive source-slope payment is at most

    (M_x-M_s) Q_x <= 2 w a E_x |M_x-M_s|.

If `M_s>=M_x`, the established one-sided polarization theorem derives
`Q_x>=0` from `E_x>=0` and `G(x)>=0`; hence the source-slope payment is
**nonpositive**. Both cases give the universal signed estimate

    (M_x-M_s) Q_x <= 2 w a E_x |M_x-M_s|.

This is strictly a one-sided estimate: it would generally be false as
an absolute-value bound for Q. It uses the sign of the positive initial
deficit and nonlinear cost. It is why the H³ snapshot Young-envelope
terms disappear from the upper bound.

### 2. Physical radius-only bound

The actual momentum FTC bounds sharp highpass mass variation by

    |M_x-M_s| <= A_x,
    A_x := H_x [2 ||V_x|| + H_x],

where `H_x` is the existing kinetic-anchored physical projected-source
terminal budget. For `0<rho<=sigma`, sharp highpass projection and
`a<=sigma²`, `w<=sigma^6`, `B>=0` imply

    2 w a E_x <= 2 (sigma²)^5 ||V_x||² =: K_x(sigma).

Therefore any deficit loss `G(x)-G(s)>epsilon` forces

    epsilon - A_x K_x(sigma) < M_s (Y_s-Y_x).

In particular, if `A_x K_x(sigma)<=epsilon`, the ORIGINAL Young-width
cost increases strictly: `Y_s>Y_x`.

No Fourier cubic Young/residual norm appears in `K_x`. This is a genuine
use of the signed polarization, not a new upper envelope assumption.

### 3. Cofinal formulation and what is still open

For selected cofinal snapshots with non-collapsing sixth-power time scale,
finite actual H³ dissipation enforces the familiar mass-transport branch
or a positive signed Young residual, but its source price is now **only**

    2 (sigma_k²)^5 ||V(x_k)||² A(x_k).

The unweighted projected-source tail tends to zero. Proving a suitable
moving-radius weighted product tends to zero is still open; no Navier–Stokes
continuation result is asserted. This package does not invent an H³ trace,
uniform frequency tightness, or a PDE source derivative bound.

## Lean results

Theorems:
- `thirdFullKinetic_earlyYoung_sourceSlope_kineticOnly244`
- `thirdFullKinetic_earlyYoung_kineticOnlyResidual244`
- `thirdFullKinetic_earlyYoung_kineticSlope_radiusCap244`
- `thirdFullPhysical_outerDeficitDrop_kineticOnlySlopeResidual244`
- `thirdFullPhysical_selectedOuter_lowHalfTail_kineticOnlyYoungResidual244`
- `thirdFullPhysical_selectedOuter_kineticOnlySlopeSmall_forcesYoungGrowth244`
- `thirdFullPhysical_cofinalOuter_kineticOnlyYoungResidual244`

Definition: `thirdFullPhysicalOuterKineticOnlySlopeCap244`.

All proofs are written without `sorry`, `admit`, or new axioms. The local
Lean/mathlib toolchain is not available in the authoring container, so
compilation must be performed by the pinned project build script.
