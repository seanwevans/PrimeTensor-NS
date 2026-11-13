# Selected outer carrier: exact signed Young-width gain versus physical source-tail slope

Expected base commit: `4cfe1c78a` (`charge selected outer H3 carrier excursions to physical source tails`).

## New mathematical step

For a genuine selected annular snapshot at time `x` and a later physical time `s`, let

- `M(t)` be the actual sharp physical highpass kinetic mass at the selected inner radius `rho`;
- `Y(t)` be the **original nonlinear** physical annular Young-gap/width cost at `rho,sigma`;
- `G(t)` be the original annular kinetic deficit, not an abstract replacement;
- `a = (rho^2+sigma^2)/2`, `w = (rho^2)^3`;
- `B = sqrt(E0(b))*3*LowBandCeiling(rho,E0(b))`, and `P = OuterViscousCapBase(b,a)`.

The previously established exact two-time polynomial identity, in the **signed** orientation, is

```
G(x)-G(s) = (M(x)-M(s))*Lambda(x,s) + M(x)*(Y(s)-Y(x)),
Lambda(x,s) = w*a*(a*(M(x)+M(s))-2*B) - (Y(s)+w*P).
```

The second summand is **signed Young-width growth**, not `M(x)*abs(Y(s)-Y(x))`. This distinction matters: an absolute oscillation estimate does not force the direction of nonlinear action.

The unconditional physical Hilbert Navier--Stokes FTC and existing source bound give

```
S(x) = integral_x^T ||projected physical momentum source(t)|| dt,
H(x) = (3+C_L)*((1+6*E0(b))*(T-x) + 3*integral_x^T D_H3(t) dt),
S(x) <= H(x),
|M(x)-M(s)| <= H(x)*(2*||U(x)||+H(x))  (x <= s < T).
```

For a strict epsilon-drop of the actual deficit, the original PDE forces

```
epsilon/2 < H(x)*(2*||U(x)||+H(x))*abs(Lambda(x,s))
    OR
 epsilon/2 < M(x)*(Y(s)-Y(x)).
```

Under selected strict positive kinetic margin, positive annular deficit, and insufficient actual H3 terminal-tail dissipation, combine this with the preceding physical source-tail alternative. The result has **three** channels:

1. Direct weighted physical source action pays the selected kinetic margin.
2. Physical highpass source drift, amplified by the **exact** annular polynomial slope, pays the lost deficit.
3. The original nonlinear Young-width cost **increases positively** before the midpoint of the remaining terminal interval.

The cofinal theorem carries the three-way physical statement and records `S(x_k) -> 0` from finite dissipation, with no arbitrary rate assumptions.

An additional local conditional theorem shows that upper bounds on both *frequency-weighted* source payments imply the third channel: a forced positive signed Young-width increment. Those are explicit analytic conditions, not silently supplied by finite dissipation.

## Remaining hard mathematical obstruction

Finite H3 dissipation forces `S(x_k) -> 0` and `T-x_k -> 0`. It does **not** force products with `rho_k^2+sigma_k^2` or the moving annular slope `Lambda_k` to vanish. The genuinely new estimate needed next is to bound those frequency-amplified source payments, or directly control the signed nonlinear Young-width increase using physical Fourier triad cancellation at the moving radii. No continuation result is claimed.

## Lean interface

- `thirdFullPhysicalOuterTerminalSourceBudget244` (definition)
- `thirdFullPhysicalOuterDeficitTimeSlope244` (definition)
- `thirdFullKinetic_deficitDrop_forces_signedYoungGain244`
- `thirdFullPhysical_outerDeficitDrop_sourceSlopeOrSignedYoung244`
- `thirdFullPhysical_selectedOuter_lowHalfTail_sourceSlopeOrSignedYoung244`
- `thirdFullPhysical_selectedOuter_sourceSlopeSmall_forcesSignedYoungGrowth244`
- `thirdFullPhysical_cofinalSelectedOuterMargins_sourceSlopeOrSignedYoung244`

No new axioms and no proof placeholders. Requires verification in the repository's pinned Lean/mathlib toolchain.
