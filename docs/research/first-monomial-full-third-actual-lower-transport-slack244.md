# Exact actual lower-transport slack and the joint signed cubic

Base: `98985992` (`master` after removing all root-level one-off scripts).

## Why this is the next bridge

The preceding fixed-channel terminal obstruction concerns two individually
normalized signed quantities, `X_G` (the 972-gradient completion) and `X_I`
(the physical multiplicity-three 243-interpolation completion). Both were
formed by charging half of a worst-case `24 C1 sqrt(E) E` lower-order
transport allowance and one copy of the actual dissipation.

This is a *majorant*, not the exact physical energy rate. The excess can be
large because the lower-order bound is slack even when the actual lower-order
transport has the favorable sign. We now identify the slack exactly.

On every strict energy-class time of the actual unforced Navier–Stokes path,
write `E = velocityH3EnergyAt u t`, `D = velocityH3DissipationAt u t`,
`T_k = velocityH3TransportDerivative{k}At u t`. The established order-zero
convective cancellation, signed lower-order estimate, and exact PDE balance
read

```
T_0 = 0
|T_1+T_2| <= 24 C1 sqrt(E) E
E' + 2D = -(T_1 + T_2 + T_3).
```

Define the real, physical lower-order slack

```
L = 24 C1 sqrt(E) + (T_1+T_2)/E.
```

Then the new Lean module proves all of the following pointwise equalities and
bounds:

```
0 <= L <= 48 C1 sqrt(E)
signedThirdRate = E'/E + L
X_G + X_I = E'/E - 4422 + L
Q + X_G + X_I = 4422 C1 sqrt(E) + L,
```

where `Q` is the existing *effective physical Riccati defect*, not a newly
postulated spectral expression.

## Stronger continuation frontier via signed cancellation

Earlier results showed continuation if **both** channels admit integrable
a.e. upper majorants. We now need only an integrable a.e. upper majorant of
the **sum** `X_G + X_I` on one genuine preterminal energy-class tail. The
proof uses the measurable physical unabsorbed Riccati rate (not any assumed
measurability of the individual spectral channels) and the pointwise bound

```
0 <= U <= max(0, X_G+X_I).
```

Thus, given `X_G+X_I <= r` a.e. with `r` integrable, the actual rate is
majorized by `|r|`, which is integrable, and the existing smooth-continuation
theorem applies. Conversely, hypothetical nonextension excludes every such
integrable joint envelope on every strict terminal subtail.

**Scope:** none of these conditional statements proves an unconditional PDE
lower bound for `Q`, an integrable joint signed envelope, or global
Navier–Stokes regularity. The precise remaining issue is estimating the
actual dynamical signed cancellation/defect, not static Schwarz absorption.
