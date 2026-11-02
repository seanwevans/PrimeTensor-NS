# Physical H³ annular clock compression or superquadratic PDE rate

Baseline: `ee3adb9c` — bound physical H3 annular PDE persistence by terminal dissipation.

## Quantitative improvement

Let the existing synchronized witnesses have spike threshold
`H(k) = R(k)^2 epsilon(k)^2/8`, lower cutoff `L(k)`, upper cutoff `N(k)`,
source-window time remaining `d(k) = t(v(k)) + w(v(k)) - p(k)`, and actual
projected-PDE annular variation rate

```
Lambda(k) = h3PathFiniteAnnulusPDEVariationCoefficient244
  (L(k)+1) (N(k)+1)
  ‖actual weighted spectral velocity at sState(k)‖
  ‖actual projected momentum source at sSource(k)‖.
```

The preceding module constructs `theta(k) = min(d(k)/2,
H(k)/(8*(Lambda(k)+1)))` on active annular indices and zero otherwise.
Physical finite terminal H³ dissipation makes
`theta(k)*H(k)/4 -> 0` and its series summable.

This module now derives, **for every** constants `c>0` and `M>0`, at all
sufficiently late indices:

```
  inactive(k)
    OR  d(k)*H(k) < c
    OR  M*H(k)^2 < Lambda(k)+1.
```

The last disjunct is a genuinely **superquadratic necessary PDE rate** if
`d(k)*H(k)` stays bounded away from zero and the annular branch remains
active. More precisely, no uniform `Lambda(k)+1 <= M*H(k)^2` is compatible
with a noncollapsing `d(k)*H(k)` on all late active indices. The scalar
corollary proves that such an eventual normalized-rate ceiling forces
inverse-height source-window compression instead.

## Scope

* Same cofinal fivefold witnesses, source and state maxima, and four-way gate.
* Uses the actual annular PDE coefficient, not an assumed H³ time derivative.
* Uses finite terminal physical H³ dissipation explicitly, via the previous
  module. No statement of terminal continuation is inferred.
* Both bottlenecks remain: `d(k)*H(k)` can collapse and `Lambda(k)` can grow
  faster than `H(k)^2`; proving exclusion requires further physical estimates.

## Verification

Run the patch's audit registrar, proof index generator and its check mode,
fragment checker, targeted Lean module build, full Lake build, and baseline
audit. No shell files are included in the ZIP.
