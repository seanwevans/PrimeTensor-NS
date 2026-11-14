# Selected outer H³ carrier: exact viscous-only and Leray two-step energy decomposition

Base commit prefix: `ca67c9754` (`split selected outer highpass drain into signed viscous and Leray work`).

## Exact physical statement

For `0 < x <= s < T`, let `P_>=rho` be the established real physical sharp
highpass and define:

- `H_x = P_>=rho u(x)`, `H_s = P_>=rho u(s)`;
- `A_D = P_>=rho (integral_x^s Delta u(t) dt)`;
- `A_N = P_>=rho (integral_x^s Leray(u(t)) dt)`.

Here `Delta u - Leray(u)` is the repository's **actual** projected momentum
source and all integrals are actual physical Bochner integrals. The preceding
SignedSourceWork module establishes both source-component integrability and
the unconditional physical momentum FTC.

Consequently, `H_s = H_x + A_D - A_N`. Applying the exact Hilbert square
identity twice, or polarizing around `H_x + A_D`, yields

```
||H_x||² - ||H_s||²
  = (||H_x||² - ||H_x + A_D||²)
    + 2 <H_x + A_D, A_N> - ||A_N||².
```

The first bracket is the *viscous-only increment's energy loss* (a signed
quantity). The second pair of terms is the true **signed nonlinear Leray
contribution**, including its nonpositive quadratic correction.

This is not a heat-semigroup identity: `A_D` contains the time-dependent
Laplacian of the *nonlinear* path, not the Laplacian of an independent heat
solution. In particular, the first bracket is not proved nonnegative.

## Leray transfer threshold

If the actual highpass kinetic drain strictly exceeds the signed viscous-only
energy loss, then necessarily

```
||A_N||² < 2 <H_x + A_D, A_N>
```

and the right pairing is strictly positive. This identifies the sign and
quantitative minimum required of the nonlinear component, not merely of the
total source norm.

Likewise, if a previously derived selected no-Young-growth obstruction
requires `epsilon < K*(||H_x||²-||H_s||²)` with `K>0`, but the viscous-only
contribution is bounded above by `epsilon`, then the Leray pairing is
strictly positive. This is a **conditional gate** whose remaining analytic
obligation is to quantify the viscous-only payment.

## Frontier

Obtain a coercive or one-sided bound for the *actual* integrated viscous
increment `A_D`, using sharp Fourier heat dissipation plus a temporal
commutator. Without that estimate, positive Leray transfer is an alternative,
not a contradiction or a proof of terminal H³ continuation.

No new axioms or proof holes are intended. The Lean file needs validation
against the project's pinned Lean and mathlib toolchain.
