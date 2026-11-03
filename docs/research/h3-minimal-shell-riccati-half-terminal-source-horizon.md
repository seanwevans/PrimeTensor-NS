# Minimal-shell physical source peaks: the intrinsic half-terminal Riccati horizon

**Accepted baseline:** `aaecc40f` — exact last-shell overshoot or physical Laplacian/Leray excursions.

## New analytic estimate: short horizon implies an actual source ceiling

Write `E(t) = velocityH3EnergyAt u t`, `K = h3PathSqrtEnergyRiccatiCoefficient >= 0`, and `C_L = h3AuditInitialLerayEnergyCoefficient >= 0`. The existing full physical H³ energy-class result proves monotonicity of

    t ↦ 1/sqrt(E(t)) + (K/2)*t.

Thus for `t<=s<T`,

    1/sqrt(E(t)) <= 1/sqrt(E(s)) + (K/2)*(s-t).

If `E(s)>4 E(t)`, elementary *strict* square-root comparison forces

    1 < K*(s-t)*sqrt(E(t)).

For the **canonical half-terminal source window**

    I(t)=[t, t+(T-t)/2],

we have `s-t <= (T-t)/2`; hence

    K*(T-t)*sqrt(E(t)) <= 2

rules out every fourfold increase at all times `s in I(t)`:

    E(s) <= 4 E(t).

The accepted actual Fourier-physical source majorant gives

    ||P(s)|| <= (3+C_L) E(s),
    P(s)=Delta u(s)-Leray(u·grad u)(s).

Because the canonical source envelope is an **attained** maximum of `||P(s)||` on the compact interior interval `I(t)`, the stronger, literal endpoint estimate follows:

    CanonicalSourceEnvelope(t,I(t)) <= 4 (3+C_L) E(t).

No uniform terminal source modulus, source time derivative, endpoint H³ trace, or finite terminal full-H³ dissipation is used. Its failure implies

    2 < K*(T-t)*sqrt(E(t))

and therefore the quantitative lower terminal energy concentration

    4 < K^2*(T-t)^2*E(t).

## Same-selector physical obstruction

The previous minimal-shell source-pressure branch retained a *literal occupied last integer Fourier shell* at original first crossing `N=m+1` and an actual projected source observation on `I(t)`. At each prescribed `D,L>=0`, eventually a Riccati-heavy window therefore satisfies one of:

1. `R^2 < 4(4K^2+1) E(t)` (quadratic original-anchor energy),
2. `D*R < m+2`, with `omega>0`, `mu>0`, and `omega/(4(N+2)^8) <= mu` for the genuine last-shell kinetic mass,
3. `L < 4(3+C_L) E(t)` (actual H³ anchor pays the proposed source threshold),
4. `4 < K^2*(T-t)^2*E(t)` (the exact inverse-square terminal anchor-energy rate).

All `t,N,m,C,delta,v` are the original minimal first-crossing witnesses. The terminal source observation is on the **half-terminal source interval**, which need not fit inside the shorter disjoint dissipation window. The alternative is eventual **for each fixed D,L**, not simultaneously for all D,L at one index.

The complementary unbounded-cubic-charge arm is preserved without requiring the positive signed-gap budget. No unconditional Riccati recurrence, uniform last-shell overshoot fraction, or Navier–Stokes smooth continuation follows.

## Next analytic obstruction

The physical source-escape arm is now reduced to either H³ anchor expenditure or the precise terminal rate `E(t) > 4/(K^2 (T-t)^2)` (when `K>0`), instead of an unconstrained diffusion/Leray jump. This can be matched against the minimal Fourier carrier and the exact cubic dissipation charges in a later step. Proving that they are incompatible still requires genuinely new PDE information.
