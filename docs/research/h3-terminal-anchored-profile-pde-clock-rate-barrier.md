# Endpoint H³ escape: exact physical PDE clock or quadratic rate barrier

Baseline `210c4467cc19e612ff52284a6ca761644f114bdf`.

## Main statement

Let `u` satisfy the existing logged preterminal H³ path-admissibility and
`PreterminalH3EnergyClass` hypotheses. Suppose the actual physical H³ Fourier
state has no strong terminal trace at `T`. If additionally the genuine
physical full H³ dissipation is integrable on `[a,T]`, then for **every**
positive prescribed profile `M : ℕ → ℝ` with `M(n) → +∞`, there exist:

- genuine terminal times `τ(n) → T`;
- finite annulus outer cutoffs `N(n) ≥ n`;
- actual physical spectral input ceilings `K(n)` and projected-source
  ceilings `C(n)` on the selected intervals;
- positive windows of **exact anchored PDE width** `δ(n)`; and
- a cofinal strictly increasing index selection `v(k)` with disjoint windows.

At each `n`, the finite annulus has initial viscous height `Bₙ > Mₙ/2`,
and throughout the chosen interval its dissipation remains `> Mₙ/4`.
Define

    Λₙ = h3PathFiniteAnnulusPDEVariationCoefficient244
        (n+1) (N(n)+1) Kₙ Cₙ,
    Ξₙ = h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
        (n+1) (N(n)+1) Cₙ.

The selected width is not arbitrary:

    δₙ = min { (T-τₙ)/4, 1, (Bₙ-Mₙ/4)/(2(Λₙ+Ξₙ+1)) }.

For the disjoint selected windows, the actual physical dissipation integral
bounds every finite partial sum of `δ(v(k))*M(v(k))/4`. Hence the real
nonnegative series is summable and these weighted widths converge to zero.
Because `M(v(k)) → +∞`, sufficiently late indices have `M(v(k)) ≥ 1`
and `δ(v(k))*M(v(k)) < 1`. The sharp minimum formula forces

    (T-τ(v(k))) * M(v(k)) < 4

**or**

    M(v(k))² < 8 * (Λ(v(k)) + Ξ(v(k)) + 1).

The second implication uses the strict height gap
`Bₙ-Mₙ/4 > Mₙ/4`, so it is genuinely quadratic in the arbitrary
prescribed viscous height.

## What remains open

The disjunction is a **necessary** condition on missing H³ endpoint traces,
under an additional finite dissipation hypothesis. Neither branch is ruled
out by these theorems: terminal clocks may collapse superfast, and actual
physical source-dependent PDE rate coefficients may grow fast. The next
mathematical task is to constrain the **cofinal selected** `Λ, Ξ` through
physical source/transport budgets and the geometry of the outer annulus.

The source and H³ norm ceilings are not uniform in `n`; the choice of times,
outer radii and widths depends on the prescribed profile. The construction
neither asserts integrability of full dissipation nor solves Navier--Stokes
continuation.
