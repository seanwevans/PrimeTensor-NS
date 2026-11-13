# Selected outer carrier: physical projected-source tail versus nonlinear Young-width loss

Expected base: `647374fef` (`force physical temporal excursions of selected outer H3 carriers`).

## Actual physical PDE transfer

The predecessor proved an unconditional half-tail physical-velocity-or-deficit excursion under finite H3 dissipation and a selected noncollapsing sixth-power terminal margin. This module consumes the actual *unconditional* positive-time physical Hilbert FTC (not a separately hypothesized time-regularity modulus):

`U(s)-U(x) = integral_x^s G(r) dr`, where `G` is the genuine projected momentum source.

Writing `S(x) = integral_x^T ||G(r)|| dr` and `V(x) = integral_x^T D_H3(r) dr`, actual source integrability and monotonicity give

`||U(s)-U(x)|| <= S(x)` for every `x <= s < T`, and thus

`||U(s)||+||U(x)|| <= 2||U(x)|| + S(x)`.

The exact sharp physical highpass polarization bound therefore charges the selected kinetic-mass excursion to

`margin < (rho^2+sigma^2) * S(x) * (2||U(x)|| + S(x))`.

The existing projected source majorant gives **without added differentiability assumptions**

`S(x) <= H(x) := (3+C_L) * ((1+6E0(b))*(T-x) + 3 V(x))`.

Combining yields the original physical-PDE three-way conclusion in a two-channel statement:

`margin < (rho^2+sigma^2) * H(x) * (2||U(x)|| + H(x))`

or a strict `epsilon` drop of the **original nonlinear annular kinetic deficit** by the terminal midpoint.

For cofinal selected snapshots satisfying `c <= margin_k * sigma_k^6 * (T-x_k)` eventually, the alternative is eventually forced and *also* `S(x_k) -> 0` by finite H3 dissipation and source L1 integrability.

## Mathematical frontier

The unweighted projected-source action vanishes, but the factor `rho_k^2+sigma_k^2` can escape and the margin can shrink. The source arm is therefore not eliminated automatically. To force actual Young-width loss, one must show the *normalized* physical source payment is small compared with the selected excess margin. To eliminate the remaining Young-width arm, one needs a compatible nonlinear modulus in a moving annulus. Nothing here establishes a Navier--Stokes continuation theorem.

## Lean statements

1. `thirdFullPhysical_outerSourceTail_controlsVelocityIncrement244`
2. `thirdFullPhysical_outerMassExcursion_forcesSourceTailCost244`
3. `thirdFullKinetic_sourceTail_quadraticMonotonicity244`
4. `thirdFullPhysical_outerSourceTail_le_kineticViscousBudget244`
5. `thirdFullPhysical_selectedOuter_lowHalfTail_forcesSourceOrDeficit244`
6. `thirdFullPhysical_selectedOuter_lowHalfTail_forcesViscousSourceOrYoung244`
7. `thirdFullPhysical_cofinalOuterSourceTail_tendsto_zero244`
8. `thirdFullPhysical_cofinalSelectedOuterMargins_forceSourceOrYoung244`

No new axioms, `sorry`, or `admit` are introduced. Requires compilation in the repository's pinned Lean/mathlib environment.
