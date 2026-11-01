# Source-driven highpass source collapse: endpoint physical H³ dissipation pays the high-frequency displacement

Base: `80a3f0e2` (actual high-radial spectral motion forced by a physical source drop).

## Exact high-band estimate

For actual three-coordinate weighted Fourier H³ velocity states `G,H`, with frequency cutoff `R`, the scalar Hilbert inequality `|z-w|² ≤ 2(|z|²+|w|²)` implies

    H_R(G-H) ≤ 2 [ HighMass_R(G) + HighMass_R(H) ].

This is proved for the actual Lebesgue integrals on the complement of the radial ball, not for an abstract Fourier symbol, and uses only integrability of genuine weighted Fourier L² densities. The full square energy uses a three-component **sum** of squared L² coordinate norms, not the product sup norm.

The already-proven strict-time physical dissipation coercivity says for `R≥0`,

    R² HighMass_R(U(t)) ≤ D_{>R}(t).

Therefore for two actual strict energy-class times,

    R² H_R(U(t)-U(s)) ≤ 2 [D_{>R}(t) + D_{>R}(s)].

No time-continuity assumption and no H³ temporal-derivative bound is needed. Each `D_{>R}` is actual physical fourth-order viscous dissipation, not an arbitrary spectral cutoff functional.

## Closing the source-drop budget

The earlier actual physical momentum FTC and source-drop theorem give, if the projected source highpass loses margin `P≥0` between `t≤s` and the high-radial dissipation at s falls to `M`,

    P² ≤ A² [3 W₃(R) (C (s-t))² + H_R(U(t)-U(s))],

where `A = 3 + C_L (||U(t)||+||U(s)||)` and `C` bounds the **actual** projected-momentum physical L² source on `[t,s]`. Multiplying by `R²` and using the endpoint high-band estimate proves

    R² P² ≤ A² [3 R² W₃(R) (C(s-t))² + 2(D_{>R}(t)+D_{>R}(s))].

This eliminates the previously unpriced *temporal* high-band term and replaces it with genuine physical endpoint dissipation. A final theorem takes the contrapositive: two explicitly prescribed endpoint dissipation ceilings that make the right side too small prevent the high-radial drop. It is **not a bound on those endpoint dissipations**. Thus it does not force positive terminal persistence width, a finite terminal H³ dissipation budget, or unconditional Navier–Stokes regularity.

Lean declarations:

- `h3Critical_fourierDifference_normSq_le_twoEndpointSquares`
- `h3Critical_highTemporalMass_le_twoEndpointHighMass`
- `h3Critical_highTemporalMass_radiusSq_le_endpointDissipation`
- `h3Critical_sourceDrop_forces_endpointPhysicalDissipationBudget`
- `h3Critical_sourceDrop_endpointDissipationCeilings_preclude_drop`

Compile with pinned toolchain. Static checks are not Lean elaboration.
