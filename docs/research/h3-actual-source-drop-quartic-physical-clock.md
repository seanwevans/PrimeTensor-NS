# Actual physical PDE quartic H³ temporal clock

Base `d45fd2f3`: source-driven cofinal physical gradient / signed-energy gate.

## New analytic consequence of the real PDE

For two strict physical times `t <= s`, let `U(t)` and `U(s)` be the genuine
three-component weighted H³ Fourier velocity states and let `C` bound the
actual physical projected momentum source on the full interval `[t,s]`.
For a spectral cutoff `R >= 1`, the already-proved Fourier split gives

    ||U(t)-U(s)||² <= LowTemporalMass_R + HighTemporalMass_R.

The actual physical momentum FTC and radial Plancherel give

    LowTemporalMass_R <= 3 W₃(R) [C(s-t)]²,
    W₃(R) = 1 + R² + R⁴ + R⁶.

Actual viscous H³ dissipation coercivity at both genuine endpoints gives

    R² HighTemporalMass_R <= 2 [D_{>R}(t) + D_{>R}(s)].

Now suppose the *quartic spectral clock* condition

    R^4 (s-t) <= 1

holds. Since `R >= 1`, `W₃(R) <= 4 R⁶`, hence

    R² * 3 W₃(R) [C(s-t)]² <= 12 C².

It follows with no assumed temporal H³ derivative that

    R² ||U(t)-U(s)||² <= 12 C² + 2[D_{>R}(t)+D_{>R}(s)].

This is a genuine PDE-derived full-H³ spectral temporal displacement estimate,
not a full-H³ Lipschitz theorem. The right side has actual physical endpoint
H³ dissipation, which may become arbitrarily large toward T.

## Source and source-drop consequences

The previously proved projected-source Lipschitz coefficient

    A = 3+C_L (||U(t)||+||U(s)||)

gives for the actual Fourier highpass source `H_{rho,i}`:

    R² ||H_{rho,i}(t)-H_{rho,i}(s)||²
       <= A² (12 C² + 2[D_{>R}(t)+D_{>R}(s)]).

If the actual high-radial H³ dissipation at s has fallen below threshold M,
and the source at t exceeds its kinetic barrier `B_{sigma,M}`, set

    P = ||H_{rho,i}(t)|| - B_{sigma,M} >= 0.

Then the same quartic physical PDE budget yields

    R² P² <= A² (12 C² + 2[D_{>R}(t)+D_{>R}(s)]).

The source-driven cofinal peak theorem from `d45fd2f3` supplies real peak
times, but does **not** force a later dissipation drop within a quartic
clock, or a numerical gap relative to actual source ceiling C and endpoint
dissipations. The new result isolates the precise scale-normalized cost;
it neither assumes nor establishes terminal-uniform bounds.

Lean declarations:

- `h3Critical_quarticClock_radialWeight_le_fourSixth`
- `h3Critical_quarticClock_scaledFiniteBandCost_le_twelve`
- `h3Critical_quarticClock_actualSpectralDisplacement_le_physical`
- `h3Critical_quarticClock_highpassSourceTemporalDisplacement_le_physical`
- `h3Critical_sourceDrop_quarticClock_endpointDissipationBudget`

Static inspection and audit registration are not Lean elaboration. Validate
using the repository's pinned Lean and Mathlib toolchain.
