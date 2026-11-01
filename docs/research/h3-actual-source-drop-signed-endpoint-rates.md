# Source-drop physical signed H³ endpoint-rate obstruction

Base `becf6bd6` (exact spectral-temporal cost charged to physical endpoint H³ dissipation).

## Exact signed PDE transfer

The committed source-drop theorem works on arbitrary two strict physical times
`t ≤ s` in the same H³ energy class. Let `P` be the actual coordinate highpass
projected-momentum source excess above the kinetic barrier, `A` its exact
established spectral-state source Lipschitz coefficient, `C` a **local**
physical projected-momentum source ceiling on `[t,s]`, and `R ≥ 0` the
independent temporal spectral cutoff. If high-H³ dissipation at `s` has
fallen below the chosen threshold M, it already proves

    R² P² ≤ A² [ 3 R² W₃(R) C²(s-t)² + 2(D_{>R}(t)+D_{>R}(s)) ].

The actual physical Fourier H³ partition bounds `D_{>R}(r) ≤ D(r)` at
strict energy-class times. The exact NS energy identity, already proved in
`H3/Energy/Balance/Exact.lean`, is

    E'(r) + 2 D(r) = - Transport(r).

Hence, with no additional assumptions about endpoint dissipation,

    R² P² ≤ A² [3 R² W₃(R) C²(s-t)²
                    - E'(t) - Transport(t) - E'(s) - Transport(s)].

This is an exact *necessary* source-collapse condition. The right-hand side
contains the actual signed H³ energy and nonlinear transport derivatives at
the same physical times; it does not assume a terminal bound for either.

## Pointwise signed bottleneck

For any real threshold K, if

    A² [3 R² W₃(R) C²(s-t)² + 2K] < R² P²,

then the same source-driven dissipation drop forces at least one endpoint
signed rate above K:

    K < -E'(t)-Transport(t)   OR   K < -E'(s)-Transport(s).

Consequently, at t or s, either the physical energy derivative is less than
`-K/2`, or the nonlinear transport derivative is less than `-K/2`.
This is an actual physical signed-rate alternative, not an assumed uniform
bound, not a proof that the source peak or rate K has prescribed terminal
scaling, and not an unconditional H³ regularity theorem.

Declarations:

- `h3Critical_sourceDrop_forces_signedEndpointRateBudget`
- `h3Critical_sourceDrop_forces_oneLargeSignedEndpointRate`
- `h3Critical_largeSignedViscousRate_energyDrain_or_transport`
- `h3Critical_sourceDrop_forces_endpointEnergyDrain_or_transport`

The new bridge introduces no axioms, admits, or sorry placeholders. Static
checks are not Lean elaboration. Verify in the pinned local Lean toolchain.
