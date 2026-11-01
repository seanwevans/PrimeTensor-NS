# Cofinal actual source peaks: intrinsic H³ energy slope / physical gradient gate

Base `370c03d3`. The prior pointwise gradient-or-drain theorem required an explicit
*common* H³ energy ceiling `Emax` and a compatibility condition
`4422(1+H) Emax <= K/2`. The new theorem prices the actual endpoint energies
separately, removing both artificial prerequisites.

## Actual physical PDE inequality

Let `P = ||HighpassSource(t)|| - B_sigma(M) >= 0`,
`A = 3 + C_L (||U(t)|| + ||U(s)||)` and `L = 3 R² W₃(R) (C(s-t))²`.
From the already formalized source-drop endpoint signed-rate budget:

    R² P² <= A² [L - E'(t) - Tr(t) - E'(s) - Tr(s)].

If the actual physical first spatial velocity derivatives are bounded by
`Ht` at t and `Hs` at s, the proven one-time Landau commutator gives

    -Tr(t) <= 4422 (1+|Ht|) E(t),
    -Tr(s) <= 4422 (1+|Hs|) E(s).

Therefore, WITHOUT a terminal-uniform H³ energy ceiling,

    R² P² <= A² [L - E'(t) - E'(s)
                    + 4422(1+|Ht|)E(t) + 4422(1+|Hs|)E(s)].

If the source excess exceeds the RHS computed with `-E'(t)-E'(s)` replaced
by `2K`, at least one endpoint has `E' < -K`, or a *real spatial derivative*
exceeds its corresponding gradient cap. Separate endpoint caps are permitted.

## Synchronizing the real cofinal source witnesses

The imported source-driven disjoint-window theorem proves one fixed Fourier
coordinate, times `t(v k) -> T`, separated positive windows, and arbitrary
square-source-mass floors. Choose the source floor to be
`Ksource(n) = B_sigma(n)(M(n))²`, exactly the squared kinetic barrier.
Plancherel yields an ACTUAL strict source-peak inequality at every selected
start time. This closes a formerly repeated premise `hPeak` on the moving
cofinal diagonal. Every window retains `D_{>sigma(n)} > M(n)` throughout.

For any later physical time after a selected window at which this dissipation
actually drops to `<= M(n)`, the intrinsic physical gradient-or-drain gate
applies at that same selected source-peak time and the later time. Its local
source ceiling, strict numerical gap, drop, and absence of rapid energy
drain are all explicitly provided premises, NOT consequences of cofinality.

This is a conditional post-window obstruction, not a proof that any drop
occurs, that the gap is forced, or that the branches yield a contradiction.
The source cutoff, dissipation cutoff and temporal velocity cutoff remain
independent. No global Navier-Stokes regularity is claimed.

Declarations:
- `h3Critical_sourceDrop_gradientCaps_signedEnergySlopeBudget`
- `h3Critical_sourceDrop_gradientCaps_force_endpointEnergyDrain`
- `h3Critical_sourceDrop_noDrain_forces_actualEndpointGradient`
- `h3Critical_noL2Trace_cofinalSourceWindows_postDropGradientGate`

Compile with the pinned Lean/Mathlib toolchain. Static validation is not proof certification.
