# Actual source peak forces a positive local high-H³ dissipation persistence width

Base `7eb4319b` (actual quartic physical PDE clock).

## Previously missing numerical gap is automatic locally

Let `t` be a strict genuine Navier–Stokes H³ energy-class time with a
**strict** highpass projected source norm above the kinetic anchored barrier:

    P = ||H_{rho,i}(t)|| - B_{sigma,M} > 0.

Fix an arbitrary strict interval `[t,t+delta0]`, `delta0>0`, `t+delta0<T`,
on which the actual projected momentum source has norm at most C and the
actual weighted H³ spectral velocity has norm at most E. Both are *local*
strict-time quantities; the theorem does not assert a terminal-uniform bound.
Let

    A = 3 + C_L (||U(t)||+E),
    D = velocityH3DissipationAt(u,t),
    B = 12 C^2 + 2(D+M),
    Q = max(1,sigma).

Assume `sigma>=0`, `M>=0`, and define explicitly

    R = Q + 1 + (A^2 B)/P^2,
    delta = min(delta0, 1/R^4).

Then `R>=1`, `R>=sigma`, `delta>0`, `R^4 delta<=1`, and the **automatic strict gap**

    A^2 B < R^2 P^2

holds by scalar algebra. There is NO new `hGap` hypothesis.

The actual quartic PDE source-drop estimate and the **already proved radial
antitonicity** of actual high-H³ dissipation give, if any `s∈[t,t+delta]`
were to satisfy `D_{>sigma}(s)<=M`,

    R^2 P^2 <= A_s^2 (12 C^2 + 2[D_{>R}(t)+D_{>R}(s)])
              <= A^2(12 C^2 + 2[D(t)+M]) = A^2 B.

This contradicts the automatic gap. Therefore the genuine physical
high-radial H³ dissipation cannot fall to or below M on the entire nonzero
physical interval:

    for all s∈[t,t+delta], D_{>sigma}(s)>M.

It does **not** require any H³ spectral temporal Lipschitz assumption,
continuity of full H³ dissipation, terminal-uniform source ceiling, or
terminal-uniform persistence width. The radius and width degenerate if P
shrinks or the local endpoint physical costs grow. The result is a finite-time
rigidity theorem, not a global Navier–Stokes continuation proof.

## Lean declarations

- `h3Critical_positiveSourceMargin_selectsDominantQuarticRadius`
- `h3Critical_quarticSourceDrop_initialTailDissipationBudget`
- `h3Critical_strictSourcePeak_automaticLocalHighDissipationPersistence`

The ZIP carries source, idempotent registrar and notes. Lean compilation and
baseline audits must be run in the repository's pinned environment.

## Lean elaboration correction (fix1 at `7eb4319b`)

The compiler found a sum-orientation mismatch in
`h3Critical_quarticSourceDrop_initialTailDissipationBudget`.
`add_le_add_right hLater D_t` produces `D_t+D_s ≤ D_t+M`, preserving the
original endpoint order, and `add_le_add_right hDouble (12*C²)` produces
`12*C²+2*(D_t+D_s) ≤ 12*C²+2*(D_t+M)`. Previously both steps used
`add_le_add_left`, yielding reordered sums which did not elaborate
by definitional equality. The unused `ring` tactic after `field_simp`
was also removed. No theorem statements or mathematical assumptions changed.
The pinned Lean toolchain must verify the correction.
