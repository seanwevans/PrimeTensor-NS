# Scalar Gram angular action and the physical terminal Hilbert trace

Checkpoint baseline: `945daf6b`, `identify scalar physical Gram terminal action and trace criterion`.

## Geometric equation

Write `U` for the actual physical `L²` Hilbert velocity, `R = U'`,
`E = ||U||²`, `D = -<U,R>`, and `Delta = E ||R||² - D²`. When `E>0`, the
normalized unit velocity `N = U / sqrt(E)` satisfies

    ||N'|| = sqrt(Delta) / E.

For strict preterminal times `s <= t`, the Bochner FTC implies

    ||N(t) - N(s)|| <= ∫_s^t sqrt(Delta(r)) / E(r) dr.

The scalar angular-action condition requires this nonnegative integral to
vanish uniformly on increasingly terminal subintervals. It is an explicitly
additional hypothesis, not a consequence of kinetic dissipation alone.

## New conditional endpoint theorem

If the canonical kinetic limit `L>0` and the angular action vanishes on
all terminal tails, `N` becomes Cauchy in the physical Hilbert space and
converges to a genuine unit vector `N_T`. Since `sqrt(E) -> sqrt(L)`,
`U` converges strongly to `U_T=sqrt(L) N_T`, with `||U_T||²=L`.

This condition measures **total path length** rather than **net angular
motion**. A convergent curve can have infinite total length, so the criterion
is sufficient but not generally necessary for strong convergence. Neither
H³ control nor regular continuation follows without further estimates.

## Next analysis

Compare the scalar angular Gram action to the signed physical H³ transport,
particularly whether the spectral cascade produces a lower bound on angular
motion or can remain tangent to essentially fixed physical L² directions.
