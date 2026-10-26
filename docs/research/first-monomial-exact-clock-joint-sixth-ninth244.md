# Joint intermittent sixth/ninth PDE concentration

Base commit: `8a0d526b`.

## Input

The existing quadratically sharp clock retains the actual physical annular
variation `Lambda*delta + Xi*delta^2` and gives, for every epsilon > 0,
eventually a cubic geometric compression cap or one of two rate caps:

`R^3*(T-tau)/4 <= epsilon`, or
`R^6 <= 16*epsilon*(Lambda+1)`, or
`R^9 <= 16*epsilon^2*(Xi+1)`.

Under the explicit assumptions of positive terminal kinetic energy, no
strong terminal physical L2 trace, and *additional* finite terminal full
H3 dissipation, the same selected cofinal annuli retain the quarter-cubic
gap and have disjoint positive windows of summable cost.

## Joint result

For any positive geometric floor `eta` and nonnegative candidate sixth and
ninth rate ceilings `B,D`, every sufficiently late selected witness with
`eta <= R^3*(T-tau)/4` satisfies

`B*R^6 < Lambda+1 OR D*R^9 < Xi+1`.

The proof chooses a single epsilon small relative to `eta`, `B+1`, and
`D+1`. Thus the linear and quadratic rates cannot both remain at their
candidate scales on late noncompressed witnesses. No branch is selected
globally.

The quadratic coefficient has the exact factorization
`Xi(R,Q,C) = C^2*H(R,Q)` with a nonnegative explicit cutoff gain H.
Consequently, at a late noncompressed witness where `Lambda+1 <= B*R^6`
and `C^2<=S^2`, the cutoff gain satisfies
`D*R^9 < S^2*H(R,Q)+1`.

These are conditional necessary concentration statements. Neither finite
terminal H3 dissipation, an uncompressed terminal lag, nor bounded physical
source/cutoff gains is proved from initial path admissibility.

## Validation

The ZIP contains only source, an idempotent registrar, and these notes.
Lean compilation has not been run in the packaging environment. Run the
single module, index, audit, full build, and staged whitespace checks.
