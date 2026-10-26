# Conditional projected-source ceiling escape on intermittent cubic clocks

Base commit: `5d79d59a` (source/cutoff amplification split).

## The algebraic mechanism

At a physical finite annulus the exact coefficient is

`Z = C*L(R,Q,K) + C^2*H(R,Q) + 1`,

where `L,H` are nonnegative when the selected starting-state ceiling `K` is
nonnegative. Suppose an actual sixth-order barrier `B R^6 <= Z` holds.
Fix a hypothetical nonnegative source ceiling `S`. If the cutoff gains
at that fixed source ceiling satisfy

`S*L(R,Q,K) + S^2*H(R,Q)+1 <= D R^6`

for some `D < B`, then `C > S`. The proof uses the previously certified
exact factorization and nonnegativity, not an assumed PDE bound.

## The physical intermittent statement

Under the earlier explicit hypotheses of no terminal strong physical L2
trace, positive terminal kinetic mass and **additional finite terminal
H3 dissipation**, choose the same type of disjoint cofinal cubic annuli.
This module retains the original quarter-cubic gap, exact persistence
width, summable costs, and the selected `K>=0`, `C>=0`.

There is also an unconditional tradeoff: for any positive sixth-order
threshold `B`, every sufficiently late noncompressed witness with `C_k<=S`
must satisfy

`B R_k^6 <= S L(R_k,Q_k,K_k) + S^2 H(R_k,Q_k) + 1`.

This does not require a cutoff bound: it shows the cutoff gain must become
super-sixth on *any* intermittent subset where the source remains bounded.

For each positive geometric threshold `eta`, nonnegative candidate source
ceiling `S`, and nonnegative sixth-scale cutoff-gain bound `D`:

If eventually

`S*L(R_k,Q_k,K_k) + S^2*H(R_k,Q_k)+1 <= D R_k^6`,

then eventually every witness with

`eta <= R_k^3*(T-tau_k)/4`

has `S < C_k`.

This is a conditional source-concentration criterion; it **does not**
assert that the displayed gain bound holds, that noncompressed times
occur, or that finite terminal H3 dissipation is automatic. In particular,
the quadratic amplifier grows quickly with the outer cutoff and may
prevent applying the criterion for fixed S.

## Validation

The patch registers the four named theorems in the root and audit imports.
Run Lean, the audit, `proof/generate_index.py`, and the full build locally.
