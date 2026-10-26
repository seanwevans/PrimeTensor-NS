# Ninth-order quadratic PDE concentration forces ninth-eighth outer-cutoff escape

Base commit: `08c77aad` (quadratic PDE gain bounded by eighth powers of the selected radii).

## Input

The physical quadratic-sharp disjoint cubic clocks obey an intermittent barrier.
For every positive geometric threshold `eta`, and nonnegative linear and
quadratic thresholds `B,D`, every sufficiently late witness satisfies:

- if `eta <= R_k^3*(T-tau_k)/4`,
- and `Lambda_k + 1 <= B*R_k^6`,
- and `C_k^2 <= S^2`,

then

`D*R_k^9 < 36*S^2*((Q_k+1)^8+(R_k+1)^8)+1`,

where `R_k=(v k)+1`, `Q_k=N(v k)+1` are the *actual* inner and outer radii.
This is supplied by the prior physical eighth-cutoff theorem. Finite full
terminal H3 dissipation is an explicit additional assumption.

## New calculation

For `R>=1`, `(R+1)^8 <=256 R^8 <=256 R^9` and `1<=R^9`.
If the chosen outer radius were constrained by `(Q+1)^8<=M R^9`,
then the right-hand side would be at most

`(36*S^2*(M+256)+1)*R^9`.

Choose the freely available ninth-order threshold
`D=36*S^2*(M+256)+2`. This contradicts the strict spike. Therefore,
for every chosen `M>=0`, eventually each witness satisfying those three
branch tests has

`M*R_k^9 < (Q_k+1)^8`.

In particular, if noncompression, a sixth-order linear-rate bound, and a
bounded squared source ceiling all hold eventually, then

`(Q_k+1)^8/R_k^9 -> +infinity`.

This quantitatively forces faster-than-`R^(9/8)` outer-cutoff growth on that
specific branch, not on all physical paths unconditionally. No bound on
outer radius, exclusion of terminal geometric compression, or resolution of
Navier-Stokes regularity is claimed.

## Validation

The archive contains a Lean source file, registrar, and these notes.
Run `lake env lean` on the module, its `lake build`, audit checks,
`proof/generate_index.py --check`, and the full project build before commit.
