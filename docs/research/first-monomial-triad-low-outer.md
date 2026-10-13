# Linear separation gains for the outer triad frequencies

Base: 93f62723, quadratic separation gain for low-middle triads.

Write q=-(p+r), P=|p|, R=|r|, Q=|q| and A(p)=|U(p)|_2. The existing
shell estimate gives 2P²R²Q³ A(p)A(r)A(q). On P<=eps R, eps>=0,

    P²R²Q³ <= eps P R³Q³.

Thus the small p factor carries one derivative and the other two factors
carry three derivatives each. The measure-preserving substitution

    (x,y) -> (p,r)=(-(x+y),x)

makes q=y and places p in the L1 factor. The existing L2-L2-L1 inequality
then proves

    |integral S_low_left| <= 2 eps E3 M1,
    E3 = integral |p|⁶ A(p)²,
    M1 = integral |q| A(q).

The paired shell kernel is invariant under exchanging p and r. Its
restriction to R<=eps P therefore satisfies the same integral bound.
All weighted moment hypotheses are derived from the Schwartz data.
The statement allows eps=0 without division; eps<1 is the regime in
which these are separation gains.

## Reuse and scope

The previous middle-frequency measurable equivalence and its measure
preservation theorem are made public so the cyclic substitution can reuse
them. Their definitions and proofs are unchanged.

The patch estimates the low-left and low-right restrictions individually.
It does not sum overlapping indicators or assert a partition identity.
The middle-frequency bound from the previous module is quadratic in eps;
the outer-frequency bounds here are linear in eps.

After excluding all three low-frequency regions at a fixed positive eps,
all three radii are comparable up to constants depending on eps. The next
mathematical task is to assemble the regions and assess that comparable
contribution. The separated estimates alone do not establish absorption
against viscous dissipation or continuation.

## Checks

Source index, fragment consistency and whitespace checks run before packaging.
Lean compilation and the theorem audit remain pending on the pinned local
toolchain. No axioms or sorry declarations are introduced.
