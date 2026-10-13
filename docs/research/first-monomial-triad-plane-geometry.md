# Polarization geometry after the sign audit

Base: 24e20e71, both signs of the complete six-order coefficient.

## Exact identity

Choose frequencies p=(x,y,0), q=(z,w,0), r=-p-q. Let J(vx,vy,0)=(-vy,vx,0)
and n=(0,0,1). Parameterize the complex polarizations by

    a=alpha Jp+A n, b=beta Jq+B n, c=gamma Jr+C n.

Each polarization is incompressible at its own frequency. The basis Jp
is not normalized: alpha is a coefficient, not the magnitude of a's planar
component. Let Delta=xw-yz and P²=p·p, Q²=q·q, R²=r·r.
The complete six-order coefficient is exactly

    Delta [ alpha B C (q·r) P² (R²-Q²)
          - beta  A C (p·r) Q² (R²-P²)
          + gamma A B (p·q) R² (Q²-P²) ].

Products of polarizations are complex bilinear products, as in the original
triad kernel; no Hermitian conjugation is inserted.

The fully planar alpha beta gamma contribution cancels across the six
orderings. The surviving terms have one planar coefficient and two normal
amplitudes. They also retain the outer shell differences and oriented area.

## Formal consequences

The patch proves:

- momentum conservation and incompressibility for the parameterization;
- the exact six-order formula above;
- zero for fully planar polarizations;
- zero for purely normal polarizations;
- zero if all pairwise normal-amplitude products vanish;
- zero when the oriented frequency area vanishes.

The preceding sign example is alpha=gamma=0, A=C=1, beta=i, B=0,
with p=(1,0,0), q=(1,1,0). The middle term is 16i, consistent with the
sign audit. Thus the new cancellation and the earlier nonzero example
fit the same identity.

## Scope and next question

This is presently a coordinate-plane identity for finite-dimensional
polarizations. The patch does not yet supply an orthogonal-coordinate
transport theorem, a measurable choice of triad frame, or an integral
bound using normal components. It is not a statement that a nontrivial
three-dimensional Schwartz field has spectrum confined to a plane.

The polynomial contains an area factor, but a quantitative angular gain
must account for the unnormalized planar basis and the sizes of alpha,
beta,gamma. No new dimensionless angular estimate is claimed here.
The next useful step is an invariant formulation or a bound that retains
these normal-polarization products through the frequency integral.

## Checks

An independent sparse-polynomial expansion over ten indeterminates checked
the identity exactly: both sides have the same 96 nonzero monomials after
cancellation. Source indexing, fragment consistency and whitespace checks
run before packaging. Lean compilation and the audit remain pending on
the pinned local toolchain. No axioms or sorry declarations are introduced.
