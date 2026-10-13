# Comparable-frequency sign audit

Base: fb56195a, full physical Schwartz interpolation bounded by E3 M1.

## Question

Could a further permutation of the comparable-frequency triad force its
signed contribution to vanish or have one favorable sign, using only
momentum conservation and incompressibility?

The patch defines the complete six-order coefficient: all assignments
of p,q,r to the three frequency slots, with the corresponding amplitudes.
It proves that this is exactly the sum of the three paired shell terms.
It then evaluates a concrete three-dimensional configuration.

## Exact example

    p=(1,0,0), q=(1,1,0), r=(-2,-1,0),
    a=c=(0,0,1), b=tau*i*(-1,1,0).

Momentum is zero and p·a=q·b=r·c=0. The squared radii are 1,2,5,
so all frequencies are nonzero and comparable, with radius ratio sqrt(5).
For tau=1 the six ordered contributions are

    -2i, 0, 0, 0, 0, 18i,

and their sum is 16i. The theorem proves the general value 16*tau*i.
Choosing tau=1 and tau=-1 gives imaginary parts +16 and -16.
The same sum results after reflecting every frequency and replacing
b(tau) by b(-tau), its complex conjugate. Real-field Fourier symmetry
therefore does not itself cancel this paired contribution.

## Consequence and limits

There is no universal zero or one-sided sign for this six-order symbol
under just these algebraic conditions. This rules out a favorable-sign
argument based solely on incompressibility plus triad permutation.
It does not rule out quantitative estimates, further PDE information,
geometry-dependent bounds, or cancellations between different triads.

This is a finite-dimensional symbol calculation, not a constructed
Schwartz velocity, a theorem about the sign of a full Schwartz integral,
or a counterexample to continuation. No such stronger conclusion is
claimed. The examples obey the local constraints needed for the symbol
but do not encode the full evolution assumptions.

## Next mathematical direction

The global E3 M1 estimate is established and the separated-frequency
improvements remain available. At comparable scales, an improved argument
must use more than a universal sign of this symbol. A useful next step is
to quantify the role of polarization geometry or test the energy-dissipation
scaling of a proposed stronger estimate before formalizing more wrappers.

## Checks

An independent integer calculation gave the six real coefficients
[-2,0,0,0,0,18], squared radii [1,2,5], and zero divergence contractions.
The complex phase is linear in tau. Source indexing, fragment consistency
and whitespace checks run before packaging. Lean compilation and the audit
remain pending locally. No axioms or sorry declarations are introduced.
