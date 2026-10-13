# Six-center nonresonance for the sharp low-normal triad

Base checkpoint: `a4498cce` (measure-preserving cyclic first-monomial integral identity).

The sharp pointwise family and its Fourier reality partners use

    p=(1,0,0), q=(t,t,0), r=(-1-t,-t,0), -p, -q, -r.

For nonzero `t`, embed the integer plane into physical frequency space by

    L_t(a,b)=(a+t*b,t*b,0).

This is injective: its second coordinate gives `b`, then the first gives `a`.
The six centers are the image of the six *fixed* lattice vectors

    (1,0), (0,1), (-1,-1), (-1,0), (0,-1), (1,1).

A kernel-checked finite classification identifies every ordered triple of
center labels whose momentum sum is zero. Exactly 12 of 216 triples qualify:
all six permutations of (p,q,r), and all six permutations of (-p,-q,-r).
All 204 other ordered label triples have nonzero momentum sum. The proof
transfers the lattice classification to the exact family for **every t != 0**,
not only a small-t asymptotic regime.

This removes a concrete combinatorial obstruction to localizing Fourier
amplitudes near the sharp family: any unwanted center triple has positive
momentum defect; because there are finitely many such triples, one can choose
small enough support balls to exclude every spurious interaction. The
positive common radius and bump-field construction remain to be formalized.

The next hard steps are (a) construct a smooth compactly supported Fourier
polarization satisfying divergence and U(-xi)=conj(U(xi)); (b) identify
its prescribed values or near-values on the six centers; (c) control the
integrated six-order kernel on the resulting neighborhoods. The finite
nonresonance theorem alone does not assert an integrated sign or any
Navier--Stokes regularity claim.
