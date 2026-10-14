# Twelve coherent resonant sectors: permutation and reflection audit

Checkpoint: `37889bc3`.

The six-order first-monomial coefficient is symmetric under permutations of the three paired frequency/polarization inputs. On the momentum plane `q = -(p+r)`, two generators suffice: swap `(p,r) -> (r,p)` and cycle `(p,r) -> (q,p)`. Both preserve the signed kernel `F(p,r) = Re (I C6(p,q,r,U(p),U(q),U(r)))` for the actual fixed quarter-scale Hermitian Schwartz field.

Consequently, the six positive ordered pairs `(P,R)`, `(R,P)`, `(Q,R)`, `(R,Q)`, `(Q,P)`, `(P,Q)` all have value `9/64`, and reflection creates six further center pairs with exactly the same value. The general positive-local-ball lemma proves that *each indexed sector* has a positive-radius compact ball with a strictly positive integral of `F`.

**Open hard-math frontier:** These compact positive balls do not cover the entire six-packet support. Therefore summing their integrals cannot establish a nonzero full-space integral without controlling the sign and size of the complement within all twelve coherent resonant sectors. A promising next step is a quantitative uniform-neighborhood estimate in terms of the packet localization radius, or a controlled shrinking family of cutoffs followed by dominated convergence / rescaling.

No singularity exclusion or global Navier–Stokes result follows from this statement alone.
