# Common three-window product under six physical Fourier permutations

Base `494e838e` (“transport actual full third six Schwartz sectors by measure preserving permutations”).

The six coherent positive orientations are `(p,r)`, `(r,p)`, `(q,r)`, `(r,q)`, `(q,p)`, `(p,q)`, with `q = -p-r`. Previously proved Hilbert-pair measurable equivalences preserve product Fourier volume; this step identifies their action on **the actual three real Schwartz bump factors** `thirdFullPositiveSectorWindowProduct244` rather than an auxiliary symbolic cutoff.

The main pointwise target is, for all `n : Fin 6` and every Fourier pair `z`:

`thirdFullPositiveSectorWindowProduct244 ρ hρ n (thirdFullPositivePairPermutationEquiv244 n z) = thirdFullPositiveCommonThreeWindow244 ρ hρ z`.

The common product is the original `n = 0` Fourier Schwartz scalar; neither support assumptions nor nonzero triple mass are needed for this purely algebraic identity. The separate physical coefficient may have either sign.

An integral theorem combines six such weighted coefficients as one integral of the common product times their transported sum, using the preceding measure-preserving six-integral theorem.

**Outstanding:** Identify the transported actual physical-core coefficients with the moving-germ projected Hermitian six-orbit *on all relevant frequencies*, handle spectral triple-mass zero points, and establish positivity of the common window on a nonempty set. The previously proved strict negativity applies only to the properly symmetrized coefficient on a sufficiently small common neighborhood; it does not imply each positive orientation is negative. No signed integral theorem or Navier–Stokes continuation theorem is claimed here.
