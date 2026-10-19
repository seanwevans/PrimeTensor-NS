# Actual full-third Fourier density: removal of the spectral-mass gate

Base checkpoint: `d7b9f7de` — close actual full third Schwartz zero mass branch and six sector formula.

The previous result identified the TRUE unphased Fourier density with a physical
seven-derivative polynomial on every positive coherent sector if triple spectral
mass is nonzero, and with zero if that mass vanishes. The physical polynomial
was therefore guarded by an `if` testing this mass.

This patch removes the guard without falsely assuming Fourier nondegeneracy.

1. The already proved five-index physical contraction identifies every
   cutoff-free sector core with twice its corrected ordered real symbol.
   The symbol is trilinear in the three actual moving transverse germs; it
   vanishes if any of those three germ vectors is zero.
2. If the scalar product of three real Schwartz cutoff values is zero, the
   windowed physical polynomial is zero by exact cutoff factorization.
3. If all three cutoff values are nonzero, their frequencies lie in their
   own isolated primary spectral neighborhoods. Each recovered Fourier vector
   is then its own complex cutoff multiplied by its nonzero phase and actual
   real transverse germ. If triple spectral mass is zero, a vector vanishes,
   hence the corresponding real transverse germ vanishes. Therefore the
   entire physical polynomial vanishes. This includes degeneration of the
   true transverse Leray polynomial even if all cutoffs are positive.
4. Consequently the guarded polynomial equals the original physical
   polynomial pointwise at ALL Fourier frequencies, and the TRUE unphased
   imaginary kernel equals that polynomial on each real positive sector.
5. The actual real solenoidal Schwartz full H3 commutator equals the six
   physical-polynomial integrals over their correct measurable, supported
   coherent sectors, including the already established factor `2*(2*pi)^7`.

This does NOT yet replace the six sector integrals with six unrestricted
polynomial integrals, nor show the actual Fourier window product is positive
on a non-null region of the negative Hermitian tube. Those are the next
mathematical obligations before declaring the static noncancellation closed.

No external axiom, PDE continuation claim, division by spectral mass, or
nonzero Fourier-amplitude hypothesis is added.
