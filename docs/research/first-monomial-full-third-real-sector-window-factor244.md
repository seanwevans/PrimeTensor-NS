# Full third real H3 physical kernel: common Fourier-window extraction

**Parent checkpoint:** `dbac456a` — complete real physical five-index sector polynomial.

This module separates the real cutoffs from the frequency-dependent exactly solenoidal transverse germs without dropping or replacing any of the physical seven-derivative contractions.  It proves the algebraic identity for **all** Fourier momentum pairs, not merely on a coherent sector:

`PhysicalPolynomial(ρ,n,z) = WindowProduct(ρ,n,z) * PhysicalCore(n,z)`.

Here `WindowProduct` is the product of the three distinct real `ContDiffBump` windows evaluated at the actual frequencies `p`, `q = -p-r`, and `r`.  The `PhysicalCore` is the complete five-index `3+3+1` gradient polynomial with factor **2**, plus the genuine `3+2+2` interpolation contraction with factor **6**, evaluated at the variable-frequency transverse-germ polarizations without scalar cutoff amplitudes.

The final theorem transports this exact factorization to the actual imaginary part of the physical Fourier kernel at points of the six positive coherent sectors where the recovered Schwartz triple mass is nonzero.  For zero triple mass and for the signed integral, separate analytical steps remain.

## Next mathematical obligations

1. Prove the complete real `PhysicalCore` equals the previously derived projected six-order sharp symbol at the six exact center pairs, with all normalization and derivative orders checked.
2. Prove a **uniform negative** bound for `PhysicalCore` in suitably narrow positive-sector neighborhoods, or determine whether that sign is false.
3. Establish the product window's sign and nontrivial positive-measure support, handle zero-triple-mass points, and integrate with the already-proved Hermitian reflection and six-sector decomposition.

No sign result, global noncancellation, or Navier–Stokes regularity is claimed by this patch.
