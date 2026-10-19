# Actual full-third zero-spectral-mass branch and six-sector formula

Base: `a726557e` (`identify transported full third physical sectors with projected Hermitian orbit`).

The previous bridge proved an unconditional equality of *six physical
polynomials* with one projected Hermitian orbit. The actual Fourier kernel
was identified with those polynomials only at points of nonzero triple
spectral mass on each positive coherent sector.

This module proves, using the existing exact recovered Fourier-spectrum
factorization for each 3+3+1 gradient slot, that when the triple spectral
mass vanishes, EVERY physical gradient slot vanishes. The fivefold axis sums
are preserved. Combined with the previously proved 3+2+2 interpolation
zero-mass theorem, the complete complex unphased kernel then vanishes.
Consequently its imaginary part vanishes at every such point.

The exact sector formula has two cases, with no inverse or nonzero mass
hypothesis in its statement:

```
actualImag(z) =
  if spectralTripleMass(z) != 0
  then actualThreeWindow(n,z) * actualPhysicalCore(n,z)
  else 0
```

This is proved at **every point of each actual positive coherent sector**
under the previously established width and sector-disjointness hypotheses.
The six true sector integrals, and hence the actual real Schwartz H3 full
commutator, are rewritten exactly as six integrals of the mass-gated
coefficients. The physical factors `2` and `(2*pi)^7` are retained.

## Remaining hard-math step

The mass-gated expressions are not yet the *ungated* physical polynomials
appearing in the recent common-window/Hermitian orbit theorem. Show the
windowed core vanishes on the mass-zero locus, including zero transverse
germs (not just zero cutoffs). Then transport the indicators of the actual
positive sector sets and use the strict local Hermitian tube and positivity
of the original smooth windows to deduce genuine signed noncancellation.
After nonvanishing is established, the existing oddness and fixed-kinetic
concentration theorems close the static obstruction, not global regularity.
