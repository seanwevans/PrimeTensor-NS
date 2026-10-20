# Weighted H³ canonical full-third commutator and physical bridge

**Base commit:** `487b3e83` — canonical third-gradient reference independence.

This module builds the complete signed transport observable **G₃ + 3 M** on
arbitrary native weighted H³ spectral velocity data. Both summands are
reference-independent; the multiplicity three is the previously proven
physical cyclic identity, not a choice or reindexing assumption.

* `h3MatchedSchwartzGradientCompletion_fullThird_tendsto244` proves convergence
  of the genuine complete signed third-order Schwartz transport for every
  fully decoder-/jet-matched completion.
* `fullSchwartzThirdCommutator_spectralPair_modulus244` gives a quantitative
  full two-profile bound, retaining all 972 gradient terms and 243 signed
  interpolation terms, and the exact physical factor `3 * 2 = 6`.
* `exists_physicalSnapshot_matchedFullThirdAndFirstJet244` constructs a single
  approximating family whose full signed transport approaches the canonical
  spectral full-third value and whose literal first derivatives converge to
  the actual logged physical velocity gradients at every Euclidean point.
* The final physical discrepancy identity, and its absolute-value bound,
  express the remaining PDE identification as **two explicit mismatches**:
  canonical gradient vs. actual third-order gradient, and canonical signed
  interpolation vs. actual physical 3–2–2 term. Neither equality is assumed.

This does NOT yet prove that those physical mismatches vanish, nor construct
fourth-order dissipation convergence from H³ density. In particular it does not
claim Navier–Stokes global regularity.
