# Complete full-third REAL Schwartz static commutator: coherent-tube Fourier identity

**Base checkpoint:** `e9b20f5d` — identify full third physical gradient Fourier slots on coherent tube.

## Mathematical content

This patch combines the physical Fourier slot proved at `e9b20f5d` with the genuine interpolation kernel of the same real Schwartz velocity. The complete `3+3+1` gradient contribution has four ordered derivative patterns, each carrying the pairing factor `2`, and five nested sums over the three positive-depth physical coordinate axes. Every one of those 3+3+1 integrands is already proved absolutely integrable and vanishes outside the twelve-center coherent tube.

The other physical term, the `3+2+2` first monomial, is the preexisting `h3SchwartzTriadKernel` on the Euclidean Fourier carrier. Unfolding its exact amplitude kernel shows that if any of the three frequency-space velocity amplitudes vanishes, the integrand is zero. The recently established triple spectral mass/support lemma therefore applies directly: there is no need to postulate an abstract equivalence to a cubic multiplier or impose an independent support hypothesis.

Both channels are localized to **the same** Euclidean-pair preimage of the intrinsic `Axis Depth.three` coherent thickening, with no unproved measure-preservation claim or normalization factor. The complex coefficient still has the original factor `6` in front of the `3+2+2` Fourier integral, representing interpolation multiplicity `3` times pairing factor `2`, and the gradient channels still have the original factor `2`. All channels retain the seventh Fourier phase `(2 π I)^7`.

The main theorem `thirdFullAxisRealThirdCommutator_eq_tube244` identifies the full physical real static `H³` third commutator for the *constructed real solenoidal Schwartz field* with the real part of this complete, tube-localized coefficient.

The additional theorem `thirdFullAxisRealThirdCommutator_exists_tube244` chooses a sufficiently narrow width **uniformly for all polarization parameters**, for any specified positive tube radius.

## Remaining hard mathematics

The theorem is an **exact identity**, not an evaluation. It makes no sign assertion about the complete twelve-sector integral: the twelve phases, oriented permutations, and the two physical channel aggregates still have to be combined and compared. The earlier local `-192` polynomial orbit by itself does not establish noncancellation for this actual field. No Navier–Stokes continuation or Millennium result is claimed.

## Validation

Lean source and audit files are included, with no `sorry`, `admit`, `axiom`, or new opaque premise. Run `lake env lean` for the module, the theorem/axiom audit, then `lake build` and the existing source-index checks on Rocky Linux. The assistant environment did not have a Lean toolchain, so no Lean compilation is claimed here.
