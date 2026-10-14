# Quarter-scale inverse Fourier: Hermitian-to-real Schwartz reconstruction

Base checkpoint: `d730883c` — construct inverse Fourier Schwartz field and transfer cyclic shell sign.

## Proof target

The existing explicit even-windowed Fourier field `Uρ` is smooth,
compactly supported, Hermitian (`Uρ(-ξ)=conj(Uρ(ξ))`) and divergence-free.
The previous checkpoint constructed the inverse-Fourier component on the
Euclidean Hilbert carrier and verified its Fourier transform equals `Uρ`.

The new generic lemma proves the Hermitian-to-real converse for **every**
complex Schwartz spectrum on `EuclideanSpace ℝ (Fin 3)`. In the inverse
Fourier integral, replace `ξ` by `-ξ`. The Euclidean volume is preserved;
complex conjugation of the Fourier character flips the sign of the
frequency; and conjugation of the Hermitian amplitude restores it. Hence
`star (𝓕⁻ F x) = 𝓕⁻ F x` at every spatial point.

Taking the real part through `Complex.reCLM` constructs a genuine
`𝓢(EuclideanSpace ℝ (Fin 3), ℝ)` for each velocity component. The proof
then identifies its complexification with the original inverse-Fourier
Schwartz function and verifies Fourier recovery of all three components.

## Explicit limitations

The real spatial Schwartz velocity is now constructed on the `Fin 3`
Euclidean carrier, but this does **not** yet assert equality with any logged
Navier–Stokes path snapshot, nor the canonical physical `Point3` first-monomial
aggregate. That requires an exact carrier/index transport from `Fin 3` to
`Axis Depth.three`, preservation of product volume, and application of the
existing real-Schwartz physical aggregate/cyclic-shell identities. The
positive six-order Fourier integral and negative physically phased integral
remain established separately in preceding modules.

The resulting noncancellation does not alone prove global regularity or
blowup of Navier–Stokes.
