# Real Schwartz realization of the full-third Hermitian axis packet

Base checkpoint: `2af70a34` (exact inverse-Fourier realization).

The 6-frequency smooth compact Schwartz Fourier packet, constructed with the
fixed-center polynomial transverse germs and complex phase product `I`, has
already been proven Hermitian and pointwise divergence-free on
`Axis Depth.three`. Its Fourier carrier has been transported without approximation
to `H3FourierPoint3` and inverted there.

This module uses the project's existing **canonical axis** theorem
`lowNormalQuarterAxisHermitianSchwartz_fourierInv_im_zero` (not the Fin-three
specialization). Therefore each inverse-Fourier component has zero imaginary
part at every physical point. Taking the real part constructs a genuine real
Schwartz three-velocity. Complexification recovers the exact complex inverse
Schwartz components; Fourier transforming recovers the original six-frequency
Hermitian spectrum on the same carrier.

The theorem `thirdFullAxisRealSchwartz_physical_divergence244` uses the existing
Schwartz physical-divergence/Fourier-multiplier theorem and Fourier inversion
to establish zero Euclidean spatial divergence at every point. This is not
only a frequency-space identity.

**Still unresolved:** identifying the full Fourier trilinear transport
coefficient of this *real velocity* with an explicit sum over all 12 coherent
momentum sectors. The negative windowed LOCAL sector established earlier
cannot establish the sign of the complete integral without support-wide
control, sign transfer and the associated integral changes of variables.
No Navier--Stokes regularity theorem follows from this patch.

## Validation

Register the module, run `python3 proof/generate_index.py` and its `--check`,
`python3 proof/check_fragment.py --all`, compile this module, compile the
first-monomial audit, run full `lake build`, and include `proof/order.txt` in
the commit. Lean/mathlib are not available in the artifact-preparation runtime;
Lean compiler verification takes place on the project machine.
