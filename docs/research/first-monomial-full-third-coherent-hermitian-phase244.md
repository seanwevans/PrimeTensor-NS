# Full-third coherent Hermitian phase: permutation and conjugate reflection

Base checkpoint: `4242d6b4` — exclusion of noncoherent full-third axis-window interactions.

This module begins the coherent-sector proof after the quantitative support
exclusion. The corrected complete six-permutation seven-derivative Fourier
symbol is invariant under paired transpositions of (momentum, polarization).
Those permutations continue to preserve the exact projected Hermitian
momentum coefficient when *each* moving transverse polarization is carried
with its own frequency and projection center.

The polynomial transverse lift
`P_ξ(a) = |ξ|² a - (ξ·a) ξ` is even in frequency; its normalized fixed-center
germ consequently obeys `G_{-η}(-ξ,a)=G_η(ξ,a)` without a singular denominator.
By contrast the corrected real seven-derivative Fourier symbol is ODD under
simultaneous frequency reflection. The Hermitian orbit with scalar complex
phase `z` equals twice the corrected six-order real symbol times `Im(z)`;
therefore reflection must also conjugate `z`, which changes its imaginary
part's sign. The two sign changes cancel. This pairing holds with three
frequency-dependent, exactly solenoidal polarizations.

Key theorems:

- `thirdFullProjectedHermitianKernel_swap_first_coherent244`
- `thirdFullProjectedHermitianKernel_swap_last_coherent244`
- `thirdFullLabelledWindowedProjectedKernel_noncoherent_zero244`
- `thirdFullLabelledWindowedProjectedKernel_swap_first244`
- `thirdFullLabelledWindowedProjectedKernel_swap_last244`
- `thirdFullFixedCenterTransverseGerm_reflect_coherent244`
- `thirdFullPhysicalHermitianOrbit_reflect_conj_coherent244`
- `thirdFullMovingHermitianOrbit_phase_coherent244`
- `thirdFullMovingHermitianOrbit_reflect_conj_coherent244`

This module concerns pointwise Fourier polynomials and phases. It does NOT
prove that a six-packet *Schwartz* Fourier field has a nonzero integrated
full-third commutator, nor does it assert a Navier--Stokes continuation theorem.
Still needed: the actual complex-valued Hermitian six-window assembly on
`Axis Depth.three`, localization of its complete Fourier integral to the
12 coherent sectors, and a signed integral lower bound using the already
proved local negative tube.

## Build and audit

Run the registration script, regenerate `proof/order.txt` with
`python3 proof/generate_index.py`, check its freshness with `--check`, validate
prose fragments, compile the new Lean module, and run the complete `lake build`.
The assistant-side preparation environment does not contain Lean/mathlib, so
Lean compilation on the project checkout is the required proof-validation gate.
