# Full-third seven-derivative weighted local integral

Base: `4f46e172` — coherent Hermitian permutation and conjugate-reflection identities.

The previous positive-measure local integral was of an *unweighted* Hermitian
polynomial. Here the actual three labelled smooth scalar frequency windows on
`Axis Depth.three` are multiplied into the corrected frequency-varying
solenoidal Hermitian polynomial. The weighted kernel is continuous, and each
window equals one exactly at its assigned center. Its center coefficient
therefore remains the exact negative Hermitian value -192, and strict
negativity persists on a positive-radius six-dimensional pair ball. The
weighted integral over that ball is strictly negative.

The explicit center instance uses labels `0, 1, 2` at parameter `t=1`,
with p=(1,0,0), q=(1,1,0), r=(-2,-1,0), and real polarizations
A=(0,1,0), B=(1,-1,0), C=(1,-2,0) with the imaginary Hermitian orbit phase.
The window radius is arbitrary positive for this **local** theorem; the
existing noncoherent support exclusion additionally requires a sufficiently
small window radius when proceeding to the global integral.

New proof targets:

- `thirdFullLabelledWindowedProjectedKernel_continuous244`
- `thirdFullLabelledWindowedProjectedKernel_at_centers244`
- `thirdFullLabelledWindowedProjectedKernel_exists_negative_local_integral244`
- `thirdFullLabelledWindowedProjectedKernel_exists_concrete_negative_integral244`

**Critical limit:** This is the integral of the *selected labelled coherent
window coefficient on a local set*. It is not the integral of the full six
packet's Hermitian Schwartz Fourier transform. Twelve coherent sectors must
still be assembled with their actual complex phase, the Fourier measure and
Jacobians, and the Fourier transforms linked back to the real physical
`fullSchwartzThirdCommutator244`. Nothing here proves Navier–Stokes
continuation or global regularity.

## Build

Run the included registration script, `python3 proof/generate_index.py`, its
`--check`, `proof/check_fragment.py --all`, then individual Lean compilation,
the theorem audit and full `lake build` before committing the updated index.
The patch is prepared statically; Lean is not available to typecheck it in
the artifact environment.
