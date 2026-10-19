# Actual positive-sector full-third interpolation phase

Baseline: `bc556d1f` (“extract real cubic Fourier phase from actual full third coherent sectors”).

The physical seven-derivative third-order coefficient has already been reduced
exactly to the full unphased imaginary Fourier kernel. Its two constituents
are the four genuine `3+3+1` gradient patterns with their five index sums,
and six times the **actual** `3+2+2` interpolation channel.

## New mathematical step

On each of the six positive coherent sectors with nonzero actual Schwartz triple
mass, the previous Fourier identification gives three independently windowed,
solenoidal, *real* frequency-dependent germs `G_p,G_q,G_r` with phases
`α,β,γ∈{1,i}` satisfying `αβγ=i`. Here `q=-(p+r)`.

The literal physical interpolation kernel is

`complexCoefficient p q r (U q) * amplitudeDot (U p) (U r)`.

Using the exact finite sums defining `mixedDot` and **bilinear**, rather than
Hermitian, `amplitudeDot`, this kernel equals

`i * ((dot p r) * (dot p q)^2 * (dot r G_q) * (dot G_p G_r))`.

The window amplitudes remain in `G_p,G_q,G_r`; no cutoff is dropped or
replaced by its sharp-center value. Consequently the actual interpolation
kernel has zero real part and the indicated real coefficient as its
imaginary part throughout every nonzero-mass positive coherent sector.

The full physical unphased imaginary density is therefore **exactly**

`Im(full genuine five-index gradient sum) + 6 * realInterpolationCoefficient`.

## What is **not** proved

This is not a constant-sign theorem. The five-index `3+3+1` gradient sum
still has to be reduced to the same real moving-polarization polynomial, and
then the complete real density must be compared with the corrected sharp
`-192` six-orbit symbol and bounded uniformly on the six positive sectors.
No Navier–Stokes continuation or global noncancellation is claimed.

## Build and audit

`python3 tools/audit/register_first_monomial_full_third_real_sector_interpolation_phase244.py`

`lake env lean PrimeTensor/Fluid/Vorticity/Continuation/H3/Control/FirstMonomialTriadLowQuarterPoint3FullThirdRealSectorInterpolationPhase244.lean`
