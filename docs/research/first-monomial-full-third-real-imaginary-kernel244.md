# Full third real physical commutator: unphased imaginary Fourier kernel

Base Git checkpoint: `8e61a873` — identify full third physical commutator with Hermitian signed density integral.

The existing full real three-component, divergence-free Schwartz packet has a complete Fourier signed density containing the four `3+3+1` gradient terms, five original physical axis sums, factor `2`, and the `3+2+2` interpolation term with coefficient `6`. All component Fourier integrands are absolutely integrable, and the signed density is pointwise even under simultaneous reflection of the two free frequencies.

This module extracts the *same* common `(2*pi*i)^7` factor from the full complex density and defines `thirdFullAxisRealThirdUnphasedKernel244` without that factor. The result is the exact identity

```
fullSchwartzThirdCommutator244 (realSchwartzVelocity rho A B C)
  = (2*pi)^7 * integral (Imag (thirdFullAxisRealThirdUnphasedKernel244 rho A B C))
```

The imaginary density is even under Hermitian reflection, vanishes outside the exact twelve-center coherent tube, and its negative integral is **equivalent** to the physical static commutator being negative. The commutator integral has an exact phase-free coherent-tube indicator representation. All coefficients, physical index sums, Fourier amplitudes, and frequencies are unchanged. This removes phase bookkeeping from the six-sector sign analysis. No full-sector sign bound or noncancellation is asserted.

Run `tools/audit/register_first_monomial_full_third_real_imaginary_kernel244.py`, regenerate `proof` index, compile module, and build/audit all. No `sorry` or `admit`.
