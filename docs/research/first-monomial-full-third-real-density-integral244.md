# Real full-third signed-density integral (checkpoint ee2ecf30)

The previous `FirstMonomialTriadLowQuarterPoint3FullThirdRealInterpolationReflection244.lean`
constructed an actual real-valued signed Fourier density from all four 3+3+1
Schwartz gradient patterns, all five physical axis sums, and the 3+2+2
interpolation transport coefficient 6, and showed pointwise Hermitian
reflection evenness plus exclusion outside the twelve coherent frequency sectors.

This module supplies the missing **integration bridge**. It defines a complex
Schwartz Fourier density with four actual gradient slots and a final
interpolation summand. Absolute integrability is proved *before* exchanging
finite sums, pulling scalars through integrals, or taking real parts.

It then proves:

- `thirdFullAxisRealThirdComplexDensity_integral244`: integrating the full
  complex density exactly recovers `fullThirdSchwartzFourierCoefficient244`
  of the recovered physical real Schwartz velocity.
- `thirdFullAxisRealThirdSignedDensity_eq_complex_re244`: the previously
  constructed real density is literally the complex density's real part.
- `thirdFullAxisRealThirdCommutator_eq_signedDensity_integral244`: integrating
  that real density over the entire six-dimensional Fourier pair carrier is
  exactly the original full static physical H³ commutator.
- `thirdFullAxisRealThirdCommutator_eq_signedDensity_tube244`: when the Fourier
  packet is narrow enough, the same physical coefficient is an integral over
  the common twelve-center tube and zero elsewhere.
- `thirdFullAxisRealThirdCommutator_exists_signedDensity_tube244`: the packet
  width may be chosen uniformly over all three real polarization parameters.

No Jacobian or normalization constant is silently inserted. The physical
factor two, the interpolation coefficient six, and the seventh-power Fourier
phase remain explicit throughout.

**Unsolved analytic frontier:** reflection evenness prevents cancellation
*solely due to opposite-frequency conjugation*, but does not give a common
sign on the six independent permutation sectors. Pointwise positivity or
negativity for the complete assembled signed density on its true support,
or a quantitative domination argument for any adverse sectors, is still
required to prove global noncancellation. Nothing here constructs a
Navier–Stokes blowup or proves global regularity.
