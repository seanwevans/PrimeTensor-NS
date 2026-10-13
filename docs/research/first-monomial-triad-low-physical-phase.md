# Seven-derivative physical phase and the cyclic shell frontier

Base checkpoint: `83cb929c` (Fourier reality phase of the sharp low-normal triad).

The previous audit treated multiplication by `i` as a deliberately symbolic
odd-derivative phase. The project's **proved** Schwartz Fourier derivative
identity instead supplies exactly

    (2πi)^7 = -(2π)^7 i.

For the sharp reflected six-order pair,

    Cpair(t) = -2i t² (1+2t)²,

so the real part after multiplying by the **actual seven-derivative phase** is

    Re[(2πi)^7 Cpair(t)] = -2(2π)^7 t²(1+2t)².

It is nonpositive for all real t. Its absolute value remains at least
`2(2π)^7 t²` when `t >= 0`. The patch also scales the preceding sharpness
argument to show that no constant controls this *pointwise physical-phase*
magnitude by the proposed quadratic-separation weight.

## What the repository ALREADY proves

- `FirstMonomialTriadFourier.lean` proves the phase and Schwartz triple
  Fourier-integral identity, including all seven directional derivatives.
- `FirstMonomialTriadAggregate.lean` proves the full coordinate contraction,
  outer-frequency exchange, and the signed shell integral formula.
- `FirstMonomialTriadPhysicalShell.lean` transports the signed shell formula
  to the actual physical first-monomial aggregate, **conditional on** a real
  Schwartz realization of the logged velocity components and divergence-free
  physical data.

Those are genuine substantial bridges, not missing foundational work.

## New cyclic bookkeeping

For one divergence-free Fourier polarization field `U` and any momentum triad
`p+q+r=0`, the patch proves

    shellKernel(U; p,r) + shellKernel(U; p,q) + shellKernel(U; q,r)
      = sixOrderTriadCoefficient(p,q,r; U(p),U(q),U(r)).

The second argument of `shellKernel` is the other outer frequency; the middle
frequency is inferred from momentum. This uses the same actual polarization
field in all three cyclic evaluations rather than three unrelated vectors.

## What remains hard

The sharp pointwise amplitudes do **not** themselves produce a Schwartz
Fourier field or a nonzero integrated physical pairing. To transfer pointwise
sharpness into the integrated formula, prove the two-dimensional measure-
preserving cyclic reindexings, construct compactly supported smooth Fourier
polarizations satisfying divergence and reality, and control every cross-triad
contribution. Only then can a lower bound on an actual integral be asserted.

No new Navier–Stokes regularity or nonregularity conclusion follows here.
