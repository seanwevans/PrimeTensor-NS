# Complete six-permutation third-order derivative symbol

Base commit: `6355d7fb` (`close ordered triad sums and positive axis coordinate evaluation`).

The previous module proves an **ordered real derivative polynomial**

  S(p,q,r; A,B,C) = (A·C)(B·r) (p·q) [(p·q)^2 + 3(p·q)(p·r) + 3(p·r)^2].

Here `p` labels the differentiated test velocity, `q` the advecting velocity,
and `r` the transported velocity. The polarization at each frequency moves
with that frequency when we permute the three pairs.

For the explicit momenta and polarizations

    p=( 1, 0,0), q=( 1, 1,0), r=(-2,-1,0),
    A=( 0, 1,0), B=( 1,-1,0), C=( 1,-2,0),

we have `p+q+r=0` and `p·A=q·B=r·C=0`. Six ordered evaluations give:

| Permutation | S |
| --- | ---: |
| pqr | 14 |
| prq | -2 |
| qpr | -57 |
| qrp | 9 |
| rpq | -294 |
| rqp | 234 |
| **sum** | **-96** |

The new source proves these *separately*, the sum, permutation invariance,
and the odd-frequency-reflection law `S(-p,-q,-r;A,B,C)=-S(p,q,r;A,B,C)`.

## Hard analytic frontier (not claimed closed)

This is the six-permuted **real derivative polynomial**. Physical Fourier
products insert `(2 π i)^7` and their amplitudes are complex, with Hermitian
reflection `U(-ξ)=conj U(ξ)`. Pure real Fourier amplitude packets and their
reflected copies can cancel an odd derivative symbol. A nonzero real Fourier
physical integral therefore requires a deliberate relative phase, Fourier
support localization and a signed lower bound for the *actual* Schwartz
construction. The coefficients in this module do not by themselves show
`fullSchwartzThirdCommutator244 f ≠ 0` for any specific f, nor rule out
Navier–Stokes continuation. The next proof should address that analytic bridge.
