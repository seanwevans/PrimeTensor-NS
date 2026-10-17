# Matched compact-weighted / physical Schwartz cubic derivatives (244)

Baseline: commit `a86656d4`.

## Actual analytic bridge

For a complex Schwartz raw Fourier spectrum `S`, the real Schwartz inverse
`psi = Re(F^{-1} S)` has the exact threefold derivative identity

    D_a D_b D_c psi = Re(D_a D_b D_c (F^{-1} S)).

The Fourier transform of the complex derivative is exactly
`(2 pi i xi_a)(2 pi i xi_b)(2 pi i xi_c) S(xi)`, with the complete
ordered multiplier matching `h3FourierDerivativeSymbol3`. The result is
not restricted to distinct indices.

If `F` is a weighted spectral state whose genuine deweighted Fourier L2
class equals `S.toLp`, then the project's actual third-order physical
reconstruction of `F` equals the transported L2 class of the LITERAL
threefold derivative of `psi`. This is proved through Schwartz-Plancherel
compatibility, real projection, and inverse Fourier unitarity.

The final existence theorem chooses a compact smooth weighted representative
from native H3 spectral density and constructs a real Schwartz `psi` such that

  * ||G-F|| < epsilon in the full weighted spectral H3 norm;
  * decodeReal(F) = psi.toLp exactly;
  * ALL 27 ordered third derivative reconstructions of scalar F equal the
    physical L2 embeddings of literal third derivatives of psi.

For three velocity components this corresponds to all 81 cubic slots once
assembled. The separate second-order reconstruction, divergence-free
preservation, and total E2/E3 energy Cauchy theorem remain to be supplied.
