# Pointwise Schwartz reconstruction from exact real H³ spectral L² decoding

Base: `5e915232` — derive Schwartz spectral first jets from zeroth-order realization.

## Previously missing identification

The H³ weighted spectral compact approximation theorem already constructs a weighted
state `F` and genuine real Schwartz map `ψ` with exact equality of their *real
L² decoded states*. The canonical C¹ inverse-Fourier representative of `F`
is proved equal almost everywhere to its decoded L² class. Since `ψ` is
continuous as well, uniqueness of continuous representatives upgrades this
to exact equality at **every** point of Euclidean space. Composing with the
volume-preserving `WithLp.toLp` carrier proves

  `h3SchwartzPoint3Scalar ψ = h3SpectralScalarRealC1RepresentativeOnPoint3 F`.

This is the zeroth-order equality the previous first-jet bridge needed. It
is **derived**, not postulated for the approximating Schwartz sequence.
The result imports existing compact-weighted real Schwartz spectral density,
with the original weighted H³ convergence and third-jet reconstruction limits.

## Genuine new analytic implication

For any two spectral states with matched Schwartz physical representatives:

  `|∂ᵢψ_F(x) - ∂ᵢψ_G(x)| ≤ C₁ ‖F-G‖_{weighted H³}`.

For the coherent sequence `F_n → G`, actual first derivative Schwartz fields
converge pointwise to the canonical H³ C¹ derivative of `G`; **G need not be
Schwartz**. This bypasses the earlier need to posit a Schwartz target when
studying first-jet convergence.

## Still open

The signed monomial's second-derivative L⁴ convergence and top dissipation
H⁴ convergence do not follow just from H³ spectral convergence. Identifying
the complete nonlinear physical transport at an arbitrary path slice is still
required. None of these results prove unrestricted Navier–Stokes regularity.
