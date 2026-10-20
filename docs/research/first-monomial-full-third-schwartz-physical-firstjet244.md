# Physical first-jet uniform limit of synchronized H³ Schwartz approximation

Base `be92bf44` — synchronize Schwartz decoder and mixed H³ Sobolev jets.

## Mathematical step

For `u(t)` a genuinely Fourier-compatible old physical H³ velocity slice of
a preterminal Navier–Stokes-admissible path, the already proved BKM
reconstruction theorem identifies its canonical real `C¹` spectral
representative with `loggedVelocityComponent u t` as **pointwise** functions.
The prior decoder-realization theorem identifies the Schwartz approximants'
first jets with the corresponding spectral first jets exactly.

Combining both results with the existing coordinate evaluation coefficient
`C₁ = h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient` gives

    ∀ n j i x,
      |(∂ᵢ Ψₙⱼ)(x) - (∂ᵢ uⱼ)(ofLp x)|
        ≤ C₁ ‖Vₙⱼ - Uⱼ‖.

Because `Vₙ → U` in the actual weighted H³ spectral velocity space, the
right-hand side is a uniform-in-space vanishing gauge for each component.
The same Ψ sequence has `SchwartzMixedJetGraphCauchy244`, hence 27 genuine
second-jet L⁴ and 81 third-jet L² Cauchy estimates by already-compiled GN
results. Its 243-slot signed monomial converges to the choice-independent
`weightedH3CanonicalSignedFirstMonomial244 U`.

`h3PhysicalSnapshotCanonicalSignedMonomial244` is explicitly the latter
functional evaluated at the physical slice's Fourier H³ encoding. It is **not**
identified here with the independently defined Navier–Stokes cubic pairing.
That requires an L²/L⁴ product identification on the non-Schwartz target.
An H⁴ dissipation limit is also not implied by H³ density.

## Exported results

- `h3PhysicalSnapshotCanonicalSignedMonomial244` (definition)
- `thirdFullSchwartz_physicalFirstJetError_le_spectral244`
- `exists_thirdFullSchwartz_physicalFirstJetGaugeAndSigned244`
- `exists_thirdFullSchwartz_physicalFirstJetTendstoAndSigned244`

The pointwise conclusion uses the strong full-space uniform estimate, not
simply independent pointwise convergence of the first derivatives.
