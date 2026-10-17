# Physical real L² convergence of weighted spectral Schwartz approximants

Base: `dabf6137` (2026-10-17).

The previous checkpoint constructed a single three-component spectral Schwartz
sequence that converges in weighted H³, raw Fourier L², and decoded **complex**
physical L². This checkpoint uses the existing real-part L² continuous linear
projection, and its exact linearity, to prove contraction on differences:

    ‖decodeReal(F) - decodeReal(G)‖₂ ≤ ‖F - G‖_{H³ spectral}.

The exact SAME weighted spectral Schwartz sequence then converges in the real
physical L² product. For an actual compatible H³ velocity snapshot,
`h3SpectralVelocityDecodeRealL2_velocityH3SpectralStateAt_apply_eq`
identifies the limit with the actual transported physical zeroth-order jet
`h3ToFourierRealL2 (velocityH3L2JetAt ... (h3JetSlot0 j))`.

## Logical limits

This does not construct real physical Schwartz approximants. The original
Schwartz maps inhabit the weighted complex **frequency** carrier, and their
real-part decoders are only asserted to belong to real physical L².
The next step must construct reality-preserving physical Schwartz representatives
and establish convergence in the complete physical derivative energies E₂/E₃.
Solenoidality and identification of the completed signed transport functional
remain independent obligations. No regularity theorem is claimed.
