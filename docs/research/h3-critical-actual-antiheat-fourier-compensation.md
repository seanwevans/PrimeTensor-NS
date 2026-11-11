# Actual physical Fourier anti-heat residual and low/high kinetic compensation

Pinned HEAD: `2a8619c2d5f99f5df4ddbfb1cf16c2391f76e856`.

## Genuine physical Fourier bridge

The accepted exact Young gap is `q^3 |N+2q z|²`. At strict time, the genuine
projected physical momentum source is `R=-q z-N` (real physical Fourier
reconstruction and raw-Leray quotient L² representative, not a surrogate).
Therefore, on every sharp highpass, without additional assumptions,

    ∫_{sqrt(q)>=ρ} q³ |N+2qz|² = ∫_{sqrt(q)>=ρ} q³ |qz-Rhat|².

The first three theorems certify the actual a.e. Fourier source and the
localized exact Young-gap residual. No terminal-uniform bound follows.

## Quantitative kinetic compensation

For an orthogonal splitting U=U_low+U_high, R=R_low+R_high,
`<U_low,R_high>=<U_high,R_low>=0`, the actual order-zero kinetic law
`<U,R>=-D0` implies, for every real rate,

    D0 + rate ||U_high||²
      <= ||U_low|| ||R_low|| + ||U_high|| ||R_high-rate U_high||.

If the low-band masses are bounded by M and C, and high-band relative
antiheat mismatch is bounded by eps, then

    (rate-eps) ||U_high||² <= M*C.

The same inequality is specialized to the actual H³-path physical Hilbert
velocity/source using its verified kinetic cancellation.

**Important:** The last theorem accepts explicit decomposition and cross
orthogonality certificates. It does NOT prove that applying the sharp
physical Fourier lowpass to the actual three-component physical Hilbert
states supplies these certificates. That identification, followed by
control of the lowpass source and of q-variation on moving shells, is the
remaining analytic task. The theorem is conditional on those geometric
data; no hidden continuation premise or unproved cancellation is assumed.

## Theorems
- `thirdFullPhysical_actualFourierSource_antiHeatRepresentative244`
- `thirdFullPhysical_actualYoungGap_eq_antiHeatResidual_ae244`
- `thirdFullPhysical_actualYoungGap_highBand_eq_antiHeat244`
- `thirdFullKinetic_twoChannel_antiHeatCompensation244`
- `thirdFullKinetic_twoChannel_highMassGate244`
- `thirdFullPhysical_kineticSplit_highMassGate244`

No new axioms, sorry, admit, or terminal-uniform regularity hypotheses.
