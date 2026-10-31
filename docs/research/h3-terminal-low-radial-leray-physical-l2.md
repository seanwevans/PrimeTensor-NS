# Low-radial Leray Fourier and physical L² kinetic bridge

**Base:** `1257c5f60f0a0d1338b3c9f8fd45c64b858afba3`.

## Precise result

Let `U(t) = h3AuditActualSpectralVelocityTotal hH3 t`, fix an H³ energy-class
interval `(a,T)`, kinetic anchor `b ∈ (a,T)`, physical time `t ∈ (b,T)`,
Fourier cutoff `ρ ≥ 0`, and coordinate `i : Fin 3`. Put
`Sρ = h3TerminalRadialFrequencyBelow ρ` and `E = velocityH3Energy0At u b`.

The previous proof bounded the **actual** pointwise Fourier Leray forcing
`Nᵢ(U(t),U(t))(ξ)` on `Sρ` by `18 ρ E`. The new theorem proves

    ∫_{Sρ} ‖Nᵢ(U(t),U(t))(ξ)‖² dξ
      ≤ volume(Sρ) · (18 ρ E)².

The Fourier ball has finite measure because `h3FourierGradientMagnitude ξ =
2π‖ξ‖`, so `Sρ` lies in a finite-dimensional Euclidean metric ball.
The case `ρ = 0` is included.

The source is packaged in `h3CriticalLowRadialLerayFourierL2` as a bona fide
complex Fourier L² element using `MemLp.indicator` and `toLp`, and its norm
squared is proved exactly equal to the above integral. Then
`h3CriticalLowRadialLerayPhysicalL2` applies the repository's existing
real inverse-Fourier decoder and its contraction estimate. Thus

    ‖lowRadialLerayPhysicalL2(ρ,U(t),i)‖²
      ≤ volume(Sρ) · (18 ρ E)².

No extra kinetic positivity, Fourier L¹, terminal H³ bound or finite H³
dissipation hypothesis is introduced.

## Remaining proof obligations

1. Identify the real decoded sharp Fourier cutoff with the corresponding
   physical Fourier multiplier acting on the **actual** Leray source.
2. Prove continuous (or a.e.-strongly measurable) time-dependence of that
   physical lowpass family and consequently Bochner-L¹ on every finite
   terminal tail under the uniform kinetic ceiling.
3. Supply the parallel low-frequency physical Laplacian bound.
4. Assemble the lowpass projected momentum-source bound and discharge the
   explicitly conditional `hLow` premise from
   `h3Critical_noL2Trace_fixed_coordinate_highpass_escape_of_lowpass_L1`.

**Caution:** a uniform norm ceiling *alone* is not a Bochner integrability
proof without time measurability; the present file does not claim that step.
