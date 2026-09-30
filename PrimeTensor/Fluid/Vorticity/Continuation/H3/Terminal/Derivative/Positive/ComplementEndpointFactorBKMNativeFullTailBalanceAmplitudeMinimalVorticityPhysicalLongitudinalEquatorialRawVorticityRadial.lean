import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityPhysicalLongitudinalEquatorialNormalizedVorticityChannel

/-!
# Raw vorticity behind the normalized equatorial obstruction

The preceding checkpoint identified the frozen degree-zero curl channel with a
fixed complementary normalized-vorticity symbol.

This file exposes the exact raw symbol underneath it.  For nonzero radial
frequency,

    normalizedVorticity_q(ξ,g)
      =
    rawVorticity_q(ξ,g) / |D(ξ)|.

Equivalently,

    |rawVorticity_q|
      =
    |D| |normalizedVorticity_q|.

Hence on every radial region `ρ ≤ |D|` with `ρ > 0`,

    ρ² |normalizedVorticity_q|²
      ≤
    |rawVorticity_q|².

This is intentionally pointwise.  Integrating the raw quantity globally would
require an additional radial derivative of the weighted H³ spectral state.
No such H⁴ assumption is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalPhysicalLongitudinalEquatorialRawVorticityRadial
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Raw vorticity-symbol components -/

/--
Raw Fourier vorticity-symbol amplitude in the physical coordinate convention

* `q = 0`: `d₁ g₂ - d₂ g₁`,
* `q = 1`: `d₂ g₀ - d₀ g₂`,
* `q = 2`: `d₀ g₁ - d₁ g₀`.
-/
def h3TerminalRawVorticityComponentAmplitude
    (q : Fin 3)
    (ξ : H3FourierPoint3)
    (g : Fin 3 → ℂ) : ℂ :=
  if q = 0 then
    h3FourierDerivativeSymbol (1 : Fin 3) ξ * g 2
      -
    h3FourierDerivativeSymbol (2 : Fin 3) ξ * g 1
  else if q = 1 then
    h3FourierDerivativeSymbol (2 : Fin 3) ξ * g 0
      -
    h3FourierDerivativeSymbol (0 : Fin 3) ξ * g 2
  else
    h3FourierDerivativeSymbol (0 : Fin 3) ξ * g 1
      -
    h3FourierDerivativeSymbol (1 : Fin 3) ξ * g 0

/--
Away from zero radial frequency, normalized vorticity is exactly raw
vorticity divided by the radial gradient magnitude.
-/
theorem normalizedVorticityComponentAmplitude_eq_raw_div_gradientMagnitude
    (q : Fin 3)
    (ξ : H3FourierPoint3)
    (g : Fin 3 → ℂ)
    (hGrad :
      0 < h3FourierGradientMagnitude ξ) :
    h3TerminalNormalizedVorticityComponentAmplitude q ξ g
      =
    h3TerminalRawVorticityComponentAmplitude q ξ g
      /
    (h3FourierGradientMagnitude ξ : ℂ) := by

  fin_cases q <;>
    simp [
      h3TerminalNormalizedVorticityComponentAmplitude,
      h3TerminalRawVorticityComponentAmplitude,
      h3TerminalNormalizedCurl01Amplitude,
      h3TerminalNormalizedCurl02Amplitude,
      h3TerminalNormalizedCurl12Amplitude,
      h3TerminalNormalizedDerivativeSymbol,
      hGrad.ne'
    ] <;>
    ring

/--
Norm form of the raw/normalized relation.
-/
theorem norm_normalizedVorticityComponentAmplitude_eq_raw_div_gradientMagnitude
    (q : Fin 3)
    (ξ : H3FourierPoint3)
    (g : Fin 3 → ℂ)
    (hGrad :
      0 < h3FourierGradientMagnitude ξ) :
    norm
      (
        h3TerminalNormalizedVorticityComponentAmplitude
          q ξ g
      )
      =
    norm
      (
        h3TerminalRawVorticityComponentAmplitude
          q ξ g
      )
      /
    h3FourierGradientMagnitude ξ := by

  rw [
    normalizedVorticityComponentAmplitude_eq_raw_div_gradientMagnitude
      q ξ g hGrad,
    norm_div,
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_pos hGrad
  ]

/--
Equivalent multiplicative norm identity: raw vorticity carries one radial
frequency factor relative to normalized vorticity.
-/
theorem norm_rawVorticityComponentAmplitude_eq_gradientMagnitude_mul_normalized
    (q : Fin 3)
    (ξ : H3FourierPoint3)
    (g : Fin 3 → ℂ)
    (hGrad :
      0 < h3FourierGradientMagnitude ξ) :
    norm
      (
        h3TerminalRawVorticityComponentAmplitude
          q ξ g
      )
      =
    h3FourierGradientMagnitude ξ
      *
    norm
      (
        h3TerminalNormalizedVorticityComponentAmplitude
          q ξ g
      ) := by

  have hNorm :=
    norm_normalizedVorticityComponentAmplitude_eq_raw_div_gradientMagnitude
      q ξ g hGrad

  have hGradNe :
      h3FourierGradientMagnitude ξ ≠ 0 :=
    hGrad.ne'

  calc
    norm
        (
          h3TerminalRawVorticityComponentAmplitude
            q ξ g
        )
        =
      h3FourierGradientMagnitude ξ
        *
      (
        norm
          (
            h3TerminalRawVorticityComponentAmplitude
              q ξ g
          )
          /
        h3FourierGradientMagnitude ξ
      ) := by
        field_simp [hGradNe]
    _ =
      h3FourierGradientMagnitude ξ
        *
      norm
        (
          h3TerminalNormalizedVorticityComponentAmplitude
            q ξ g
        ) := by
          rw [hNorm]

/-! ## Radial lower-frequency cutoff -/

/--
Radial region bounded away from zero frequency.
-/
def h3TerminalRadialFrequencyAbove
    (ρ : ℝ) :
    Set H3FourierPoint3 :=
  {
    ξ |
      ρ
        ≤
      h3FourierGradientMagnitude ξ
  }

/--
On frequencies `|D| ≥ ρ > 0`, raw-vorticity square dominates `ρ²` times
normalized-vorticity square.
-/
theorem sq_mul_normalizedVorticity_le_rawVorticity_sq_of_mem_radialFrequencyAbove
    {ρ : ℝ}
    (hρ : 0 < ρ)
    {ξ : H3FourierPoint3}
    (hHigh :
      ξ ∈ h3TerminalRadialFrequencyAbove ρ)
    (q : Fin 3)
    (g : Fin 3 → ℂ) :
    ρ ^ 2
        *
      norm
        (
          h3TerminalNormalizedVorticityComponentAmplitude
            q ξ g
        ) ^ 2
      ≤
    norm
      (
        h3TerminalRawVorticityComponentAmplitude
          q ξ g
      ) ^ 2 := by

  change
    ρ
      ≤
    h3FourierGradientMagnitude ξ
    at hHigh

  have hGrad :
      0 < h3FourierGradientMagnitude ξ :=
    lt_of_lt_of_le
      hρ
      hHigh

  have hRadialSq :
      ρ ^ 2
        ≤
      h3FourierGradientMagnitude ξ ^ 2 :=
    (
      sq_le_sq₀
        (le_of_lt hρ)
        (le_of_lt hGrad)
    ).2
      hHigh

  have hNormRaw :=
    norm_rawVorticityComponentAmplitude_eq_gradientMagnitude_mul_normalized
      q ξ g hGrad

  calc
    ρ ^ 2
          *
        norm
          (
            h3TerminalNormalizedVorticityComponentAmplitude
              q ξ g
          ) ^ 2
        ≤
      h3FourierGradientMagnitude ξ ^ 2
          *
        norm
          (
            h3TerminalNormalizedVorticityComponentAmplitude
              q ξ g
          ) ^ 2 :=
        mul_le_mul_of_nonneg_right
          hRadialSq
          (sq_nonneg _)
    _ =
      (
        h3FourierGradientMagnitude ξ
          *
        norm
          (
            h3TerminalNormalizedVorticityComponentAmplitude
              q ξ g
          )
      ) ^ 2 := by
        ring
    _ =
      norm
        (
          h3TerminalRawVorticityComponentAmplitude
            q ξ g
        ) ^ 2 := by
          rw [← hNormRaw]

end

end Euclidean
end Bridge
end PrimeTensor
