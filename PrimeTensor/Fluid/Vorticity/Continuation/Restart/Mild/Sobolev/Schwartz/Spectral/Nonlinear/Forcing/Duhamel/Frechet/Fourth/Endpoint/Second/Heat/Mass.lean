import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fourth.Endpoint.Third.Variation.Zero.Envelope
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.MildSecond

/-!
# Quantitative second Fourier moment of positive-time heat pieces

The only remaining state envelope in the full-third variation argument is the
uniform positive-time `9/4` raw Fourier mass.

The frozen `9/4` endpoint estimate passes through a quantitative first forcing
moment, which in turn needs a quantitative second moment of the selected mild
state.  This file starts that lower bootstrap by quantifying the easiest
piece: positive-time heat evolution.

The already-compiled multiplier theorem gives, for every positive heat time,

    |ξ|² |H_t(ξ)| ≤ (sqrt(ν (t/3))⁻¹)².

Therefore

    ∫ |ξ|² |H_t f̂|
      ≤ C₂(ν,t) ∫ |f̂|
      ≤ C₂(ν,t) C_dw ‖G‖.

The last inequality uses the quantitative H³ deweighting theorem from
`ThirdVariationZeroEnvelope`.

We also transfer the bound to the named quotient-safe free-heat `L²` package
used in the selected mild decomposition.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFourthEndpointSecondHeatMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Positive-time second-moment heat multiplier coefficient. -/
noncomputable def h3HeatSecondMomentRawL1Coefficient
    (ν t : ℝ) : ℝ :=
  ((Real.sqrt (ν * (t / 3)))⁻¹) ^ (2 : ℕ)

/-- The second-moment heat coefficient is nonnegative. -/
theorem h3HeatSecondMomentRawL1Coefficient_nonneg
    (ν t : ℝ) :
    0 ≤ h3HeatSecondMomentRawL1Coefficient ν t := by
  unfold h3HeatSecondMomentRawL1Coefficient
  positivity

/-- The explicit positive-time heat representative has second raw Fourier mass
bounded by the heat multiplier coefficient times the input raw `L¹` mass. -/
theorem h3SpectralScalarHeatRawRepresentative_secondMoment_integral_le_rawL1
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState) :
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖)
      ≤
    h3HeatSecondMomentRawL1Coefficient ν t *
      h3SpectralScalarRawFourierL1Mass G := by
  have hRaw :
      Integrable
        (h3SpectralScalarRawFourier G)
        (volume : Measure H3FourierPoint3) :=
    MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 G)

  have hTarget :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 *
            ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    h3SpectralScalarHeatRawRepresentative_moment_integrable
      hν ht G 2 (by norm_num)

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3HeatSecondMomentRawL1Coefficient ν t *
            ‖h3SpectralScalarRawFourier G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hRaw.norm.const_mul
      (h3HeatSecondMomentRawL1Coefficient ν t)

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
            ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖
          ≤
        h3HeatSecondMomentRawL1Coefficient ν t *
          ‖h3SpectralScalarRawFourier G ξ‖ := by
    intro ξ

    have hHeat :=
      h3HeatFourierMomentMultiplier_le_three
        hν ht 2 (by norm_num) ξ

    unfold h3SpectralScalarHeatRawRepresentative
    rw [norm_mul]

    calc
      ‖ξ‖ ^ 2 *
          (‖h3HeatFourierSymbol ν t ξ‖ *
            ‖h3SpectralScalarRawFourier G ξ‖)
          =
        (‖ξ‖ ^ 2 * ‖h3HeatFourierSymbol ν t ξ‖) *
          ‖h3SpectralScalarRawFourier G ξ‖ := by
        ring
      _ ≤
        (((Real.sqrt (ν * (t / 3)))⁻¹) ^ (2 : ℕ)) *
          ‖h3SpectralScalarRawFourier G ξ‖ :=
        mul_le_mul_of_nonneg_right
          hHeat
          (norm_nonneg _)
      _ =
        h3HeatSecondMomentRawL1Coefficient ν t *
          ‖h3SpectralScalarRawFourier G ξ‖ := by
        rfl

  have hIntegral :=
    integral_mono hTarget hMajor hPoint

  unfold h3SpectralScalarRawFourierL1Mass

  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        h3HeatSecondMomentRawL1Coefficient ν t *
          ‖h3SpectralScalarRawFourier G ξ‖ :=
      hIntegral
    _ =
      h3HeatSecondMomentRawL1Coefficient ν t *
        ∫ ξ : H3FourierPoint3,
          ‖h3SpectralScalarRawFourier G ξ‖ := by
      rw [integral_const_mul]

/-- Quantitative positive-time second-moment smoothing directly from the H³
solver norm. -/
theorem h3SpectralScalarHeatRawRepresentative_secondMoment_integral_le_norm
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState) :
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖)
      ≤
    h3HeatSecondMomentRawL1Coefficient ν t *
      h3RawFourierL1DeweightingCoefficient *
      ‖G‖ := by
  have hBase :=
    h3SpectralScalarHeatRawRepresentative_secondMoment_integral_le_rawL1
      hν ht G

  have hRaw :=
    h3SpectralScalarRawFourierL1Mass_le_norm G

  have hCoeff0 :
      0 ≤ h3HeatSecondMomentRawL1Coefficient ν t :=
    h3HeatSecondMomentRawL1Coefficient_nonneg ν t

  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖)
        ≤
      h3HeatSecondMomentRawL1Coefficient ν t *
        h3SpectralScalarRawFourierL1Mass G :=
      hBase
    _ ≤
      h3HeatSecondMomentRawL1Coefficient ν t *
        (h3RawFourierL1DeweightingCoefficient * ‖G‖) :=
      mul_le_mul_of_nonneg_left hRaw hCoeff0
    _ =
      h3HeatSecondMomentRawL1Coefficient ν t *
        h3RawFourierL1DeweightingCoefficient *
        ‖G‖ := by
      ring

/-- The selected initial free-heat coordinate has an explicit second-moment
bound in terms of the restart radius parameter `A`. -/
theorem h3SpectralFinHeatLeraySelectedInitialHeat_secondMoment_integral_le
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3SpectralScalarHeatRawRepresentative
            ν t (U₀ i) ξ‖)
      ≤
    h3HeatSecondMomentRawL1Coefficient ν t *
      h3RawFourierL1DeweightingCoefficient *
      A := by
  have hHeat :=
    h3SpectralScalarHeatRawRepresentative_secondMoment_integral_le_norm
      hν ht (U₀ i)

  have hCoord :
      ‖U₀ i‖ ≤ A :=
    le_trans
      (h3SpectralVelocity_coordinate_norm_le U₀ i)
      hU₀

  have hCoeff0 :
      0 ≤
        h3HeatSecondMomentRawL1Coefficient ν t *
          h3RawFourierL1DeweightingCoefficient :=
    mul_nonneg
      (h3HeatSecondMomentRawL1Coefficient_nonneg ν t)
      h3RawFourierL1DeweightingCoefficient_nonneg

  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3SpectralScalarHeatRawRepresentative
            ν t (U₀ i) ξ‖)
        ≤
      h3HeatSecondMomentRawL1Coefficient ν t *
        h3RawFourierL1DeweightingCoefficient *
        ‖U₀ i‖ :=
      hHeat
    _ ≤
      h3HeatSecondMomentRawL1Coefficient ν t *
        h3RawFourierL1DeweightingCoefficient *
        A :=
      mul_le_mul_of_nonneg_left hCoord hCoeff0

/-- The same numerical free-heat bound on the named quotient-safe raw Fourier
`L²` state used by the selected mild decomposition. -/
theorem h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_secondMoment_integral_le
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖((h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
              hν U₀ ht i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      ≤
    h3HeatSecondMomentRawL1Coefficient ν t *
      h3RawFourierL1DeweightingCoefficient *
      A := by
  have hRep :=
    h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_ae_eq_heatRepresentative
      hν U₀ ht i

  have hIntegralEq :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 *
            ‖((h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
                hν U₀ ht i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3SpectralScalarHeatRawRepresentative
            ν t (U₀ i) ξ‖ := by
    apply integral_congr_ae
    filter_upwards [hRep] with ξ hξ
    rw [hξ]

  rw [hIntegralEq]

  exact
    h3SpectralFinHeatLeraySelectedInitialHeat_secondMoment_integral_le
      hν U₀ hA hU₀ ht i

end
end Euclidean
end Bridge
end PrimeTensor
