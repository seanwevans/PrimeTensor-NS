import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.NineQuarterTailStateMass
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fourth.Endpoint.SecondDuhamelHeadMass
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Third.Endpoint.NineQuarterHeat

/-!
# Quantitative nine-quarter mass of the selected Duhamel midpoint head

The selected midpoint head is the half-time Duhamel state evolved by the
strictly positive heat lag `t/2`.

The quantitative `9/4` heat multiplier estimate gives

    ∫ |ξ|^(9/4) |H_{t/2}(ξ) F(ξ)| dξ
      ≤
    C_{9/4}(ν,t/2) ∫ |F(ξ)| dξ.

The H³ deweighting bound gives

    ∫ |F(ξ)| dξ ≤ C_dw ‖G‖,

and `SecondDuhamelHeadMass` already proves

    ‖G‖ ≤ h3SelectedDuhamelHalfTimeH3Envelope ν A t.

Hence the explicit selected head budget is

    C_{9/4}(ν,t/2)
      * C_dw
      * h3SelectedDuhamelHalfTimeH3Envelope ν A t.

The final theorem transfers this estimate to the named quotient-safe raw
Fourier `L²` head state through the already-compiled a.e. representative
identity.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzNineQuarterHeadMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Explicit `9/4` raw Fourier mass envelope for one selected midpoint-head
coordinate. -/
noncomputable def h3SelectedDuhamelHeadNineQuarterMomentEnvelope
    (ν A t : ℝ) : ℝ :=
  h3HeatNineQuarterMomentCoefficient ν (t / 2) *
    h3RawFourierL1DeweightingCoefficient *
    h3SelectedDuhamelHalfTimeH3Envelope ν A t

theorem h3SelectedDuhamelHeadNineQuarterMomentEnvelope_nonneg
    {ν A t : ℝ}
    (hν : 0 ≤ ν)
    (hA : 0 ≤ A)
    (ht : 0 ≤ t) :
    0 ≤ h3SelectedDuhamelHeadNineQuarterMomentEnvelope ν A t := by
  unfold h3SelectedDuhamelHeadNineQuarterMomentEnvelope
  exact
    mul_nonneg
      (mul_nonneg
        (h3HeatNineQuarterMomentCoefficient_nonneg
          hν (by linarith : 0 ≤ t / 2))
        h3RawFourierL1DeweightingCoefficient_nonneg)
      (h3SelectedDuhamelHalfTimeH3Envelope_nonneg hA)

/-- Quantitative `9/4` raw Fourier mass of the explicit heat representative
underlying the selected Duhamel midpoint head. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedHead_nineQuarterMoment_integral_le
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let G : H3SpectralScalarState :=
      h3SpectralFinHeatLerayDuhamel
        ν (t / 2) hν W W i
    (∫ ξ : H3FourierPoint3,
        h3FourierNineQuarterWeight ξ *
          ‖h3SpectralScalarHeatRawRepresentative
            ν (t / 2) G ξ‖)
      ≤
    h3SelectedDuhamelHeadNineQuarterMomentEnvelope ν A t := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let G : H3SpectralScalarState :=
    h3SpectralFinHeatLerayDuhamel
      ν (t / 2) hν W W i

  have hhalf : 0 < t / 2 := by
    linarith

  have hRaw :
      Integrable
        (h3SpectralScalarRawFourier G)
        (volume : Measure H3FourierPoint3) :=
    MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 G)

  have hHeat :=
    h3HeatFourierSymbol_nineQuarter_norm_integral_le
      hν hhalf
      (h3SpectralScalarRawFourier G)
      hRaw

  have hHeatRep :
      (∫ ξ : H3FourierPoint3,
          h3FourierNineQuarterWeight ξ *
            ‖h3SpectralScalarHeatRawRepresentative
              ν (t / 2) G ξ‖)
        ≤
      h3HeatNineQuarterMomentCoefficient ν (t / 2) *
        h3SpectralScalarRawFourierL1Mass G := by
    unfold h3SpectralScalarHeatRawRepresentative
    unfold h3SpectralScalarRawFourierL1Mass
    exact hHeat

  have hRawMass :=
    h3SpectralScalarRawFourierL1Mass_le_norm G

  have hHeatCoeff0 :
      0 ≤ h3HeatNineQuarterMomentCoefficient ν (t / 2) :=
    h3HeatNineQuarterMomentCoefficient_nonneg hν.le hhalf.le

  have hRawBound :
      h3HeatNineQuarterMomentCoefficient ν (t / 2) *
          h3SpectralScalarRawFourierL1Mass G
        ≤
      h3HeatNineQuarterMomentCoefficient ν (t / 2) *
          (h3RawFourierL1DeweightingCoefficient * ‖G‖) :=
    mul_le_mul_of_nonneg_left hRawMass hHeatCoeff0

  have hG :
      ‖G‖
        ≤
      h3SelectedDuhamelHalfTimeH3Envelope ν A t := by
    dsimp only [G, W]
    exact
      norm_h3SpectralFinHeatLerayDuhamel_selectedRestart_halfTime_coordinate_le
        hν U₀ hA hU₀ ht i

  have hCoeff0 :
      0 ≤
        h3HeatNineQuarterMomentCoefficient ν (t / 2) *
          h3RawFourierL1DeweightingCoefficient :=
    mul_nonneg
      hHeatCoeff0
      h3RawFourierL1DeweightingCoefficient_nonneg

  unfold h3SelectedDuhamelHeadNineQuarterMomentEnvelope

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierNineQuarterWeight ξ *
          ‖h3SpectralScalarHeatRawRepresentative
            ν (t / 2) G ξ‖)
        ≤
      h3HeatNineQuarterMomentCoefficient ν (t / 2) *
        h3SpectralScalarRawFourierL1Mass G :=
      hHeatRep
    _ ≤
      h3HeatNineQuarterMomentCoefficient ν (t / 2) *
        (h3RawFourierL1DeweightingCoefficient * ‖G‖) :=
      hRawBound
    _ =
      h3HeatNineQuarterMomentCoefficient ν (t / 2) *
        h3RawFourierL1DeweightingCoefficient *
        ‖G‖ := by
      ring
    _ ≤
      h3HeatNineQuarterMomentCoefficient ν (t / 2) *
        h3RawFourierL1DeweightingCoefficient *
        h3SelectedDuhamelHalfTimeH3Envelope ν A t :=
      mul_le_mul_of_nonneg_left hG hCoeff0

/-- Quantitative `9/4` bound transferred to the named quotient-safe selected
Duhamel midpoint-head raw Fourier `L²` state. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_nineQuarterMass_le
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        h3FourierNineQuarterWeight ξ *
          ‖((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
              hν U₀ hA hU₀ ht i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      ≤
    h3SelectedDuhamelHeadNineQuarterMomentEnvelope ν A t := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let G : H3SpectralScalarState :=
    h3SpectralFinHeatLerayDuhamel
      ν (t / 2) hν W W i

  have hRep :=
    h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_ae_eq_heatRepresentative
      hν U₀ hA hU₀ ht i

  have hIntegralEq :
      (∫ ξ : H3FourierPoint3,
          h3FourierNineQuarterWeight ξ *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
                hν U₀ hA hU₀ ht i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierNineQuarterWeight ξ *
          ‖h3SpectralScalarHeatRawRepresentative
            ν (t / 2) G ξ‖ := by
    apply integral_congr_ae
    dsimp only [G, W] at hRep ⊢
    filter_upwards [hRep] with ξ hξ
    rw [hξ]

  rw [hIntegralEq]

  dsimp only [G, W]

  exact
    h3SpectralFinHeatLerayDuhamelSelectedHead_nineQuarterMoment_integral_le
      hν U₀ hA hU₀ ht i

end
end Euclidean
end Bridge
end PrimeTensor
