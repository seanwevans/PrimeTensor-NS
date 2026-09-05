import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fourth.Endpoint.Second.Heat.Mass

/-!
# Quantitative second Fourier moment of the selected Duhamel head

The positive-time selected Duhamel head is the shorter-time Duhamel state
evolved by an additional heat lag `t/2`.

At the midpoint,

    D(t/2) =
      h3SpectralFinHeatLerayDuhamel ν (t/2) W W,

and the globally extended selected mild path satisfies

    ‖W(s)‖ ≤ 2 A

for every real `s`.  The already-compiled physical Duhamel estimate therefore
gives

    ‖D(t/2)‖
      ≤
    C_D(ν) sqrt(t/2) (2A) (2A).

One coordinate is no larger than the finite velocity-state norm.  Feeding
that coordinate through the quantitative positive-time heat estimate from
`SecondHeatMass` yields a completely explicit second raw Fourier moment for
the selected Duhamel head.

No higher Fourier moment is used here, so this estimate is non-circular with
respect to the later `9/4` state envelope.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFourthEndpointSecondDuhamelHeadMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- H³ norm envelope for the shorter-time Duhamel state occurring inside the
selected positive-lag head. -/
noncomputable def h3SelectedDuhamelHalfTimeH3Envelope
    (ν A t : ℝ) : ℝ :=
  h3HeatLerayDuhamelPathCoefficient ν *
    Real.sqrt (t / 2) *
    (2 * A) *
    (2 * A)

/-- Explicit second-moment envelope for one selected Duhamel head coordinate. -/
noncomputable def h3SelectedDuhamelHeadSecondMomentEnvelope
    (ν A t : ℝ) : ℝ :=
  h3HeatSecondMomentRawL1Coefficient ν (t / 2) *
    h3RawFourierL1DeweightingCoefficient *
    h3SelectedDuhamelHalfTimeH3Envelope ν A t

theorem h3SelectedDuhamelHalfTimeH3Envelope_nonneg
    {ν A t : ℝ}
    (hA : 0 ≤ A) :
    0 ≤ h3SelectedDuhamelHalfTimeH3Envelope ν A t := by
  unfold h3SelectedDuhamelHalfTimeH3Envelope
  exact
    mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (h3HeatLerayDuhamelPathCoefficient_nonneg ν)
          (Real.sqrt_nonneg _))
        (mul_nonneg (by norm_num) hA))
      (mul_nonneg (by norm_num) hA)

theorem h3SelectedDuhamelHeadSecondMomentEnvelope_nonneg
    {ν A t : ℝ}
    (hA : 0 ≤ A) :
    0 ≤ h3SelectedDuhamelHeadSecondMomentEnvelope ν A t := by
  unfold h3SelectedDuhamelHeadSecondMomentEnvelope
  exact
    mul_nonneg
      (mul_nonneg
        (h3HeatSecondMomentRawL1Coefficient_nonneg ν (t / 2))
        h3RawFourierL1DeweightingCoefficient_nonneg)
      (h3SelectedDuhamelHalfTimeH3Envelope_nonneg hA)

/-- The selected Duhamel state at the midpoint has the expected explicit H³
norm bound inherited from the global `2A` selected path bound. -/
theorem norm_h3SpectralFinHeatLerayDuhamel_selectedRestart_halfTime_le
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ‖h3SpectralFinHeatLerayDuhamel
        ν (t / 2) hν W W‖
      ≤
    h3SelectedDuhamelHalfTimeH3Envelope ν A t := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hWb :=
    h3SpectralFinHeatLerayMildSolutionPhysicalExtension_continuous_bounded
      hν
      (h3FinHeatLerayRestartRadius_pos ν hA).le
      U₀
      hA
      hU₀
      (h3FinHeatLerayRestartRadius_smallness ν hA.le)

  have hWcont : Continuous W := by
    dsimp only [W]
    simpa only [
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
    ] using hWb.1

  have hWbound :
      ∀ s : ℝ, ‖W s‖ ≤ 2 * A := by
    intro s
    dsimp only [W]
    simpa only [
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
    ] using hWb.2 s

  have hhalf : 0 ≤ t / 2 := by
    linarith

  have hTwoA : 0 ≤ 2 * A := by
    positivity

  have hD :=
    norm_h3SpectralFinHeatLerayDuhamel_le_pathCoefficient
      hν
      hhalf
      hTwoA
      hTwoA
      W W
      hWcont hWcont
      hWbound hWbound

  unfold h3SelectedDuhamelHalfTimeH3Envelope
  exact hD

/-- One coordinate of the midpoint Duhamel state has the same H³ envelope. -/
theorem norm_h3SpectralFinHeatLerayDuhamel_selectedRestart_halfTime_coordinate_le
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
    ‖h3SpectralFinHeatLerayDuhamel
        ν (t / 2) hν W W i‖
      ≤
    h3SelectedDuhamelHalfTimeH3Envelope ν A t := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hCoord :
      ‖h3SpectralFinHeatLerayDuhamel
          ν (t / 2) hν W W i‖
        ≤
      ‖h3SpectralFinHeatLerayDuhamel
          ν (t / 2) hν W W‖ :=
    h3SpectralVelocity_coordinate_norm_le
      (h3SpectralFinHeatLerayDuhamel
        ν (t / 2) hν W W)
      i

  have hD :
      ‖h3SpectralFinHeatLerayDuhamel
          ν (t / 2) hν W W‖
        ≤
      h3SelectedDuhamelHalfTimeH3Envelope ν A t := by
    dsimp only [W]
    exact
      norm_h3SpectralFinHeatLerayDuhamel_selectedRestart_halfTime_le
        hν U₀ hA hU₀ ht

  exact le_trans hCoord hD

/-- Quantitative second raw Fourier moment of the explicit heat representative
underlying the selected Duhamel head. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedHead_secondMoment_integral_le
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
        ‖ξ‖ ^ 2 *
          ‖h3SpectralScalarHeatRawRepresentative
            ν (t / 2) G ξ‖)
      ≤
    h3SelectedDuhamelHeadSecondMomentEnvelope ν A t := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let G : H3SpectralScalarState :=
    h3SpectralFinHeatLerayDuhamel
      ν (t / 2) hν W W i

  have hhalf : 0 < t / 2 := by
    linarith

  have hHeat :=
    h3SpectralScalarHeatRawRepresentative_secondMoment_integral_le_norm
      hν hhalf G

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
        h3HeatSecondMomentRawL1Coefficient ν (t / 2) *
          h3RawFourierL1DeweightingCoefficient :=
    mul_nonneg
      (h3HeatSecondMomentRawL1Coefficient_nonneg ν (t / 2))
      h3RawFourierL1DeweightingCoefficient_nonneg

  unfold h3SelectedDuhamelHeadSecondMomentEnvelope

  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3SpectralScalarHeatRawRepresentative
            ν (t / 2) G ξ‖)
        ≤
      h3HeatSecondMomentRawL1Coefficient ν (t / 2) *
        h3RawFourierL1DeweightingCoefficient *
        ‖G‖ :=
      hHeat
    _ ≤
      h3HeatSecondMomentRawL1Coefficient ν (t / 2) *
        h3RawFourierL1DeweightingCoefficient *
        h3SelectedDuhamelHalfTimeH3Envelope ν A t :=
      mul_le_mul_of_nonneg_left hG hCoeff0

/-- Quantitative second-moment bound transferred to the named quotient-safe
selected Duhamel head raw Fourier `L²` state. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_secondMoment_integral_le
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
              hν U₀ hA hU₀ ht i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      ≤
    h3SelectedDuhamelHeadSecondMomentEnvelope ν A t := by
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
          ‖ξ‖ ^ 2 *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
                hν U₀ hA hU₀ ht i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3SpectralScalarHeatRawRepresentative
            ν (t / 2) G ξ‖ := by
    apply integral_congr_ae
    dsimp only [G, W] at hRep ⊢
    filter_upwards [hRep] with ξ hξ
    rw [hξ]

  rw [hIntegralEq]

  dsimp only [G, W]

  exact
    h3SpectralFinHeatLerayDuhamelSelectedHead_secondMoment_integral_le
      hν U₀ hA hU₀ ht i

end
end Euclidean
end Bridge
end PrimeTensor
