import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.NineQuarterDuhamelMass
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.MildRawNineQuarter

/-!
# Quantitative nine-quarter Fourier mass of the selected mild state

The selected positive-time mild state decomposes exactly as

    W(t) = H_t U₀ + D(t).

The nonlinear Duhamel term now has the explicit `9/4` envelope

    h3SelectedDuhamelNineQuarterMomentEnvelope ν A t.

For the free heat term, the already-compiled `9/4` heat multiplier estimate and
H³ deweighting give

    ∫ |ξ|^(9/4) |H_t(ξ) Û₀,i(ξ)| dξ
      ≤
    C_{9/4}(ν,t) C_dw A.

This file combines those two quantitative pieces at the named quotient-safe
raw Fourier `L²` level and then transfers the estimate to the canonical raw
Fourier representative used by the nonlinear forcing layer.

Thus one selected coordinate satisfies

    M_{9/4}(W_i(t))
      ≤
    C_{9/4}(ν,t) C_dw A
      + h3SelectedDuhamelNineQuarterMomentEnvelope ν A t.

This is the explicit state envelope needed by the third-variation bootstrap.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzMildNineQuarterMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Explicit `9/4` raw Fourier mass envelope for one selected positive-time
mild coordinate. -/
noncomputable def h3SelectedMildNineQuarterMomentEnvelope
    (ν A t : ℝ) : ℝ :=
  h3HeatNineQuarterMomentCoefficient ν t *
      h3RawFourierL1DeweightingCoefficient * A
    +
  h3SelectedDuhamelNineQuarterMomentEnvelope ν A t

/-- Quantitative `9/4` raw Fourier mass of the explicit selected initial heat
representative. -/
theorem h3SpectralFinHeatLeraySelectedInitialHeat_nineQuarterMoment_integral_le
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        h3FourierNineQuarterWeight ξ *
          ‖h3SpectralScalarHeatRawRepresentative
            ν t (U₀ i) ξ‖)
      ≤
    h3HeatNineQuarterMomentCoefficient ν t *
      h3RawFourierL1DeweightingCoefficient * A := by
  have hRaw :
      Integrable
        (h3SpectralScalarRawFourier (U₀ i))
        (volume : Measure H3FourierPoint3) :=
    MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 (U₀ i))

  have hHeat :=
    h3HeatFourierSymbol_nineQuarter_norm_integral_le
      hν ht
      (h3SpectralScalarRawFourier (U₀ i))
      hRaw

  have hBase :
      (∫ ξ : H3FourierPoint3,
          h3FourierNineQuarterWeight ξ *
            ‖h3SpectralScalarHeatRawRepresentative
              ν t (U₀ i) ξ‖)
        ≤
      h3HeatNineQuarterMomentCoefficient ν t *
        h3SpectralScalarRawFourierL1Mass (U₀ i) := by
    unfold h3SpectralScalarHeatRawRepresentative
    unfold h3SpectralScalarRawFourierL1Mass
    exact hHeat

  have hRawMass :=
    h3SpectralScalarRawFourierL1Mass_le_norm (U₀ i)

  have hHeatCoeff0 :
      0 ≤ h3HeatNineQuarterMomentCoefficient ν t :=
    h3HeatNineQuarterMomentCoefficient_nonneg hν.le ht.le

  have hDeweight :
      h3HeatNineQuarterMomentCoefficient ν t *
          h3SpectralScalarRawFourierL1Mass (U₀ i)
        ≤
      h3HeatNineQuarterMomentCoefficient ν t *
          (h3RawFourierL1DeweightingCoefficient * ‖U₀ i‖) :=
    mul_le_mul_of_nonneg_left hRawMass hHeatCoeff0

  have hCoord :
      ‖U₀ i‖ ≤ A :=
    le_trans
      (h3SpectralVelocity_coordinate_norm_le U₀ i)
      hU₀

  have hCoeff0 :
      0 ≤
        h3HeatNineQuarterMomentCoefficient ν t *
          h3RawFourierL1DeweightingCoefficient :=
    mul_nonneg
      hHeatCoeff0
      h3RawFourierL1DeweightingCoefficient_nonneg

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierNineQuarterWeight ξ *
          ‖h3SpectralScalarHeatRawRepresentative
            ν t (U₀ i) ξ‖)
        ≤
      h3HeatNineQuarterMomentCoefficient ν t *
        h3SpectralScalarRawFourierL1Mass (U₀ i) :=
      hBase
    _ ≤
      h3HeatNineQuarterMomentCoefficient ν t *
        (h3RawFourierL1DeweightingCoefficient * ‖U₀ i‖) :=
      hDeweight
    _ =
      h3HeatNineQuarterMomentCoefficient ν t *
        h3RawFourierL1DeweightingCoefficient *
        ‖U₀ i‖ := by
      ring
    _ ≤
      h3HeatNineQuarterMomentCoefficient ν t *
        h3RawFourierL1DeweightingCoefficient * A :=
      mul_le_mul_of_nonneg_left hCoord hCoeff0

/-- The same quantitative initial-heat `9/4` bound on the named quotient-safe
raw Fourier `L²` package. -/
theorem h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_nineQuarterMass_le
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        h3FourierNineQuarterWeight ξ *
          ‖((h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
              hν U₀ ht i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      ≤
    h3HeatNineQuarterMomentCoefficient ν t *
      h3RawFourierL1DeweightingCoefficient * A := by
  have hRep :=
    h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_ae_eq_heatRepresentative
      hν U₀ ht i

  have hIntegralEq :
      (∫ ξ : H3FourierPoint3,
          h3FourierNineQuarterWeight ξ *
            ‖((h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
                hν U₀ ht i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierNineQuarterWeight ξ *
          ‖h3SpectralScalarHeatRawRepresentative
            ν t (U₀ i) ξ‖ := by
    apply integral_congr_ae
    filter_upwards [hRep] with ξ hξ
    rw [hξ]

  rw [hIntegralEq]

  exact
    h3SpectralFinHeatLeraySelectedInitialHeat_nineQuarterMoment_integral_le
      hν U₀ hA hU₀ ht i

/-- Quantitative `9/4` raw Fourier mass of the named selected mild coordinate. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_nineQuarterMass_le
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        h3FourierNineQuarterWeight ξ *
          ‖((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
              hν U₀ hA hU₀ t i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      ≤
    h3SelectedMildNineQuarterMomentEnvelope ν A t := by
  let H : H3FourierComplexL2 :=
    h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
      hν U₀ ht i

  let D : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
      (t := t) hν U₀ hA hU₀ i

  let W : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
      hν U₀ hA hU₀ t i

  have hHeatInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineQuarterWeight ξ * ‖H ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [H]
    exact
      h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_nineQuarterMoment_integrable
        hν U₀ ht i

  have hDuhamelInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineQuarterWeight ξ * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [D]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_nineQuarterMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hFullInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineQuarterWeight ξ * ‖W ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_nineQuarterMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hRep :
      ((W : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 => H ξ + D ξ) := by
    dsimp only [W, H, D]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_ae_eq_heat_add_duhamel
        hν U₀ hA hU₀ ht htR i

  have hWeightedRep :
      (fun ξ : H3FourierPoint3 =>
        h3FourierNineQuarterWeight ξ * ‖W ξ‖)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        h3FourierNineQuarterWeight ξ * ‖H ξ + D ξ‖) := by
    filter_upwards [hRep] with ξ hξ
    rw [hξ]

  have hSumInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineQuarterWeight ξ * ‖H ξ + D ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hFullInt.congr hWeightedRep

  have hMajorInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineQuarterWeight ξ * ‖H ξ‖ +
            h3FourierNineQuarterWeight ξ * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hHeatInt.add hDuhamelInt

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        h3FourierNineQuarterWeight ξ * ‖H ξ + D ξ‖
          ≤
        h3FourierNineQuarterWeight ξ * ‖H ξ‖ +
          h3FourierNineQuarterWeight ξ * ‖D ξ‖ := by
    intro ξ

    have hw : 0 ≤ h3FourierNineQuarterWeight ξ := by
      unfold h3FourierNineQuarterWeight
      positivity

    calc
      h3FourierNineQuarterWeight ξ * ‖H ξ + D ξ‖
          ≤
        h3FourierNineQuarterWeight ξ * (‖H ξ‖ + ‖D ξ‖) :=
        mul_le_mul_of_nonneg_left
          (norm_add_le (H ξ) (D ξ))
          hw
      _ =
        h3FourierNineQuarterWeight ξ * ‖H ξ‖ +
          h3FourierNineQuarterWeight ξ * ‖D ξ‖ := by
        ring

  have hMono :
      (∫ ξ : H3FourierPoint3,
          h3FourierNineQuarterWeight ξ * ‖H ξ + D ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        (h3FourierNineQuarterWeight ξ * ‖H ξ‖ +
          h3FourierNineQuarterWeight ξ * ‖D ξ‖) :=
    integral_mono hSumInt hMajorInt hPoint

  have hHeatBound :
      (∫ ξ : H3FourierPoint3,
          h3FourierNineQuarterWeight ξ * ‖H ξ‖)
        ≤
      h3HeatNineQuarterMomentCoefficient ν t *
        h3RawFourierL1DeweightingCoefficient * A := by
    dsimp only [H]
    exact
      h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_nineQuarterMass_le
        hν U₀ hA hU₀ ht i

  have hDuhamelBound :
      (∫ ξ : H3FourierPoint3,
          h3FourierNineQuarterWeight ξ * ‖D ξ‖)
        ≤
      h3SelectedDuhamelNineQuarterMomentEnvelope ν A t := by
    dsimp only [D]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_nineQuarterMass_le
        hν U₀ hA hU₀ ht htR i

  have hIntegralEq :
      (∫ ξ : H3FourierPoint3,
          h3FourierNineQuarterWeight ξ * ‖W ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierNineQuarterWeight ξ * ‖H ξ + D ξ‖ :=
    integral_congr_ae hWeightedRep

  unfold h3SelectedMildNineQuarterMomentEnvelope

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierNineQuarterWeight ξ * ‖W ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierNineQuarterWeight ξ * ‖H ξ + D ξ‖ :=
      hIntegralEq
    _ ≤
      ∫ ξ : H3FourierPoint3,
        (h3FourierNineQuarterWeight ξ * ‖H ξ‖ +
          h3FourierNineQuarterWeight ξ * ‖D ξ‖) :=
      hMono
    _ =
      (∫ ξ : H3FourierPoint3,
          h3FourierNineQuarterWeight ξ * ‖H ξ‖) +
        ∫ ξ : H3FourierPoint3,
          h3FourierNineQuarterWeight ξ * ‖D ξ‖ := by
      rw [integral_add hHeatInt hDuhamelInt]
    _ ≤
      h3HeatNineQuarterMomentCoefficient ν t *
          h3RawFourierL1DeweightingCoefficient * A
        +
      h3SelectedDuhamelNineQuarterMomentEnvelope ν A t :=
      add_le_add hHeatBound hDuhamelBound

/-- The same quantitative `9/4` state envelope on the canonical raw Fourier
representative consumed by the nonlinear forcing layer. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_nineQuarterMass_le
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        h3FourierNineQuarterWeight ξ *
          ‖h3SpectralScalarRawFourier
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν U₀ hA hU₀ t i) ξ‖)
      ≤
    h3SelectedMildNineQuarterMomentEnvelope ν A t := by
  have hEq :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_nineQuarterMoment_ae_eq_rawFourierL2
      (t := t)
      hν U₀ hA hU₀ i

  have hIntegralEq :
      (∫ ξ : H3FourierPoint3,
          h3FourierNineQuarterWeight ξ *
            ‖h3SpectralScalarRawFourier
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                hν U₀ hA hU₀ t i) ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierNineQuarterWeight ξ *
          ‖((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
              hν U₀ hA hU₀ t i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖ :=
    integral_congr_ae hEq

  rw [hIntegralEq]

  exact
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_nineQuarterMass_le
      hν U₀ hA hU₀ ht htR i

end
end Euclidean
end Bridge
end PrimeTensor
