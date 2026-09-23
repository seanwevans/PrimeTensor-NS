import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathOrderTwoSelectedVelocityHeatRadialL2Bound
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.Mild.Second

/-!
# Uniform raw Fourier L² bound for the selected Duhamel state

The remaining order-two velocity continuity argument splits the nonlinear
Duhamel term at a positive midpoint.  To heat-smooth the earlier history
uniformly, we only need one unweighted `L²` ceiling for the complete Duhamel
state.

The exact quotient-safe mild equation is

    W(t) = H(t) - D(t),

hence

    D(t) = H(t) - W(t).

Both terms on the right are uniformly controlled:

* free heat is contractive and the restart datum has norm at most `A`;
* the selected physical extension is globally bounded by `2 * A`, and exact
  H³ deweighting plus coordinate projection are contractive.

Therefore every selected Duhamel coordinate satisfies

    ‖D_i(t)‖₂ ≤ 3 * A

throughout the positive canonical restart interval.

This is the fixed input norm needed by the midpoint fifth-radial heat estimate.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathOrderTwoSelectedVelocityDuhamelRawL2Bound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The quotient-safe free-heat raw Fourier coordinate is bounded by the
restart datum norm. -/
theorem norm_h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_le
    {ν t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (ht : 0 < t)
    (i : Fin 3) :
    ‖h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
        hν U₀ ht i‖
      ≤
    ‖U₀‖ := by

  have hRaw :
      ‖h3SpectralScalarRawFourierL2
          (h3SpectralScalarHeatApplyNN
            ν hν.le (NNReal.mk t ht.le) (U₀ i))‖
        ≤
      ‖h3SpectralScalarHeatApplyNN
          ν hν.le (NNReal.mk t ht.le) (U₀ i)‖ :=
    norm_h3SpectralScalarRawFourierL2_le
      (h3SpectralScalarHeatApplyNN
        ν hν.le (NNReal.mk t ht.le) (U₀ i))

  have hHeat :
      ‖h3SpectralScalarHeatApplyNN
          ν hν.le (NNReal.mk t ht.le) (U₀ i)‖
        ≤
      ‖U₀ i‖ :=
    norm_h3SpectralScalarHeatApplyNN_le
      ν hν.le (NNReal.mk t ht.le) (U₀ i)

  have hCoord :
      ‖U₀ i‖ ≤ ‖U₀‖ :=
    h3SpectralVelocity_coordinate_norm_le U₀ i

  unfold h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2

  exact hRaw.trans (hHeat.trans hCoord)

/-- Raw Fourier `L²` of one selected mild coordinate is bounded by the global
`2A` spectral bound. -/
theorem norm_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_le_twoA
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (t : ℝ)
    (i : Fin 3) :
    ‖h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
        hν U₀ hA hU₀ t i‖
      ≤
    2 * A := by

  let W : H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀ t

  have hRaw :
      ‖h3SpectralScalarRawFourierL2 (W i)‖
        ≤
      ‖W i‖ :=
    norm_h3SpectralScalarRawFourierL2_le (W i)

  have hCoord :
      ‖W i‖ ≤ ‖W‖ :=
    h3SpectralFinVector_coordinate_norm_le W i

  have hW :
      ‖W‖ ≤ 2 * A := by
    dsimp only [W]
    exact
      norm_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_le_twoA
        hν U₀ hA hU₀ t

  unfold h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
  rw [h3SpectralFinCoordinateRawFourierL2CLM_apply]

  exact hRaw.trans (hCoord.trans hW)

/-- The complete quotient-safe selected Duhamel raw Fourier coordinate has the
uniform bound `3A` at every strict positive restart time. -/
theorem norm_h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_le_threeA
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    ‖h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
        (t := t) hν U₀ hA hU₀ i‖
      ≤
    3 * A := by

  let H : H3FourierComplexL2 :=
    h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
      hν U₀ ht i

  let W : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
      hν U₀ hA hU₀ t i

  let D : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
      (t := t) hν U₀ hA hU₀ i

  have hMild :
      W = H - D := by
    dsimp only [W, H, D]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_eq_heat_add_duhamel
        hν U₀ hA hU₀ ht htR i

  have hSolve :
      D = H - W := by
    rw [hMild]
    abel

  have hH :
      ‖H‖ ≤ A := by
    dsimp only [H]
    exact
      (norm_h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_le
        hν U₀ ht i).trans hU₀

  have hW :
      ‖W‖ ≤ 2 * A := by
    dsimp only [W]
    exact
      norm_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_le_twoA
        hν U₀ hA hU₀ t i

  change ‖D‖ ≤ 3 * A
  rw [hSolve]

  calc
    ‖H - W‖
        ≤
      ‖H‖ + ‖W‖ :=
      norm_sub_le H W
    _ ≤
      A + 2 * A :=
      add_le_add hH hW
    _ =
      3 * A := by
      ring

/-- Path-specialized form for the canonical selected restart data. -/
theorem norm_h3PreterminalSelectedDuhamelRawFourierL2_le_threeE
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hq : q ∈ Set.Ioo
      (0 : ℝ)
      (h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (i : Fin 3) :
    ‖h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
        (t := q)
        (one_pos : (0 : ℝ) < 1)
        (h3PreterminalSelectedDecoderAnchorState
          hNS ht₀ hTail)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalSelectedDecoderAnchorState_le
          hNS ht₀ hE hTail)
        i‖
      ≤
    3 * E := by
  exact
    norm_h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_le_threeA
      (one_pos : (0 : ℝ) < 1)
      (h3PreterminalSelectedDecoderAnchorState
        hNS ht₀ hTail)
      (lt_of_lt_of_le zero_lt_one hE)
      (norm_h3PreterminalSelectedDecoderAnchorState_le
        hNS ht₀ hE hTail)
      hq.1 hq.2.le i

end

end Euclidean
end Bridge
end PrimeTensor
