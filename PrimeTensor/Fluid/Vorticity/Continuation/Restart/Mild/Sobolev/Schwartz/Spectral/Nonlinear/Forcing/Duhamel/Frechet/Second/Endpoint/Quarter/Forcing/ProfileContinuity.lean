import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.ProfileStateDifference
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.SelectedProfile

/-!
# Continuity of the selected second-moment source-time profile

For a strict retarded source time `s₀ < t`, decompose the scalar profile
variation into:

* changing the nonlinear state at the same lag `t-s`; and
* changing only the heat lag with the terminal state frozen at `W(s₀)`.

The first term tends to zero because the selected H³ path is continuous and
`ProfileStateDifference` is bilinear in the path difference.  The second tends
to zero by positive-lag frozen-profile continuity.

Hence the selected second-moment profile is continuous on the full open
retarded region `(-∞,t)`.  The endpoint `s=t` is intentionally excluded.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzQuarterForcingProfileContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The selected scalar second-moment profile is continuous at every strict
retarded source time. -/
theorem continuousAt_h3NonlinearForcingHeatSecondMomentProfile_selectedRestart_of_lt
    {ν A t s₀ : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs₀ : s₀ < t)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ContinuousAt
      (h3NonlinearForcingHeatSecondMomentProfile ν t W i)
      s₀ := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let c : ℝ → ℝ := fun s =>
    ((Real.sqrt (ν * ((t - s) / 3)))⁻¹) ^ 2

  let T : ℝ → ℝ := fun s =>
    h3NonlinearForcingHeatSecondMomentFrozenProfile
      ν (W s₀) i (t - s)

  let g : ℝ → ℝ := fun s =>
    c s *
        (h3NonlinearForcingL1Coefficient * ‖W s - W s₀‖ * ‖W s‖ +
          h3NonlinearForcingL1Coefficient * ‖W s₀‖ * ‖W s - W s₀‖)
      +
    |T s - T s₀|

  have hW :
      Continuous W := by
    dsimp only [W]
    exact
      continuous_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀

  have hs₀lag : 0 < t - s₀ :=
    sub_pos.mpr hs₀

  have hLag :
      ContinuousAt (fun s : ℝ => t - s) s₀ :=
    continuousAt_const.sub continuousAt_id

  have hScaledLag :
      ContinuousAt (fun s : ℝ => (t - s) / 3) s₀ :=
    hLag.div_const 3

  have hSqrt :
      ContinuousAt
        (fun s : ℝ => Real.sqrt (ν * ((t - s) / 3)))
        s₀ := by
    exact
      (continuousAt_const.mul hScaledLag).sqrt

  have hSqrtNe :
      Real.sqrt (ν * ((t - s₀) / 3)) ≠ 0 := by
    apply Real.sqrt_ne_zero'.mpr
    exact
      mul_pos hν (div_pos hs₀lag (by norm_num))

  have hc :
      ContinuousAt c s₀ := by
    dsimp only [c]
    exact
      (hSqrt.inv₀ hSqrtNe).pow 2

  have hTAt :
      ContinuousAt T s₀ := by
    dsimp only [T]
    exact
      (continuousAt_h3NonlinearForcingHeatSecondMomentFrozenProfile_lag
        hν hs₀lag (W s₀) i).comp hLag

  have hDiffNorm :
      ContinuousAt (fun s : ℝ => ‖W s - W s₀‖) s₀ :=
    (hW.continuousAt.sub continuousAt_const).norm

  have hWNorm :
      ContinuousAt (fun s : ℝ => ‖W s‖) s₀ :=
    hW.continuousAt.norm

  have hInner :
      ContinuousAt
        (fun s : ℝ =>
          h3NonlinearForcingL1Coefficient * ‖W s - W s₀‖ * ‖W s‖ +
            h3NonlinearForcingL1Coefficient * ‖W s₀‖ * ‖W s - W s₀‖)
        s₀ := by
    exact
      ((continuousAt_const.mul hDiffNorm).mul hWNorm).add
        ((continuousAt_const.mul continuousAt_const).mul hDiffNorm)

  have hgCont :
      ContinuousAt g s₀ := by
    dsimp only [g]
    exact
      (hc.mul hInner).add
        ((hTAt.sub continuousAt_const).abs)

  have hgZero :
      Tendsto g (𝓝 s₀) (𝓝 0) := by
    simpa [g] using hgCont.tendsto

  have hNear :
      ∀ᶠ s : ℝ in 𝓝 s₀, s < t :=
    eventually_lt_nhds hs₀

  have hUpper :
      ∀ᶠ s : ℝ in 𝓝 s₀,
        ‖h3NonlinearForcingHeatSecondMomentProfile ν t W i s -
            h3NonlinearForcingHeatSecondMomentProfile ν t W i s₀‖
          ≤
        g s := by
    filter_upwards [hNear] with s hs

    have hlag : 0 < t - s :=
      sub_pos.mpr hs

    have hState :=
      abs_h3NonlinearForcingHeatSecondMomentFrozenProfile_sub_le_stateDifference
        hν hlag (W s) (W s₀) i

    change
      ‖h3NonlinearForcingHeatSecondMomentFrozenProfile
            ν (W s) i (t - s) -
          h3NonlinearForcingHeatSecondMomentFrozenProfile
            ν (W s₀) i (t - s₀)‖
        ≤
      g s

    rw [Real.norm_eq_abs]

    calc
      |h3NonlinearForcingHeatSecondMomentFrozenProfile
            ν (W s) i (t - s) -
          h3NonlinearForcingHeatSecondMomentFrozenProfile
            ν (W s₀) i (t - s₀)|
          ≤
        |h3NonlinearForcingHeatSecondMomentFrozenProfile
              ν (W s) i (t - s) -
            h3NonlinearForcingHeatSecondMomentFrozenProfile
              ν (W s₀) i (t - s)|
          +
        |h3NonlinearForcingHeatSecondMomentFrozenProfile
              ν (W s₀) i (t - s) -
            h3NonlinearForcingHeatSecondMomentFrozenProfile
              ν (W s₀) i (t - s₀)| :=
        abs_sub_le _ _ _
      _ ≤
        c s *
            (h3NonlinearForcingL1Coefficient * ‖W s - W s₀‖ * ‖W s‖ +
              h3NonlinearForcingL1Coefficient * ‖W s₀‖ * ‖W s - W s₀‖)
          +
        |T s - T s₀| := by
        exact
          add_le_add_left
            hState
            |T s - T s₀|
      _ = g s := by
        rfl

  exact
    (tendsto_iff_norm_sub_tendsto_zero).2
      (squeeze_zero'
        (Eventually.of_forall fun s =>
          norm_nonneg
            (h3NonlinearForcingHeatSecondMomentProfile ν t W i s -
              h3NonlinearForcingHeatSecondMomentProfile ν t W i s₀))
        hUpper
        hgZero)

/-- The selected scalar second-moment profile is continuous on the entire
strict retarded region. -/
theorem continuousOn_h3NonlinearForcingHeatSecondMomentProfile_selectedRestart_Iio
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ContinuousOn
      (h3NonlinearForcingHeatSecondMomentProfile ν t W i)
      (Set.Iio t) := by
  dsimp only
  intro s hs
  exact
    (continuousAt_h3NonlinearForcingHeatSecondMomentProfile_selectedRestart_of_lt
      hν U₀ hA hU₀ hs i).continuousWithinAt

end

end Euclidean
end Bridge
end PrimeTensor
