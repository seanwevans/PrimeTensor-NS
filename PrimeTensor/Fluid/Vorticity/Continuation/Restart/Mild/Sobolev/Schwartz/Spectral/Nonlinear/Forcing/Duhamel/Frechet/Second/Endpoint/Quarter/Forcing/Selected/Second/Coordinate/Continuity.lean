import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.Second.Coordinate.State.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.Selected.Second.Coordinate.Path

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Interval

noncomputable section

noncomputable local instance axisFintypeH3SchwartzQuarterForcingSelectedSecondCoordinateContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

theorem continuousAt_h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath_selectedRestart
    {ν A t s₀ : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs₀ : s₀ < t)
    (i j k : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ContinuousAt
      (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
        ν t W W i j k x)
      s₀ := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let c : ℝ → ℝ :=
    fun s =>
      (2 * Real.pi) ^ 2 *
        ((Real.sqrt (ν * ((t - s) / 3)))⁻¹) ^ 2

  let q : ℝ → ℝ :=
    fun s =>
      h3NonlinearForcingL1Coefficient * ‖W s - W s₀‖ * ‖W s‖ +
        h3NonlinearForcingL1Coefficient * ‖W s₀‖ * ‖W s - W s₀‖

  let T : ℝ → ℂ :=
    fun s =>
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
        ν (t - s) (W s₀) (W s₀) i j k x

  let g : ℝ → ℝ :=
    fun s => c s * q s + ‖T s - T s₀‖

  have hWcont : Continuous W := by
    dsimp only [W]
    exact
      continuous_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀

  have hlag₀ : 0 < t - s₀ :=
    sub_pos.mpr hs₀

  have hLag :
      ContinuousAt (fun s : ℝ => t - s) s₀ :=
    continuousAt_const.sub continuousAt_id

  have hScaled :
      ContinuousAt (fun s : ℝ => (t - s) / 3) s₀ :=
    hLag.div_const 3

  have hSqrt :
      ContinuousAt
        (fun s : ℝ => Real.sqrt (ν * ((t - s) / 3)))
        s₀ := by
    exact (continuousAt_const.mul hScaled).sqrt

  have hSqrtNe :
      Real.sqrt (ν * ((t - s₀) / 3)) ≠ 0 := by
    apply Real.sqrt_ne_zero'.mpr
    exact mul_pos hν (div_pos hlag₀ (by norm_num))

  have hc : ContinuousAt c s₀ := by
    dsimp only [c]
    exact
      continuousAt_const.mul
        ((hSqrt.inv₀ hSqrtNe).pow 2)

  have hDiffNorm :
      ContinuousAt (fun s : ℝ => ‖W s - W s₀‖) s₀ :=
    (hWcont.continuousAt.sub continuousAt_const).norm

  have hWNorm :
      ContinuousAt (fun s : ℝ => ‖W s‖) s₀ :=
    hWcont.continuousAt.norm

  have hq : ContinuousAt q s₀ := by
    dsimp only [q]
    exact
      (((continuousAt_const.mul hDiffNorm).mul hWNorm).add
        ((continuousAt_const.mul continuousAt_const).mul hDiffNorm))

  have hT : ContinuousAt T s₀ := by
    dsimp only [T]
    exact
      continuousAt_h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative_retarded_frozen
        hν hs₀ (W s₀) (W s₀) i j k x

  have hg : ContinuousAt g s₀ := by
    dsimp only [g]
    exact
      (hc.mul hq).add
        (hT.sub continuousAt_const).norm

  have hgZero :
      Tendsto g (𝓝 s₀) (𝓝 0) := by
    simpa [g, q] using hg.tendsto

  have hNear :
      ∀ᶠ s : ℝ in 𝓝 s₀, s < t :=
    eventually_lt_nhds hs₀

  have hUpper :
      ∀ᶠ s : ℝ in 𝓝 s₀,
        ‖h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
              ν t W W i j k x s -
            h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
              ν t W W i j k x s₀‖
          ≤ g s := by
    filter_upwards [hNear] with s hs
    have hlag : 0 < t - s :=
      sub_pos.mpr hs

    have hState0 :=
      norm_h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative_diagonal_sub_le
        hν hlag (W s) (W s₀) i j k x

    have hState :
        ‖h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
              ν (t - s) (W s) (W s) i j k x -
            h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
              ν (t - s) (W s₀) (W s₀) i j k x‖
          ≤
        c s * q s := by
      simpa only [c, q] using hState0

    change
      ‖h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
              ν (t - s) (W s) (W s) i j k x -
            h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
              ν (t - s₀) (W s₀) (W s₀) i j k x‖
        ≤ g s

    calc
      ‖h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
              ν (t - s) (W s) (W s) i j k x -
            h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
              ν (t - s₀) (W s₀) (W s₀) i j k x‖
          =
        ‖(h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
              ν (t - s) (W s) (W s) i j k x -
            h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
              ν (t - s) (W s₀) (W s₀) i j k x) +
          (T s - T s₀)‖ := by
        dsimp only [T]
        congr 1
        abel
      _ ≤
        ‖h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
              ν (t - s) (W s) (W s) i j k x -
            h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
              ν (t - s) (W s₀) (W s₀) i j k x‖ +
          ‖T s - T s₀‖ :=
        norm_add_le _ _
      _ ≤
        c s * q s + ‖T s - T s₀‖ := by
        exact add_le_add hState (le_refl _)
      _ = g s := by
        rfl

  exact
    (tendsto_iff_norm_sub_tendsto_zero).2
      (squeeze_zero'
        (Filter.Eventually.of_forall fun s =>
          norm_nonneg
            (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
                ν t W W i j k x s -
              h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
                ν t W W i j k x s₀))
        hUpper
        hgZero)

theorem continuousOn_h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath_selectedRestart_Ioo
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i j k : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ContinuousOn
      (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
        ν t W W i j k x)
      (Set.Ioo (0 : ℝ) t) := by
  dsimp only
  intro s hs
  exact
    (continuousAt_h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath_selectedRestart
      hν U₀ hA hU₀ hs.2 i j k x).continuousWithinAt

end
end Euclidean
end Bridge
end PrimeTensor
