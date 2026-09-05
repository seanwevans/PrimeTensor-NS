import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.Selected.Second.Coordinate.Continuity

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Interval

noncomputable section

noncomputable local instance axisFintypeH3SchwartzQuarterForcingSelectedSecondCoordinateIntegrable
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

theorem h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath_selectedRestart_integrableOn_Ioo
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i j k : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    IntegrableOn
      (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
        ν t W W i j k x)
      (Set.Ioo (0 : ℝ) t)
      volume := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let M : ℝ → ℝ :=
    h3SelectedSecondCoordinateDerivativePathMajorant
      ν A t hν U₀ hA hU₀ i

  have hMInterval :
      IntervalIntegrable M volume 0 t := by
    dsimp only [M]
    exact
      h3SelectedSecondCoordinateDerivativePathMajorant_intervalIntegrable
        hν U₀ hA hU₀ ht htR i

  have hMIoo :
      IntegrableOn M (Set.Ioo (0 : ℝ) t) volume := by
    rw [
      ← integrableOn_Ioc_iff_integrableOn_Ioo,
      ← intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le
    ]
    exact hMInterval

  have hCont :
      ContinuousOn
        (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
          ν t W W i j k x)
        (Set.Ioo (0 : ℝ) t) := by
    dsimp only [W]
    exact
      continuousOn_h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath_selectedRestart_Ioo
        hν U₀ hA hU₀ i j k x

  have hMeas :
      AEStronglyMeasurable
        (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
          ν t W W i j k x)
        (volume.restrict (Set.Ioo (0 : ℝ) t)) :=
    hCont.aestronglyMeasurable measurableSet_Ioo

  refine hMIoo.mono' hMeas ?_
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards with s hs

  dsimp only [M, W]
  exact
    norm_h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath_selectedRestart_le_majorant
      hν U₀ hA hU₀ hs.2 i j k x

theorem h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath_selectedRestart_intervalIntegrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i j k : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    IntervalIntegrable
      (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
        ν t W W i j k x)
      volume
      0
      t := by
  dsimp only
  rw [
    intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le,
    integrableOn_Ioc_iff_integrableOn_Ioo
  ]
  exact
    h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath_selectedRestart_integrableOn_Ioo
      hν U₀ hA hU₀ ht htR i j k x

end
end Euclidean
end Bridge
end PrimeTensor
