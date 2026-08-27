import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.SelectedSecondCoordinateDuhamel

/-!
# Spatial continuity of the selected mixed second Duhamel derivative

At each positive lag the mixed second-coordinate representative is the inverse
Fourier transform of an L¹ amplitude, hence is continuous in space.  The
selected endpoint branch supplies an integrable source-time majorant independent
of the spatial point.  Dominated continuity therefore survives the full
Duhamel time integration.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped ENNReal NNReal Topology Interval RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzQuarterForcingSelectedSecondCoordinateDuhamelContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Positive-lag mixed second-coordinate representatives are continuous in
space. -/
theorem h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative_continuous_space
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i j k : Fin 3) :
    Continuous
      (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
        ν τ U V i j k) := by
  have hInnerNegContinuous :
      Continuous
        (fun p : H3FourierPoint3 × H3FourierPoint3 =>
          ((-(innerₗ H3FourierPoint3)) p.1) p.2) := by
    change Continuous
      (fun p : H3FourierPoint3 × H3FourierPoint3 =>
        -inner ℝ p.1 p.2)
    exact
      (continuous_inner (𝕜 := ℝ) (E := H3FourierPoint3)).neg

  unfold h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
  change Continuous
    (VectorFourier.fourierIntegral
      Real.fourierChar
      (volume : Measure H3FourierPoint3)
      (-(innerₗ H3FourierPoint3))
      (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude
        ν τ U V i j k))

  exact
    VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar
      hInnerNegContinuous
      (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude_integrable
        hν hτ U V i j k)

/-- Along the selected restart path, the integrated mixed second-coordinate
derivative is continuous in the spatial point. -/
theorem h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateDuhamel_selectedRestart_continuous
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i j k : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    Continuous
      (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateDuhamel
        ν t W W i j k) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  unfold h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateDuhamel

  apply intervalIntegral.continuous_of_dominated_interval
    (F := fun x : H3FourierPoint3 =>
      fun s : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
          ν t W W i j k x s)
    (bound :=
      h3SelectedSecondCoordinateDerivativePathMajorant
        ν A t hν U₀ hA hU₀ i)

  · intro x
    exact
      (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath_selectedRestart_intervalIntegrable
        hν U₀ hA hU₀ ht htR i j k x).def'.aestronglyMeasurable

  · intro x
    filter_upwards [(volume : Measure ℝ).ae_ne t] with s hst hs
    have hsIoc : s ∈ Set.Ioc (0 : ℝ) t := by
      simpa only [uIoc_of_le ht.le] using hs
    have hsIoo : s ∈ Set.Ioo (0 : ℝ) t :=
      ⟨hsIoc.1, lt_of_le_of_ne hsIoc.2 hst⟩
    exact
      norm_h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath_selectedRestart_le_majorant
        hν U₀ hA hU₀ hsIoo.2 i j k x

  · exact
      h3SelectedSecondCoordinateDerivativePathMajorant_intervalIntegrable
        hν U₀ hA hU₀ ht htR i

  · filter_upwards [(volume : Measure ℝ).ae_ne t] with s hst hs
    have hsIoc : s ∈ Set.Ioc (0 : ℝ) t := by
      simpa only [uIoc_of_le ht.le] using hs
    have hsIoo : s ∈ Set.Ioo (0 : ℝ) t :=
      ⟨hsIoc.1, lt_of_le_of_ne hsIoc.2 hst⟩
    unfold h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
    exact
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative_continuous_space
        hν (sub_pos.mpr hsIoo.2) (W s) (W s) i j k

end
end Euclidean
end Bridge
end PrimeTensor
