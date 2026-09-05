import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.Second.Coordinate.Spatial.Derivative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.Selected.Second.Coordinate.Integrable
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Spatial.Derivative

/-!
# Selected mixed second spatial derivative of the nonlinear Duhamel integral

The fixed-lag mixed derivative identity and the selected full-time
integrability theorem now provide exactly the hypotheses required by Mathlib's
dominated parametric-integral theorem.  This file moves the second coordinate
derivative through the complete source-time integral.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped Topology Interval

noncomputable section

noncomputable local instance axisFintypeH3SchwartzQuarterForcingSelectedSecondCoordinateDuhamel
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Time integral of the selected mixed second-coordinate retarded path. -/
noncomputable def h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateDuhamel
    (ν t : ℝ)
    (U V : ℝ → H3SpectralFinVectorState)
    (i j k : Fin 3)
    (x : H3FourierPoint3) : ℂ :=
  ∫ s in (0 : ℝ)..t,
    h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
      ν t U V i j k x s

/-- Along the selected restart path, differentiating the integrated first
coordinate derivative in direction `k` gives the integrated mixed
second-coordinate derivative. -/
theorem h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeDuhamel_selectedRestart_hasDerivAt_secondCoordinate
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
    HasDerivAt
      (fun r : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeDuhamel
          ν t W W i j
          (x + r • h3FourierAxisDirection (h3AxisOfFin3 k)))
      (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateDuhamel
        ν t W W i j k x)
      0 := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let e : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 k)

  let F : ℝ → ℝ → ℂ :=
    fun r s =>
      h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
        ν t W W i j (x + r • e) s

  let F' : ℝ → ℝ → ℂ :=
    fun r s =>
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
        ν t W W i j k (x + r • e) s

  let bound : ℝ → ℝ :=
    h3SelectedSecondCoordinateDerivativePathMajorant
      ν A t hν U₀ hA hU₀ i

  have hWb :=
    h3SpectralFinHeatLerayMildSolutionPhysicalExtension_continuous_bounded
      hν
      (h3FinHeatLerayRestartRadius_pos ν hA).le
      U₀ hA hU₀
      (h3FinHeatLerayRestartRadius_smallness ν hA.le)

  have hWcont : Continuous W := by
    simpa only [
      W,
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
    ] using hWb.1

  have hWbound : ∀ s : ℝ, ‖W s‖ ≤ 2 * A := by
    intro s
    simpa only [
      W,
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
    ] using hWb.2 s

  have htwoA : 0 ≤ 2 * A := by
    positivity

  have hFInt :
      ∀ r : ℝ,
        Integrable
          (F r)
          (volume.restrict (Set.Ioo (0 : ℝ) t)) := by
    intro r
    change
      IntegrableOn
        (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
          ν t W W i j (x + r • e))
        (Set.Ioo (0 : ℝ) t)
        volume
    rw [← integrableOn_Ioc_iff_integrableOn_Ioo]
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le]
    exact
      h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath_intervalIntegrable_of_continuous
        hν ht.le htwoA htwoA W W hWcont hWcont
        (fun s _ => hWbound s)
        (fun s _ => hWbound s)
        i j (x + r • e)

  have hFMeas :
      ∀ᶠ r : ℝ in 𝓝 0,
        AEStronglyMeasurable
          (F r)
          (volume.restrict (Set.Ioo (0 : ℝ) t)) :=
    Filter.Eventually.of_forall fun r => (hFInt r).aestronglyMeasurable

  have hF0Int :
      Integrable
        (F 0)
        (volume.restrict (Set.Ioo (0 : ℝ) t)) :=
    hFInt 0

  have hF'0Int :
      Integrable
        (F' 0)
        (volume.restrict (Set.Ioo (0 : ℝ) t)) := by
    change
      IntegrableOn
        (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
          ν t W W i j k (x + 0 • e))
        (Set.Ioo (0 : ℝ) t)
        volume
    rw [← integrableOn_Ioc_iff_integrableOn_Ioo]
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le]
    simpa using
      (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath_selectedRestart_intervalIntegrable
        hν U₀ hA hU₀ ht htR i j k x)

  have hF'0Meas :
      AEStronglyMeasurable
        (F' 0)
        (volume.restrict (Set.Ioo (0 : ℝ) t)) :=
    hF'0Int.aestronglyMeasurable

  have hBoundInt :
      Integrable
        bound
        (volume.restrict (Set.Ioo (0 : ℝ) t)) := by
    change
      IntegrableOn
        (h3SelectedSecondCoordinateDerivativePathMajorant
          ν A t hν U₀ hA hU₀ i)
        (Set.Ioo (0 : ℝ) t)
        volume
    rw [← integrableOn_Ioc_iff_integrableOn_Ioo]
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le]
    exact
      h3SelectedSecondCoordinateDerivativePathMajorant_intervalIntegrable
        hν U₀ hA hU₀ ht htR i

  have hBound :
      ∀ᵐ s : ℝ ∂(volume.restrict (Set.Ioo (0 : ℝ) t)),
        ∀ r ∈ (Set.univ : Set ℝ),
          ‖F' r s‖ ≤ bound s := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards with s hs
    intro r hr
    dsimp only [F', bound]
    exact
      norm_h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath_selectedRestart_le_majorant
        hν U₀ hA hU₀ hs.2 i j k (x + r • e)

  have hDiff :
      ∀ᵐ s : ℝ ∂(volume.restrict (Set.Ioo (0 : ℝ) t)),
        ∀ r ∈ (Set.univ : Set ℝ),
          HasDerivAt (F · s) (F' r s) r := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards with s hs
    intro r hr
    dsimp only [F, F']
    unfold h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
    unfold h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
    simpa [e] using
      (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_hasDerivAt_secondCoordinate_at
        hν (sub_pos.mpr hs.2) (W s) (W s) i j k x r)

  have hIntegral :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (s := (Set.univ : Set ℝ))
      (F := F)
      (F' := F')
      (x₀ := (0 : ℝ))
      (bound := bound)
      (μ := volume.restrict (Set.Ioo (0 : ℝ) t))
      Filter.univ_mem
      hFMeas
      hF0Int
      hF'0Meas
      hBound
      hBoundInt
      hDiff).2

  have hValueIntegral (r : ℝ) :
      (∫ s : ℝ,
          F r s
          ∂(volume.restrict (Set.Ioo (0 : ℝ) t)))
        =
      ∫ s in (0 : ℝ)..t,
        h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
          ν t W W i j (x + r • e) s := by
    rw [intervalIntegral.integral_of_le ht.le]
    rw [← restrict_Ioo_eq_restrict_Ioc]

  have hDerivativeIntegral :
      (∫ s : ℝ,
          F' 0 s
          ∂(volume.restrict (Set.Ioo (0 : ℝ) t)))
        =
      ∫ s in (0 : ℝ)..t,
        h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
          ν t W W i j k x s := by
    rw [intervalIntegral.integral_of_le ht.le]
    rw [← restrict_Ioo_eq_restrict_Ioc]
    simp [F', e]

  change
    HasDerivAt
      (fun r : ℝ =>
        ∫ s in (0 : ℝ)..t,
          h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
            ν t W W i j (x + r • e) s)
      (∫ s in (0 : ℝ)..t,
        h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
          ν t W W i j k x s)
      0

  have hValueFunction :
      (fun r : ℝ =>
        ∫ s in (0 : ℝ)..t,
          h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
            ν t W W i j (x + r • e) s)
        =
      (fun r : ℝ =>
        ∫ s : ℝ,
          F r s
          ∂(volume.restrict (Set.Ioo (0 : ℝ) t))) := by
    funext r
    exact (hValueIntegral r).symm

  rw [hValueFunction]
  rw [← hDerivativeIntegral]
  exact hIntegral

end
end Euclidean
end Bridge
end PrimeTensor
