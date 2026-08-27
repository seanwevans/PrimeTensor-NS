import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.SecondCoordinate
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.SelectedProfileTimeIntegrable

/-!
# Selected mixed second-coordinate retarded path

The selected second-moment source-time profile is now genuinely
interval-integrable.  `Forcing.SecondCoordinate` shows that every mixed
coordinate second derivative of the positive-lag kernel is pointwise bounded
by `(2π)^2` times that radial profile.

This file packages the actual selected retarded mixed-derivative path and its
integrable scalar majorant.  The remaining step before differentiating the
Duhamel integral twice is now a measurability/continuity statement for this
complex-valued path itself; the endpoint size and time-integrability problem
has been completely discharged.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval

noncomputable section

noncomputable local instance axisFintypeH3SchwartzQuarterForcingSelectedSecondCoordinatePath
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Mixed coordinate second derivative of the retarded nonlinear forcing
kernel along arbitrary spectral paths. -/
noncomputable def h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
    (ν t : ℝ)
    (U V : ℝ → H3SpectralFinVectorState)
    (i j k : Fin 3)
    (x : H3FourierPoint3)
    (s : ℝ) : ℂ :=
  h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
    ν (t - s) (U s) (V s) i j k x

/-- On every strict selected retarded slice, the mixed second-coordinate path
is bounded by `(2π)^2` times the named second-moment profile. -/
theorem norm_h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath_selectedRestart_le_profile
    {ν A t s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : s < t)
    (i j k : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ‖h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
        ν t W W i j k x s‖
      ≤
    (2 * Real.pi) ^ 2 *
      h3NonlinearForcingHeatSecondMomentProfile ν t W i s := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hτ : 0 < t - s :=
    sub_pos.mpr hs

  have hBound :=
    norm_h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative_le_secondMoment
      hν hτ (W s) (W s) i j k x

  simpa only [
    h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath,
    h3NonlinearForcingHeatSecondMomentProfile,
    h3RawFinLerayOuterProductDivergenceHeatRepresentative
  ] using hBound

/-- Canonical scalar majorant for every selected mixed second-coordinate
retarded path. -/
noncomputable def h3SelectedSecondCoordinateDerivativePathMajorant
    (ν A t : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (s : ℝ) : ℝ :=
  (2 * Real.pi) ^ 2 *
    h3NonlinearForcingHeatSecondMomentProfile
      ν t
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀)
      i s

/-- The selected mixed-second-derivative scalar majorant is genuinely
interval-integrable on the complete Duhamel source-time interval. -/
theorem h3SelectedSecondCoordinateDerivativePathMajorant_intervalIntegrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    IntervalIntegrable
      (h3SelectedSecondCoordinateDerivativePathMajorant
        ν A t hν U₀ hA hU₀ i)
      volume
      0
      t := by
  unfold h3SelectedSecondCoordinateDerivativePathMajorant

  exact
    (h3NonlinearForcingHeatSecondMomentProfile_selectedRestart_intervalIntegrable
      hν U₀ hA hU₀ ht htR i).const_mul ((2 * Real.pi) ^ 2)

/-- Every strict slice is dominated by the canonical integrable selected
mixed-second-derivative majorant. -/
theorem norm_h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath_selectedRestart_le_majorant
    {ν A t s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : s < t)
    (i j k : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ‖h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
        ν t W W i j k x s‖
      ≤
    h3SelectedSecondCoordinateDerivativePathMajorant
      ν A t hν U₀ hA hU₀ i s := by
  dsimp only
  exact
    norm_h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath_selectedRestart_le_profile
      hν U₀ hA hU₀ hs i j k x

end

end Euclidean
end Bridge
end PrimeTensor
