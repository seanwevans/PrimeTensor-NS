import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Forcing.Real.Point3.Gradient.Time.Continuity

/-!
# Classicalization: directional forcing-gradient time continuity

The real `Point3` Fréchet derivative of the selected instantaneous forcing is
now continuous in time.  The mixed-regularity frontier is expressed through
coordinate partial derivatives rather than operator-valued Fréchet
derivatives.

This file performs the first harmless reduction: evaluate the continuous
operator-valued derivative at a fixed spatial direction.  In particular we
record the canonical coordinate direction attached to each project axis and
obtain time continuity of the forcing derivative in that direction.

The next layer can identify this directional Fréchet derivative with
`spatial3.d`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedForcingDirectionalGradientTimeContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- The standard coordinate direction corresponding to one spatial axis. -/
noncomputable def h3CoordinateDirection
    (a : PrimeTensor.Axis Depth.three) :
    Point3 := by
  classical
  exact fun b => if b = a then 1 else 0

@[simp]
theorem h3CoordinateDirection_same
    (a : PrimeTensor.Axis Depth.three) :
    h3CoordinateDirection a a = 1 := by
  classical
  simp [h3CoordinateDirection]

theorem h3CoordinateDirection_other
    {a b : PrimeTensor.Axis Depth.three}
    (hba : b ≠ a) :
    h3CoordinateDirection a b = 0 := by
  classical
  simp [h3CoordinateDirection, hba]

/-- Evaluating the real selected forcing Fréchet derivative at any fixed
`Point3` direction preserves its time continuity. -/
theorem h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_selectedRestart_real_fderiv_apply_continuousAt_time
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x v : Point3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ContinuousAt
      (fun r : ℝ =>
        (fderiv ℝ
          (fun y : Point3 =>
            (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              (W r) (W r) i y).re)
          x) v)
      s := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hOperator :
      ContinuousAt
        (fun r : ℝ =>
          fderiv ℝ
            (fun y : Point3 =>
              (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
                (W r) (W r) i y).re)
            x)
        s := by
    dsimp only [W]
    exact
      h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_selectedRestart_real_fderiv_continuousAt_time
        hν U₀ hA hU₀ hs hsR i x

  exact
    ((ContinuousLinearMap.apply ℝ ℝ v).continuous.continuousAt).comp
      hOperator

/-- Coordinate-direction specialization of the selected real forcing gradient
time-continuity theorem. -/
theorem h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_selectedRestart_real_coordinateDerivative_continuousAt_time
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : Point3)
    (a : PrimeTensor.Axis Depth.three) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ContinuousAt
      (fun r : ℝ =>
        (fderiv ℝ
          (fun y : Point3 =>
            (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              (W r) (W r) i y).re)
          x)
          (h3CoordinateDirection a))
      s := by
  exact
    h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_selectedRestart_real_fderiv_apply_continuousAt_time
      hν U₀ hA hU₀ hs hsR i x
      (h3CoordinateDirection a)

end

end Euclidean
end Bridge
end PrimeTensor
