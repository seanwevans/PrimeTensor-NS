import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Forcing.Directional.Gradient.Time.Continuity
import Mathlib.Analysis.Calculus.Deriv.Pi

/-!
# Classicalization: selected forcing spatial partial time continuity

The previous layer proves time continuity of the real forcing Fréchet
derivative evaluated on the canonical coordinate direction.

The mixed-regularity frontier is written with the project's concrete
coordinate derivative `spatial3.d`.  This file identifies that coordinate
derivative with evaluation of the Fréchet derivative on the corresponding
coordinate direction.

The key observation is already present in Mathlib:

    HasDerivAt (Function.update x a) (Pi.single a 1) t.

The project's coordinate line is exactly `Function.update x a`, and
`h3CoordinateDirection a` is exactly `Pi.single a 1`.  Therefore the ordinary
chain rule gives

    spatial3.d a f x = (fderiv ℝ f x) (h3CoordinateDirection a)

whenever `f` is differentiable at `x`.

Applying this identity on a positive restart-time neighborhood transports the
previous directional continuity theorem to the exact `spatial3.d` forcing term
needed by the mixed spacetime argument.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedForcingSpatialPartialTimeContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- For a differentiable real scalar field on `Point3`, the concrete project
partial derivative is evaluation of the Fréchet derivative on the canonical
coordinate direction. -/
theorem spatial3_d_eq_fderiv_apply_h3CoordinateDirection
    (f : ScalarField3)
    (x : Point3)
    (a : PrimeTensor.Axis Depth.three)
    (hf : DifferentiableAt ℝ f x) :
    spatial3.d a f x
      =
    (fderiv ℝ f x) (h3CoordinateDirection a) := by
  classical

  have hLine :
      HasDerivAt
        (fun t : ℝ => coordinateLine x a t)
        (h3CoordinateDirection a)
        (x a) := by
    have hUpdate :=
      hasDerivAt_update x a (x a)

    have hDirection :
        (Pi.single a (1 : ℝ) : Point3)
          =
        h3CoordinateDirection a := by
      funext b
      by_cases hba : b = a
      · subst b
        simp [h3CoordinateDirection]
      · rw [Pi.single_eq_of_ne hba]
        exact (h3CoordinateDirection_other hba).symm

    simpa only [coordinateLine, hDirection] using hUpdate

  have hfAtLine :
      HasFDerivAt
        f
        (fderiv ℝ f x)
        (coordinateLine x a (x a)) := by
    simpa only [coordinateLine_at_base] using hf.hasFDerivAt

  have hComp :
      HasDerivAt
        (fun t : ℝ => f (coordinateLine x a t))
        ((fderiv ℝ f x) (h3CoordinateDirection a))
        (x a) :=
    hfAtLine.comp_hasDerivAt (x a) hLine

  change
    partialDeriv a f x
      =
    (fderiv ℝ f x) (h3CoordinateDirection a)

  unfold partialDeriv
  exact hComp.deriv

/-- Along the selected restart path, the exact project coordinate partial of
the real instantaneous forcing is time-continuous at every strict positive
interior restart time. -/
theorem h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_selectedRestart_real_spatial_d_continuousAt_time
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
        spatial3.d
          a
          (fun y : Point3 =>
            (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              (W r) (W r) i y).re)
          x)
      s := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let F : ℝ → ScalarField3 :=
    fun r y =>
      (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
        (W r) (W r) i y).re

  have hDirectional :
      ContinuousAt
        (fun r : ℝ =>
          (fderiv ℝ (F r) x)
            (h3CoordinateDirection a))
        s := by
    dsimp only [F, W]
    exact
      h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_selectedRestart_real_coordinateDerivative_continuousAt_time
        hν U₀ hA hU₀ hs hsR i x a

  have hInterval :
      Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν A)
        ∈ 𝓝 s :=
    Ioo_mem_nhds hs hsR

  have hEq :
      (fun r : ℝ =>
        spatial3.d a (F r) x)
        =ᶠ[𝓝 s]
      (fun r : ℝ =>
        (fderiv ℝ (F r) x)
          (h3CoordinateDirection a)) := by
    filter_upwards [hInterval] with r hr

    have hC1 :
        ContDiff ℝ 1 (F r) := by
      dsimp only [F, W]
      exact
        h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_selectedRestart_real_contDiff_one
          hν U₀ hA hU₀ hr.1 hr.2.le i

    have hDiff :
        DifferentiableAt ℝ (F r) x := by
      exact
        (hC1.differentiable (by norm_num)).differentiableAt

    exact
      spatial3_d_eq_fderiv_apply_h3CoordinateDirection
        (F r) x a hDiff

  exact
    hDirectional.congr_of_eventuallyEq hEq

end

end Euclidean
end Bridge
end PrimeTensor
