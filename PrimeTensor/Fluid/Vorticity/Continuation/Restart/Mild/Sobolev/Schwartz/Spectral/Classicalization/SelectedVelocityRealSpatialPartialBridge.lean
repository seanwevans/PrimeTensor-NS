import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedVelocityRealFirstFrechetBridge
import PrimeTensor.Bridge.Euclidean.Partials.Mixed

/-!
# Classicalization: selected real spatial-partial / first-Fréchet bridge

The order-one real/complex Fréchet transport is now available.  This file makes
the final Euclidean identification needed before differentiating that first
spatial jet in time.

For every strict positive interior restart time,

    ∂ₐ uᵢ(t,x)
      =
    Re (D uᵢ_complex(t,toLp x)[eₐ]).

The proof has only two ingredients:

* `SpatialC1.partialDeriv_eq_fderiv_axisDirection`, identifying the project's
  concrete coordinate derivative with first Fréchet evaluation;
* the selected real first-Fréchet bridge, reduced from `iteratedFDeriv ℝ 1`
  to `fderiv` by `iteratedFDeriv_one_apply`.

No time differentiation, PDE identity, estimate, or mixed-partial commutation
is used here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedVelocityRealSpatialPartialBridge
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- The concrete real spatial partial of a selected scalar coordinate is
exactly the real part of the corresponding complex first-Fréchet coordinate. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_spatial_d_eq_re_firstFrechet
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : Point3)
    (a : PrimeTensor.Axis Depth.three) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    spatial3.d
        a
        (h3SpectralScalarRealC1RepresentativeOnPoint3
          (W t i))
        x
      =
    ((fderiv ℝ
        (h3SpectralScalarC1Representative
          (W t i))
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x))
      (h3FourierAxisDirection a)).re := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let f : ScalarField3 :=
    h3SpectralScalarRealC1RepresentativeOnPoint3
      (W t i)

  have hfC1 : SpatialC1 f := by
    unfold SpatialC1
    dsimp only [f, W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_contDiff_nat
        1 hν U₀ hA hU₀ ht htR.le i

  have hPartial :
      spatial3.d a f x
        =
      (fderiv ℝ f x) (axisDirection a) := by
    exact
      hfC1.partialDeriv_eq_fderiv_axisDirection
        x a

  have hBridge :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_firstFrechet_axisDirection_eq_re
      hν U₀ hA hU₀ ht htR i x a

  have hBridge' :
      (fderiv ℝ f x) (axisDirection a)
        =
      ((fderiv ℝ
          (h3SpectralScalarC1Representative
            (W t i))
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x))
        (h3FourierAxisDirection a)).re := by
    simpa only [
      f,
      W,
      iteratedFDeriv_one_apply
    ] using hBridge

  change
    spatial3.d a f x
      =
    ((fderiv ℝ
        (h3SpectralScalarC1Representative
          (W t i))
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x))
      (h3FourierAxisDirection a)).re

  exact hPartial.trans hBridge'

end

end Euclidean
end Bridge
end PrimeTensor
