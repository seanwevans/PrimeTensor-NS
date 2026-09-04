import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedCanonicalFirstFrechetDerivTimeContinuity

/-!
# Classicalization: canonical first-Fréchet temporal derivative regularity

The explicit canonical selected reconstruction is now known, at every strict
positive interior restart time, to have

* an ordinary time derivative after one fixed spatial Fréchet-coordinate
  evaluation; and
* a time-continuous actual derivative.

This file packages those pointwise statements over the whole open canonical
restart interval `(0,R)` as

    DifferentiableOn ℝ f (Ioo 0 R)
      ∧
    ContinuousOn (deriv f) (Ioo 0 R),

where

    f(r) = D_a uᶜ_i(r,x)

and `uᶜ` is the explicit canonical inverse-Fourier reconstruction.

No bridge back to the arbitrary H³ representative is needed anymore: both
ingredients are already stated directly for the canonical reconstruction.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedCanonicalFirstFrechetTemporalDerivativeRegularity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- On the complete strict canonical restart interval, every fixed coordinate
evaluation of the first spatial Fréchet derivative of the explicit canonical
selected reconstruction is differentiable in time and its actual ordinary
derivative is continuous. -/
theorem h3SpectralFinHeatLerayRestartRadiusCanonicalC1Representative_fderiv_coordinate_temporalDerivativeRegularity
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i a : Fin 3)
    (x : H3FourierPoint3) :
    let ea : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 a)
    let f : ℝ → ℂ :=
      fun r : ℝ =>
        (fderiv ℝ
            (h3SpectralFinHeatLerayRestartRadiusCanonicalC1Representative
              hν U₀ hA hU₀ r i)
            x) ea
    let I : Set ℝ :=
      Set.Ioo
        0
        (h3FinHeatLerayRestartRadius ν A)
    DifferentiableOn ℝ f I
      ∧
    ContinuousOn (deriv f) I := by
  dsimp only

  let R : ℝ :=
    h3FinHeatLerayRestartRadius ν A

  let ea : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 a)

  let f : ℝ → ℂ :=
    fun r : ℝ =>
      (fderiv ℝ
          (h3SpectralFinHeatLerayRestartRadiusCanonicalC1Representative
            hν U₀ hA hU₀ r i)
          x) ea

  let I : Set ℝ :=
    Set.Ioo 0 R

  constructor

  · intro s hs

    have hDeriv :=
      h3SpectralFinHeatLerayRestartRadiusCanonicalC1Representative_fderiv_coordinate_hasDerivAt_time
        hν U₀ hA hU₀
        hs.1
        (by
          simpa only [I, R] using hs.2)
        i a x

    dsimp only at hDeriv

    have hDifferentiable :
        DifferentiableAt ℝ f s := by
      dsimp only [f, ea]
      exact hDeriv.differentiableAt

    exact hDifferentiable.differentiableWithinAt

  · intro s hs

    have hContinuous :
        ContinuousAt
          (deriv f)
          s := by
      dsimp only [f, ea]
      exact
        deriv_h3SpectralFinHeatLerayRestartRadiusCanonicalC1Representative_fderiv_coordinate_continuousAt_time
          hν U₀ hA hU₀
          hs.1
          (by
            simpa only [I, R] using hs.2)
          i a x

    exact hContinuous.continuousWithinAt

end

end Euclidean
end Bridge
end PrimeTensor
