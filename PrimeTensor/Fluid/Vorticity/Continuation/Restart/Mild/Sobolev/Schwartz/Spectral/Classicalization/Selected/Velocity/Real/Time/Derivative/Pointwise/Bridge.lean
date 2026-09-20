import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Real.Time.Derivative.Spatial.C2

/-!
# Classicalization: pointwise real/complex temporal-derivative bridge

The real selected temporal derivative is already known to be spatially `C²`,
but the proof of that theorem keeps the real/complex derivative identification
local.

This file exports that identification explicitly.  At every strict positive
interior restart time, the ordinary time derivative of the real `Point3`
representative is exactly the real part of the ordinary time derivative of the
complex Fourier-carrier representative at the corresponding `toLp` point.

This is the temporal analogue of the existing real/complex spatial bridges.
It introduces no derivative commutation and no new estimate.  The next layer
can differentiate this equality twice in space and match the concrete ordered
second partial to the complex second-Fréchet temporal derivative.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedVelocityRealTimeDerivativePointwiseBridge
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- The real ordinary temporal derivative on `Point3` is the real part of the
complex ordinary temporal derivative at the corresponding Fourier carrier
point. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_timeDerivative_eq_re_complexTimeDerivative
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : Point3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    deriv
        (fun s : ℝ =>
          h3SpectralScalarRealC1RepresentativeOnPoint3
            (W s i) x)
        t
      =
    (deriv
        (fun s : ℝ =>
          h3SpectralScalarC1Representative
            (W s i)
            ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x))
        t).re := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let ξ : H3FourierPoint3 :=
    (WithLp.toLp 2 : Point3 → H3FourierPoint3) x

  let fC : ℝ → ℂ :=
    fun s : ℝ =>
      h3SpectralScalarC1Representative
        (W s i) ξ

  have hComplex :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_hasDerivAt_time
      hν U₀ hA hU₀ ht htR i ξ

  have hReal :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt
      t hComplex

  have hComplexDeriv := hComplex.deriv
  have hRealDeriv := hReal.deriv

  rw [← hComplexDeriv] at hRealDeriv

  change
    deriv
        (Complex.reCLM ∘ fC)
        t
      =
    Complex.reCLM (deriv fC t)
    at hRealDeriv

  have hPathEq :
      (Complex.reCLM ∘ fC)
        =
      (fun s : ℝ => (fC s).re) := by
    funext s
    simp only [
      Function.comp_apply,
      Complex.reCLM_apply
    ]

  rw [hPathEq] at hRealDeriv

  change
    deriv
        (fun s : ℝ => (fC s).re)
        t
      =
    (deriv fC t).re

  simpa only [Complex.reCLM_apply] using hRealDeriv

/-- Velocity-component form of the pointwise real/complex temporal derivative
bridge. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_component_timeDerivative_eq_re_complexTimeDerivative
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    deriv
        (fun s : ℝ =>
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
            hν U₀ hA hU₀ s x).component j)
        t
      =
    (deriv
        (fun s : ℝ =>
          h3SpectralScalarC1Representative
            (W s (h3ClassicalizationFinOfAxis j))
            ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x))
        t).re := by
  dsimp only

  change
    deriv
        (fun s : ℝ =>
          h3SpectralScalarRealC1RepresentativeOnPoint3
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν U₀ hA hU₀ s
              (h3ClassicalizationFinOfAxis j))
            x)
        t
      =
    (deriv
        (fun s : ℝ =>
          h3SpectralScalarC1Representative
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν U₀ hA hU₀ s
              (h3ClassicalizationFinOfAxis j))
            ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x))
        t).re

  exact
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_timeDerivative_eq_re_complexTimeDerivative
      hν U₀ hA hU₀ ht htR
      (h3ClassicalizationFinOfAxis j)
      x

end

end Euclidean
end Bridge
end PrimeTensor
