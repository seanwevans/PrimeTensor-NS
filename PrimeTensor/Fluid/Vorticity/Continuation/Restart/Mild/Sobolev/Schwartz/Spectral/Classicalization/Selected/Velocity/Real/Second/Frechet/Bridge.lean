import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Real.Time.Derivative.PDE.Bridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Cubic.Point3.Frechet.Continuity

/-!
# Classicalization: selected real Point3 second-Frechet bridge

The real temporal PDE bridge is now exact on `Point3`, but its Hessian trace is
still written using the complex Fourier-carrier second Fréchet derivative.

The cubic classicalization layer already contains the exact representation
transport through

* `Complex.reCLM` on the left, and
* the fixed `h3Point3ToFourierCLM` map on the right.

For the selected positive-time path, no cubic moment hypothesis is needed at
order two: `SpatialRegularity` already gives `C²` regularity of both the
complex representative and its real part.

This file therefore records the order-two analogue of the existing cubic
transport theorem:

    D² u_real(x)[m]
      =
    re (D² u_complex(toLp x)[toLp ∘ m]).

No coordinate axes are specialized here.  The next increment can separately
identify the transported standard `Point3` directions with
`h3FourierAxisDirection`, keeping that normalization issue isolated.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedVelocityRealSecondFrechetBridge
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- At every strict positive interior restart time, the second Fréchet
derivative of the real `Point3` representative is exactly the real part of the
second Fréchet derivative of the complex representative after transporting all
directions through the canonical `Point3 → H3FourierPoint3` linear map. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_secondFrechet_eval_eq_re
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : Point3)
    (m : Fin 2 → Point3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    iteratedFDeriv ℝ 2
        (h3SpectralScalarRealC1RepresentativeOnPoint3
          (W t i))
        x m
      =
    (iteratedFDeriv ℝ 2
        (h3SpectralScalarC1Representative
          (W t i))
        (h3Point3ToFourierCLM x)
        (fun k => h3Point3ToFourierCLM (m k))).re := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hComplexC2 :
      ContDiff ℝ 2
        (h3SpectralScalarC1Representative
          (W t i)) := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_contDiff_nat
        2 hν U₀ hA hU₀ ht htR.le i

  have hRealC2 :
      ContDiff ℝ 2
        (h3SpectralScalarRealC1Representative
          (W t i)) := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1Representative_contDiff_nat
        2 hν U₀ hA hU₀ ht htR.le i

  have hLeft :
      iteratedFDeriv ℝ 2
          (h3SpectralScalarRealC1Representative
            (W t i))
          (h3Point3ToFourierCLM x)
        =
      Complex.reCLM.compContinuousMultilinearMap
        (iteratedFDeriv ℝ 2
          (h3SpectralScalarC1Representative
            (W t i))
          (h3Point3ToFourierCLM x)) := by
    unfold h3SpectralScalarRealC1Representative

    change
      iteratedFDeriv ℝ 2
          (Complex.reCLM ∘
            h3SpectralScalarC1Representative
              (W t i))
          (h3Point3ToFourierCLM x)
        =
      Complex.reCLM.compContinuousMultilinearMap
        (iteratedFDeriv ℝ 2
          (h3SpectralScalarC1Representative
            (W t i))
          (h3Point3ToFourierCLM x))

    exact
      Complex.reCLM.iteratedFDeriv_comp_left
        hComplexC2.contDiffAt
        (by norm_num)

  rw [
    h3SpectralScalarRealC1RepresentativeOnPoint3_eq_comp
      (W t i)
  ]

  have hRight :=
    h3Point3ToFourierCLM.iteratedFDeriv_comp_right
      hRealC2
      x
      (i := 2)
      (by norm_num)

  rw [hRight]

  simp only [
    ContinuousMultilinearMap.compContinuousLinearMap_apply
  ]

  rw [hLeft]

  rfl

end

end Euclidean
end Bridge
end PrimeTensor
