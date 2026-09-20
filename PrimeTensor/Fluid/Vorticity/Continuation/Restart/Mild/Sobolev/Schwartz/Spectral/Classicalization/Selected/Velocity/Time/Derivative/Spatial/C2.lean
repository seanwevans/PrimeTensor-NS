import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Time.Derivative.PDE.Form
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Forcing.C2.Spatial.Regularity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Spatial.Regularity

/-!
# Classicalization: spatial C² regularity of the selected time derivative

The selected temporal PDE is

    ∂ₜu = ν tr(D²u) - N(u,u).

At positive restart time the selected velocity is spatially `C⁴`, so its
Hessian trace is `C²`.  The instantaneous nonlinear forcing is now `C²` by
`Selected.Forcing.C2.Spatial.Regularity`.  Therefore the actual ordinary time
derivative is spatially `C²`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedVelocityTimeDerivativeSpatialC2
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_timeDerivative_spatial_contDiff_two
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ContDiff ℝ 2
      (fun x : H3FourierPoint3 =>
        deriv
          (fun s : ℝ =>
            h3SpectralScalarC1Representative
              (W s i) x)
          t) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let f : H3FourierPoint3 → ℂ :=
    h3SpectralScalarC1Representative
      (W t i)

  have hSelectedC4 :
      ContDiff ℝ 4 f := by
    dsimp only [f, W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_contDiff_nat
        4 hν U₀ hA hU₀ ht htR.le i

  have hSecondTensor :
      ContDiff ℝ 2
        (iteratedFDeriv ℝ 2 f) := by
    exact
      hSelectedC4.iteratedFDeriv_right
        (m := 2)
        (i := 2)
        (by norm_num)

  have hDiagonal
      (j : Fin 3) :
      ContDiff ℝ 2
        (fun x : H3FourierPoint3 =>
          iteratedFDeriv ℝ 2 f x
            (fun _ : Fin 2 =>
              h3FourierAxisDirection
                (h3AxisOfFin3 j))) := by
    let m : Fin 2 → H3FourierPoint3 :=
      fun _ =>
        h3FourierAxisDirection
          (h3AxisOfFin3 j)

    let evalCLM :
        (H3FourierPoint3 [×2]→L[ℝ] ℂ) →L[ℝ] ℂ :=
      {
        toFun := fun T => T m
        map_add' := by
          intro T S
          rfl
        map_smul' := by
          intro c T
          rfl
        cont := continuous_eval_const m
      }

    change
      ContDiff ℝ 2
        (fun x : H3FourierPoint3 =>
          evalCLM
            (iteratedFDeriv ℝ 2 f x))

    exact
      hSecondTensor.continuousLinearMap_comp evalCLM

  have hTrace :
      ContDiff ℝ 2
        (fun x : H3FourierPoint3 =>
          ∑ j : Fin 3,
            iteratedFDeriv ℝ 2 f x
              (fun _ : Fin 2 =>
                h3FourierAxisDirection
                  (h3AxisOfFin3 j))) := by
    simpa using
      (ContDiff.sum
        (s := Finset.univ)
        (fun j _hj => hDiagonal j))

  have hViscTrace :
      ContDiff ℝ 2
        (fun x : H3FourierPoint3 =>
          (ν : ℂ) *
            (∑ j : Fin 3,
              iteratedFDeriv ℝ 2 f x
                (fun _ : Fin 2 =>
                  h3FourierAxisDirection
                    (h3AxisOfFin3 j)))) := by
    exact
      contDiff_const.mul hTrace

  have hForcing :
      ContDiff ℝ 2
        (h3RawFinLerayOuterProductDivergenceC0Representative
          (W t) (W t) i) := by
    dsimp only [W]
    exact
      h3RawFinLerayOuterProductDivergenceC0Representative_selectedRestart_contDiff_two
        hν U₀ hA hU₀ ht htR.le i

  have hRHS :
      ContDiff ℝ 2
        (fun x : H3FourierPoint3 =>
          (ν : ℂ) *
              (∑ j : Fin 3,
                iteratedFDeriv ℝ 2 f x
                  (fun _ : Fin 2 =>
                    h3FourierAxisDirection
                      (h3AxisOfFin3 j)))
            -
          h3RawFinLerayOuterProductDivergenceC0Representative
            (W t) (W t) i x) :=
    hViscTrace.sub hForcing

  have hEq :
      (fun x : H3FourierPoint3 =>
        deriv
          (fun s : ℝ =>
            h3SpectralScalarC1Representative
              (W s i) x)
          t)
        =
      (fun x : H3FourierPoint3 =>
        (ν : ℂ) *
            (∑ j : Fin 3,
              iteratedFDeriv ℝ 2 f x
                (fun _ : Fin 2 =>
                  h3FourierAxisDirection
                    (h3AxisOfFin3 j)))
          -
        h3RawFinLerayOuterProductDivergenceC0Representative
          (W t) (W t) i x) := by
    funext x
    dsimp only [f]
    simpa only [W] using
      deriv_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_eq_selectedHessianTrace_sub_forcing
        hν U₀ hA hU₀ ht htR i x

  rw [hEq]
  exact hRHS

end

end Euclidean
end Bridge
end PrimeTensor
