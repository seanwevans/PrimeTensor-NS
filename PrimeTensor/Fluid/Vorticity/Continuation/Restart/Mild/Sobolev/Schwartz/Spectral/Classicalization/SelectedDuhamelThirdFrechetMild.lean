import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedDuhamelFirstFrechetMild
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SpatialRegularity

/-!
# Classicalization: selected Duhamel third-Fréchet mild identity

The selected pointwise mild equation is an equality of spatial functions

    Selected = Heat - Duhamel.

Rearranging it gives

    Duhamel = Heat - Selected.

At every strict positive restart time both the heat reconstruction and the
selected inverse-Fourier representative are spatially `C³`. Therefore
Mathlib's iterated-Fréchet subtraction rule gives the exact order-three
identity

    D³ Duhamel = D³ Heat - D³ Selected.

This is the third-jet term needed by the time derivative candidate for the
first spatial Fréchet derivative of the Duhamel reconstruction.

No new estimate, time derivative, or mixed-derivative interchange is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelThirdFrechetMild
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

attribute [local instance 1100] NormedSpace.complexToReal

/-- The complete third Fréchet derivative of the selected Duhamel
reconstruction is the heat third derivative minus the selected-state third
derivative. -/
theorem h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_iteratedFDeriv_three_eq_heat_sub_selected
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    iteratedFDeriv ℝ 3
        (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
          ν t W W i)
        x
      =
    iteratedFDeriv ℝ 3
        (h3SpectralScalarHeatC3Representative
          ν t (U₀ i))
        x
      -
    iteratedFDeriv ℝ 3
        (h3SpectralScalarC1Representative
          (W t i))
        x := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let H : H3FourierPoint3 → ℂ :=
    h3SpectralScalarHeatC3Representative
      ν t (U₀ i)

  let D : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
      ν t W W i

  let S : H3FourierPoint3 → ℂ :=
    h3SpectralScalarC1Representative
      (W t i)

  have hMild :
      S = H - D := by
    dsimp only [S, H, D, W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_mild_at
        hν U₀ hA hU₀ ht htR i

  have hDuhamel :
      D = H - S := by
    funext y
    have hy := congrFun hMild y
    change S y = H y - D y at hy
    change D y = H y - S y
    rw [hy]
    ring

  have hHeatC3 :
      ContDiff ℝ 3 H := by
    dsimp only [H]
    exact
      h3SpectralScalarHeatC3Representative_contDiff_three
        hν ht (U₀ i)

  have hSelectedC3 :
      ContDiff ℝ 3 S := by
    dsimp only [S, W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_contDiff_nat
        3 hν U₀ hA hU₀ ht htR i

  change
    iteratedFDeriv ℝ 3 D x
      =
    iteratedFDeriv ℝ 3 H x
      -
    iteratedFDeriv ℝ 3 S x

  rw [hDuhamel]

  exact
    iteratedFDeriv_sub_apply
      (𝕜 := ℝ)
      (i := 3)
      (x := x)
      hHeatC3.contDiffAt
      hSelectedC3.contDiffAt

/-- Evaluation of the order-three mild identity on any fixed triple of spatial
directions. -/
theorem h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_iteratedFDeriv_three_eval_eq_heat_sub_selected
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : H3FourierPoint3)
    (m : Fin 3 → H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    iteratedFDeriv ℝ 3
        (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
          ν t W W i)
        x m
      =
    iteratedFDeriv ℝ 3
        (h3SpectralScalarHeatC3Representative
          ν t (U₀ i))
        x m
      -
    iteratedFDeriv ℝ 3
        (h3SpectralScalarC1Representative
          (W t i))
        x m := by
  dsimp only

  have hOperator :=
    h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_iteratedFDeriv_three_eq_heat_sub_selected
      hν U₀ hA hU₀ ht htR i x

  dsimp only at hOperator

  have hEval :=
    congrArg
      (fun T :
        ContinuousMultilinearMap
          ℝ
          (fun _ : Fin 3 => H3FourierPoint3)
          ℂ =>
        T m)
      hOperator

  simpa only [sub_apply] using hEval

end

end Euclidean
end Bridge
end PrimeTensor
