import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Pointwise.Mild
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.C1
import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Classicalization: selected Duhamel first-Fréchet mild identity

The selected positive-time pointwise mild equation is already an equality of
spatial functions,

    Selected = Heat - Duhamel.

The nonlinear Duhamel reconstruction already has its canonical operator-valued
first Fréchet derivative, and the positive-time heat reconstruction is spatially
smooth. Differentiating the mild identity once in the spatial variable
therefore gives the exact operator identity

    D_x Duhamel = D_x Heat - D_x Selected.

This is a representation/linearity checkpoint only. No new estimate, temporal
regularity theorem, or derivative interchange is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelFirstFrechetMild
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

attribute [local instance 1100] NormedSpace.complexToReal

/-- At a strict positive selected restart time, the canonical first Fréchet
derivative of the Duhamel reconstruction is the heat first derivative minus
the selected-state first derivative. -/
theorem h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeDuhamel_selectedRestart_eq_heat_sub_selected
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
    h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeDuhamel
        ν t W W i x
      =
    fderiv ℝ
        (h3SpectralScalarHeatC3Representative
          ν t (U₀ i))
        x
      -
    fderiv ℝ
        (h3SpectralScalarC1Representative
          (W t i))
        x := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hWcont : Continuous W := by
    dsimp only [W]
    exact
      continuous_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀

  have hW :
      ∀ s ∈ Set.Ioo (0 : ℝ) t,
        ‖W s‖ ≤ 2 * A := by
    intro s hs
    dsimp only [W]
    exact
      norm_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_le_twoA
        hν U₀ hA hU₀ s

  have h2A : 0 ≤ 2 * A := by
    positivity

  have hDuhamel :
      HasFDerivAt
        (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
          ν t W W i)
        (h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeDuhamel
          ν t W W i x)
        x := by
    exact
      h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_hasFDerivAt
        hν ht.le h2A h2A
        W W
        hWcont hWcont
        hW hW
        i x

  have hHeatDiff :
      DifferentiableAt ℝ
        (h3SpectralScalarHeatC3Representative
          ν t (U₀ i))
        x := by
    exact
      ((h3SpectralScalarHeatC3Representative_contDiff_three
        hν ht (U₀ i)).of_le (by norm_num)).differentiable_one.differentiableAt

  have hDuhamelDiff :
      DifferentiableAt ℝ
        (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
          ν t W W i)
        x :=
    hDuhamel.differentiableAt

  have hMild :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_mild_at
      hν U₀ hA hU₀ ht htR i

  dsimp only at hMild

  have hMildF :=
    congrArg
      (fun f : H3FourierPoint3 → ℂ =>
        fderiv ℝ f x)
      hMild

  change
    fderiv ℝ
        (h3SpectralScalarC1Representative
          (W t i))
        x
      =
    fderiv ℝ
        (fun y : H3FourierPoint3 =>
          h3SpectralScalarHeatC3Representative
              ν t (U₀ i) y
            -
          h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
              ν t W W i y)
        x
    at hMildF

  rw [
    fderiv_fun_sub
      hHeatDiff
      hDuhamelDiff
  ] at hMildF

  rw [hDuhamel.fderiv] at hMildF

  apply (eq_sub_iff_add_eq).2
  rw [add_comm]
  exact (eq_sub_iff_add_eq).1 hMildF

/-- Evaluation of the selected first-Fréchet mild identity on an arbitrary
fixed spatial direction. -/
theorem h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeDuhamel_selectedRestart_apply_eq_heat_sub_selected
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x v : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeDuhamel
        ν t W W i x v
      =
    (fderiv ℝ
        (h3SpectralScalarHeatC3Representative
          ν t (U₀ i))
        x) v
      -
    (fderiv ℝ
        (h3SpectralScalarC1Representative
          (W t i))
        x) v := by
  dsimp only

  have hOperator :=
    h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeDuhamel_selectedRestart_eq_heat_sub_selected
      hν U₀ hA hU₀ ht htR i x

  dsimp only at hOperator

  have hEval :=
    congrArg
      (fun T : H3FourierPoint3 →L[ℝ] ℂ => T v)
      hOperator

  simpa only [sub_apply] using hEval

end

end Euclidean
end Bridge
end PrimeTensor
