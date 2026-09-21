import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Third.Frechet.Mild
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Time.Fourth.Coordinate.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Spatial.Regularity

/-!
# Classicalization: selected Duhamel fourth-Fréchet mild identity

The selected pointwise mild equation is an equality of spatial functions

    Selected = Heat - Duhamel.

Rearranging gives

    Duhamel = Heat - Selected.

At every strict positive restart time the selected inverse-Fourier
representative is spatially `C⁴`.  The heat side has the required fourth
Fourier moment at positive time; this file packages that already-proved moment
as spatial `C⁴` regularity of the ordinary inverse-Fourier heat reconstruction.
Mathlib's iterated-Fréchet subtraction rule then gives

    D⁴ Duhamel = D⁴ Heat - D⁴ Selected.

The evaluated form is the bridge needed to combine the new positive-time heat
fourth-coordinate continuity with the selected fourth-Fréchet time continuity.

No new heat estimate, Duhamel estimate, or mixed-derivative interchange is
introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelFourthFrechetMild
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

attribute [local instance 1100] NormedSpace.complexToReal

/-- Positive-time heat smoothing actually gives four spatial derivatives once
we use the already-compiled fourth Fourier moment. -/
theorem h3SpectralScalarHeatC3Representative_contDiff_four
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState) :
    ContDiff ℝ 4
      (h3SpectralScalarHeatC3Representative ν t G) := by
  have hFourier :
      ContDiff ℝ 4
        (FourierTransform.fourier
          (h3SpectralScalarHeatRawRepresentative ν t G)) := by
    apply Real.contDiff_fourier
    intro n hn

    have hn4 : n ≤ 4 := by
      simpa using hn

    by_cases hn3 : n ≤ 3
    · exact
        h3SpectralScalarHeatRawRepresentative_moment_integrable
          hν ht G n hn3
    · have hnEq : n = 4 := by
        omega
      subst n
      exact
        h3SpectralScalarHeatRawRepresentative_fourthMoment_integrable
          hν ht G

  have hEq :
      h3SpectralScalarHeatC3Representative ν t G
        =
      fun x : H3FourierPoint3 =>
        FourierTransform.fourier
          (h3SpectralScalarHeatRawRepresentative ν t G) (-x) := by
    funext x
    unfold h3SpectralScalarHeatC3Representative
    exact
      Real.fourierInv_eq_fourier_neg
        (h3SpectralScalarHeatRawRepresentative ν t G) x

  rw [hEq]
  exact hFourier.comp (by fun_prop)

/-- The complete fourth Fréchet derivative of the selected Duhamel
reconstruction is the heat fourth derivative minus the selected-state fourth
derivative. -/
theorem h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_iteratedFDeriv_four_eq_heat_sub_selected
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
    iteratedFDeriv ℝ 4
        (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
          ν t W W i)
        x
      =
    iteratedFDeriv ℝ 4
        (h3SpectralScalarHeatC3Representative
          ν t (U₀ i))
        x
      -
    iteratedFDeriv ℝ 4
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

  have hHeatC4 :
      ContDiff ℝ 4 H := by
    dsimp only [H]
    exact
      h3SpectralScalarHeatC3Representative_contDiff_four
        hν ht (U₀ i)

  have hSelectedC4 :
      ContDiff ℝ 4 S := by
    dsimp only [S, W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_contDiff_nat
        4 hν U₀ hA hU₀ ht htR i

  change
    iteratedFDeriv ℝ 4 D x
      =
    iteratedFDeriv ℝ 4 H x
      -
    iteratedFDeriv ℝ 4 S x

  rw [hDuhamel]

  exact
    iteratedFDeriv_sub_apply
      (𝕜 := ℝ)
      (i := 4)
      (x := x)
      hHeatC4.contDiffAt
      hSelectedC4.contDiffAt

/-- Evaluation of the order-four mild identity on any fixed quadruple of
spatial directions. -/
theorem h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_iteratedFDeriv_four_eval_eq_heat_sub_selected
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : H3FourierPoint3)
    (m : Fin 4 → H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    iteratedFDeriv ℝ 4
        (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
          ν t W W i)
        x m
      =
    iteratedFDeriv ℝ 4
        (h3SpectralScalarHeatC3Representative
          ν t (U₀ i))
        x m
      -
    iteratedFDeriv ℝ 4
        (h3SpectralScalarC1Representative
          (W t i))
        x m := by
  dsimp only

  have hOperator :=
    h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_iteratedFDeriv_four_eq_heat_sub_selected
      hν U₀ hA hU₀ ht htR i x

  dsimp only at hOperator

  have hEval :=
    congrArg
      (fun T :
        ContinuousMultilinearMap
          ℝ
          (fun _ : Fin 4 => H3FourierPoint3)
          ℂ =>
        T m)
      hOperator

  simpa only [sub_apply] using hEval

end

end Euclidean
end Bridge
end PrimeTensor
