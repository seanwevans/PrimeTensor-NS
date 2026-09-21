import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Fourth.Frechet.Mild
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Sixth.Endpoint.Fifth.Mild.Mass
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Quintic.Fifth.Frechet.Time.Continuity

/-!
# Classicalization: selected Duhamel fifth-Fréchet mild identity

The selected pointwise mild equation is

    Selected = Heat - Duhamel.

Hence

    Duhamel = Heat - Selected.

The sixth endpoint already proves an integrable full fifth raw Fourier moment
for the positive-time free heat term.  This upgrades the ordinary inverse-
Fourier heat reconstruction to spatial `C⁵`.  Together with the selected
state's existing `C⁵` regularity, Mathlib's iterated-Fréchet subtraction rule
gives

    D⁵ Duhamel = D⁵ Heat - D⁵ Selected.

No new heat or Duhamel estimate is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelFifthFrechetMild
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

attribute [local instance 1100] NormedSpace.complexToReal

/-- Positive-time heat smoothing gives five spatial derivatives once the
already-compiled fifth Fourier moment is used. -/
theorem h3SpectralScalarHeatC3Representative_contDiff_five
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState) :
    ContDiff ℝ 5
      (h3SpectralScalarHeatC3Representative ν t G) := by
  have hFourier :
      ContDiff ℝ 5
        (FourierTransform.fourier
          (h3SpectralScalarHeatRawRepresentative ν t G)) := by
    apply Real.contDiff_fourier
    intro n hn

    have hn5 : n ≤ 5 := by
      simpa using hn

    by_cases hn3 : n ≤ 3
    · exact
        h3SpectralScalarHeatRawRepresentative_moment_integrable
          hν ht G n hn3
    · have hn4or5 : n = 4 ∨ n = 5 := by
        omega
      rcases hn4or5 with rfl | rfl
      · exact
          h3SpectralScalarHeatRawRepresentative_fourthMoment_integrable
            hν ht G
      · exact
          h3SpectralScalarHeatRawRepresentative_fifthMoment_integrable
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

/-- The complete fifth Fréchet derivative of the selected Duhamel
reconstruction is the heat fifth derivative minus the selected-state fifth
derivative. -/
theorem h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_iteratedFDeriv_five_eq_heat_sub_selected
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
    iteratedFDeriv ℝ 5
        (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
          ν t W W i)
        x
      =
    iteratedFDeriv ℝ 5
        (h3SpectralScalarHeatC3Representative
          ν t (U₀ i))
        x
      -
    iteratedFDeriv ℝ 5
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

  have hHeatC5 :
      ContDiff ℝ 5 H := by
    dsimp only [H]
    exact
      h3SpectralScalarHeatC3Representative_contDiff_five
        hν ht (U₀ i)

  have hSelectedC5 :
      ContDiff ℝ 5 S := by
    dsimp only [S, W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_contDiff_nat
        5 hν U₀ hA hU₀ ht htR i

  change
    iteratedFDeriv ℝ 5 D x
      =
    iteratedFDeriv ℝ 5 H x
      -
    iteratedFDeriv ℝ 5 S x

  rw [hDuhamel]

  exact
    iteratedFDeriv_sub_apply
      (𝕜 := ℝ)
      (i := 5)
      (x := x)
      hHeatC5.contDiffAt
      hSelectedC5.contDiffAt

/-- Evaluation of the order-five mild identity on any fixed quintuple of
spatial directions. -/
theorem h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_iteratedFDeriv_five_eval_eq_heat_sub_selected
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : H3FourierPoint3)
    (m : Fin 5 → H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    iteratedFDeriv ℝ 5
        (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
          ν t W W i)
        x m
      =
    iteratedFDeriv ℝ 5
        (h3SpectralScalarHeatC3Representative
          ν t (U₀ i))
        x m
      -
    iteratedFDeriv ℝ 5
        (h3SpectralScalarC1Representative
          (W t i))
        x m := by
  dsimp only

  have hOperator :=
    h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_iteratedFDeriv_five_eq_heat_sub_selected
      hν U₀ hA hU₀ ht htR i x

  dsimp only at hOperator

  have hEval :=
    congrArg
      (fun T :
        ContinuousMultilinearMap
          ℝ
          (fun _ : Fin 5 => H3FourierPoint3)
          ℂ =>
        T m)
      hOperator

  simpa only [sub_apply] using hEval

end

end Euclidean
end Bridge
end PrimeTensor
