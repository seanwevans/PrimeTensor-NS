import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedPointwiseMild
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedHessianTraceTimeContinuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.SelectedFullC2

/-!
# Classicalization: selected Duhamel Hessian trace from the mild identity

The temporal Duhamel derivative candidate contains the diagonal trace of the
named selected Duhamel Hessian

    h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel.

The preceding endpoint-quarter branch already proves that this named Hessian is
the genuine Frechet derivative of the complete first-Frechet Duhamel field,
while the original Duhamel reconstruction has that first-Frechet field as its
genuine derivative.

This file first packages the resulting identification

    D²(Duhamel)(x)[m₀,m₁] = Hessian_Duhamel(x)[m₀,m₁]

using Mathlib's `iteratedFDeriv_two_apply`.

It then differentiates the exact pointwise mild identity twice in the spatial
variable.  Since the selected state, positive-time heat reconstruction, and
selected Duhamel field are all spatially `C²`, the second derivative commutes
with subtraction.  Rearranging gives, on every canonical diagonal axis,

    Hessian_Duhamel[e_j,e_j]
      =
    D² Heat[e_j,e_j] - D² Selected[e_j,e_j].

Summing over the three axes yields the corresponding trace identity.

No new estimate is introduced here; this is purely derivative identification
and algebraic transport through the already-closed mild equation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedDuhamelHessianTraceMild
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

/-- The named selected Duhamel Hessian is exactly the second iterated Frechet
derivative of the selected classical Duhamel reconstruction. -/
theorem h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_iteratedFDeriv_two_eval_eq_secondFrechet
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : H3FourierPoint3)
    (m : Fin 2 → H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    iteratedFDeriv ℝ 2
        (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
          ν t W W i)
        x m
      =
    h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel
      ν t W W i x (m 0) (m 1) := by
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

  have hFirstEq :
      fderiv ℝ
          (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
            ν t W W i)
        =
      h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeDuhamel
        ν t W W i := by
    funext y
    exact
      (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_hasFDerivAt
        hν ht.le h2A h2A
        W W
        hWcont hWcont
        hW hW
        i y).fderiv

  have hSecondEq :
      fderiv ℝ
          (h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeDuhamel
            ν t W W i)
          x
        =
      h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel
        ν t W W i x := by
    exact
      (h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeDuhamel_selectedRestart_hasFDerivAt_secondFrechet
        hν U₀ hA hU₀ ht htR i x).fderiv

  rw [iteratedFDeriv_two_apply]
  rw [hFirstEq]
  rw [hSecondEq]

/-- On one canonical spatial axis, the selected Duhamel Hessian is the heat
second derivative minus the selected-state second derivative. -/
theorem h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel_selectedRestart_axis_eq_heat_sub_selected
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i j : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let e : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 j)
    h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel
        ν t W W i x e e
      =
    iteratedFDeriv ℝ 2
        (h3SpectralScalarHeatC3Representative
          ν t (U₀ i))
        x
        (fun _ : Fin 2 => e)
      -
    iteratedFDeriv ℝ 2
        (h3SpectralScalarC1Representative
          (W t i))
        x
        (fun _ : Fin 2 => e) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let e : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 j)

  let m : Fin 2 → H3FourierPoint3 :=
    fun _ => e

  have hMild :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_mild_at
      hν U₀ hA hU₀ ht htR i

  dsimp only at hMild

  have hHeatC2 :
      ContDiff ℝ 2
        (h3SpectralScalarHeatC3Representative
          ν t (U₀ i)) :=
    (h3SpectralScalarHeatC3Representative_contDiff_three
      hν ht (U₀ i)).of_le (by norm_num)

  have hDuhamelC2 :
      ContDiff ℝ 2
        (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
          ν t W W i) := by
    exact
      h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_contDiff_two
        hν U₀ hA hU₀ ht htR i

  have hSub :=
    iteratedFDeriv_sub_apply
      (𝕜 := ℝ)
      (i := 2)
      (x := x)
      hHeatC2.contDiffAt
      hDuhamelC2.contDiffAt

  have hSubEval :=
    congrArg
      (fun T => T m)
      hSub

  have hMildSecond :=
    congrArg
      (fun f =>
        iteratedFDeriv ℝ 2 f x)
      hMild

  have hMildSecondEval :=
    congrArg
      (fun T => T m)
      hMildSecond

  rw [hSubEval] at hMildSecondEval

  change
    iteratedFDeriv ℝ 2
        (h3SpectralScalarC1Representative
          (W t i))
        x m
      =
    iteratedFDeriv ℝ 2
        (h3SpectralScalarHeatC3Representative
          ν t (U₀ i))
        x m
      -
    iteratedFDeriv ℝ 2
        (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
          ν t W W i)
        x m
    at hMildSecondEval

  have hNamed :
      iteratedFDeriv ℝ 2
          (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
            ν t W W i)
          x m
        =
      h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel
        ν t W W i x e e := by
    simpa only [m] using
      h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_iteratedFDeriv_two_eval_eq_secondFrechet
        hν U₀ hA hU₀ ht htR i x m

  rw [hNamed] at hMildSecondEval

  change
    h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel
        ν t W W i x e e
      =
    iteratedFDeriv ℝ 2
        (h3SpectralScalarHeatC3Representative
          ν t (U₀ i))
        x m
      -
    iteratedFDeriv ℝ 2
        (h3SpectralScalarC1Representative
          (W t i))
        x m

  rw [eq_sub_iff_add_eq]
  rw [hMildSecondEval]
  abel

/-- Trace form of the twice-spatially-differentiated selected mild identity. -/
theorem h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel_selectedRestart_diagonalTrace_eq_heat_sub_selected
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
    (∑ j : Fin 3,
      h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel
        ν t W W i x
        (h3FourierAxisDirection (h3AxisOfFin3 j))
        (h3FourierAxisDirection (h3AxisOfFin3 j)))
      =
    (∑ j : Fin 3,
      iteratedFDeriv ℝ 2
        (h3SpectralScalarHeatC3Representative
          ν t (U₀ i))
        x
        (fun _ : Fin 2 =>
          h3FourierAxisDirection (h3AxisOfFin3 j)))
      -
    (∑ j : Fin 3,
      iteratedFDeriv ℝ 2
        (h3SpectralScalarC1Representative
          (W t i))
        x
        (fun _ : Fin 2 =>
          h3FourierAxisDirection (h3AxisOfFin3 j))) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  calc
    (∑ j : Fin 3,
      h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel
        ν t W W i x
        (h3FourierAxisDirection (h3AxisOfFin3 j))
        (h3FourierAxisDirection (h3AxisOfFin3 j)))
        =
      ∑ j : Fin 3,
        (iteratedFDeriv ℝ 2
            (h3SpectralScalarHeatC3Representative
              ν t (U₀ i))
            x
            (fun _ : Fin 2 =>
              h3FourierAxisDirection (h3AxisOfFin3 j))
          -
         iteratedFDeriv ℝ 2
            (h3SpectralScalarC1Representative
              (W t i))
            x
            (fun _ : Fin 2 =>
              h3FourierAxisDirection (h3AxisOfFin3 j))) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact
            h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel_selectedRestart_axis_eq_heat_sub_selected
              hν U₀ hA hU₀ ht htR i j x
    _ =
      (∑ j : Fin 3,
        iteratedFDeriv ℝ 2
          (h3SpectralScalarHeatC3Representative
            ν t (U₀ i))
          x
          (fun _ : Fin 2 =>
            h3FourierAxisDirection (h3AxisOfFin3 j)))
        -
      (∑ j : Fin 3,
        iteratedFDeriv ℝ 2
          (h3SpectralScalarC1Representative
            (W t i))
          x
          (fun _ : Fin 2 =>
            h3FourierAxisDirection (h3AxisOfFin3 j))) := by
          rw [Finset.sum_sub_distrib]

end

end Euclidean
end Bridge
end PrimeTensor
