import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Derivative.DiagonalC1Cocycle
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Derivative.HistoryHeatC1Bridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.H3.Real.C1.Bridge
import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Classicalization: first-Fréchet Duhamel cocycle

The selected `C¹` Duhamel cocycle is already available as an exact equality of
spatial functions:

    C1(D(t+h)) = historyHeat(h) + C1(Dfresh(t,h)).

For positive `h`, the history term is a positive-time heat reconstruction and
is therefore spatially `C³`.  The fresh spectral Duhamel remainder is an H³
state, so its canonical inverse-Fourier reconstruction is spatially `C¹`.

This file differentiates the cocycle once in the spatial variable and records

    D C1(D(t+h))
      =
    D historyHeat(h) + D C1(Dfresh(t,h)).

A second theorem evaluates the operator identity on one canonical coordinate
direction.  This is the exact algebraic decomposition needed before taking the
right time quotient of the first spatial derivative.

No temporal limit, endpoint estimate, or mixed-partial interchange is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelFirstFrechetCocycle
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- Differentiating the selected `C¹` Duhamel cocycle once in space gives the
exact operator-valued old-history plus fresh-remainder decomposition. -/
theorem h3SelectedDuhamelC1Representative_add_time_fderiv_eq_history_add_fresh
    {ν A t h : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (hh : 0 < h)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let Dfresh : H3SpectralScalarState :=
      h3SpectralFinHeatLerayDuhamel
        ν h hν
        (fun r => W (r + t))
        (fun r => W (r + t))
        i
    fderiv ℝ
        (h3SpectralScalarC1Representative
          (h3SpectralFinHeatLerayDuhamel
            ν (t + h) hν W W i))
        x
      =
    fderiv ℝ
        (h3SelectedDuhamelHistoryHeatRepresentative
          ν A t h hν U₀ hA hU₀ ht i)
        x
      +
    fderiv ℝ
        (h3SpectralScalarC1Representative Dfresh)
        x := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let Dt : H3SpectralScalarState :=
    h3SpectralFinHeatLerayDuhamel ν t hν W W i

  let Dfresh : H3SpectralScalarState :=
    h3SpectralFinHeatLerayDuhamel
      ν h hν
      (fun r => W (r + t))
      (fun r => W (r + t))
      i

  let H : H3FourierPoint3 → ℂ :=
    h3SelectedDuhamelHistoryHeatRepresentative
      ν A t h hν U₀ hA hU₀ ht i

  let F : H3FourierPoint3 → ℂ :=
    h3SpectralScalarC1Representative Dfresh

  have hCocycle :
      h3SpectralScalarC1Representative
          (h3SpectralFinHeatLerayDuhamel
            ν (t + h) hν W W i)
        =
      H + F := by
    dsimp only [H, F, Dfresh, W]
    exact
      h3SelectedDuhamelC1Representative_add_time_eq_history_add_fresh
        hν U₀ hA hU₀ ht hh i

  have hHistoryEq :
      H
        =
      h3SpectralScalarHeatC3Representative
        ν h Dt := by
    dsimp only [H, Dt, W]
    exact
      h3SelectedDuhamelHistoryHeatRepresentative_eq_heatC3Representative
        hν U₀ hA hU₀ ht i

  have hHistoryDiff :
      DifferentiableAt ℝ H x := by
    rw [hHistoryEq]
    exact
      ((h3SpectralScalarHeatC3Representative_contDiff_three
        hν hh Dt).of_le (by norm_num)).differentiable_one.differentiableAt

  have hFreshDiff :
      DifferentiableAt ℝ F x := by
    dsimp only [F]
    exact
      (h3SpectralScalarC1Representative_contDiff_one
        Dfresh).differentiable_one.differentiableAt

  have hFDeriv :=
    congrArg
      (fun f : H3FourierPoint3 → ℂ =>
        fderiv ℝ f x)
      hCocycle

  change
    fderiv ℝ
        (h3SpectralScalarC1Representative
          (h3SpectralFinHeatLerayDuhamel
            ν (t + h) hν W W i))
        x
      =
    fderiv ℝ
        (fun y : H3FourierPoint3 =>
          H y + F y)
        x
    at hFDeriv

  rw [fderiv_fun_add hHistoryDiff hFreshDiff] at hFDeriv

  dsimp only [H, F, Dfresh, W] at hFDeriv ⊢
  exact hFDeriv

/-- Evaluation of the first-Fréchet cocycle on one canonical spatial
coordinate direction. -/
theorem h3SelectedDuhamelC1Representative_add_time_fderiv_coordinate_eq_history_add_fresh
    {ν A t h : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (hh : 0 < h)
    (i a : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let Dfresh : H3SpectralScalarState :=
      h3SpectralFinHeatLerayDuhamel
        ν h hν
        (fun r => W (r + t))
        (fun r => W (r + t))
        i
    (fderiv ℝ
        (h3SpectralScalarC1Representative
          (h3SpectralFinHeatLerayDuhamel
            ν (t + h) hν W W i))
        x)
        (h3FourierAxisDirection (h3AxisOfFin3 a))
      =
    (fderiv ℝ
        (h3SelectedDuhamelHistoryHeatRepresentative
          ν A t h hν U₀ hA hU₀ ht i)
        x)
        (h3FourierAxisDirection (h3AxisOfFin3 a))
      +
    (fderiv ℝ
        (h3SpectralScalarC1Representative Dfresh)
        x)
        (h3FourierAxisDirection (h3AxisOfFin3 a)) := by
  dsimp only

  have hOperator :=
    h3SelectedDuhamelC1Representative_add_time_fderiv_eq_history_add_fresh
      hν U₀ hA hU₀ ht hh i x

  dsimp only at hOperator

  have hEval :=
    congrArg
      (fun T : H3FourierPoint3 →L[ℝ] ℂ =>
        T (h3FourierAxisDirection (h3AxisOfFin3 a)))
      hOperator

  simpa only [add_apply] using hEval

end

end Euclidean
end Bridge
end PrimeTensor
