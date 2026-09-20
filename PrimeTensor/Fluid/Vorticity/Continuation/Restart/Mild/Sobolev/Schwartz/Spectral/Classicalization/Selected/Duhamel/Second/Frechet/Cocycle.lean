import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.First.Frechet.Cocycle
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Selected.Full.C2
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.Full.Pointwise

/-!
# Classicalization: second-Fréchet Duhamel cocycle

The exact selected `C¹` Duhamel cocycle is already available as an equality of
spatial functions,

    Total(t+h) = History(h) + Fresh(t,h).

At order two we deliberately do **not** introduce a generic bounded Hessian
evaluation functional on arbitrary `H³` states.  Such a construction would be
stronger than the regularity naturally supplied by a general H³ state.

Instead, this particular fresh remainder inherits `C²` regularity from the
cocycle itself:

* `Total(t+h)` is the selected Duhamel reconstruction at a positive interior
  time, hence is spatially `C²`;
* `History(h)` is a positive-time heat reconstruction, hence is spatially
  `C³`;
* therefore `Fresh = Total - History` is spatially `C²`.

Mathlib's `iteratedFDeriv_sub_apply` then differentiates the exact cocycle
twice and gives the ordered coordinate identity

    D² Total[e_a,e_b]
      =
    D² History[e_a,e_b] + D² Fresh[e_a,e_b].

This is the exact algebraic split needed before combining the already-closed
old-history and fresh endpoint limits.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelSecondFrechetCocycle
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- The shifted spectral fresh remainder in the exact selected Duhamel cocycle
is spatially `C²`, even though no generic H³-to-C² reconstruction theorem is
asserted.  Its extra regularity follows from `Fresh = Total - History`. -/
theorem h3SelectedDuhamelFresh_C1Representative_contDiff_two
    {ν A t h : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (hh : 0 < h)
    (hthR : t + h ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let Dfresh : H3SpectralScalarState :=
      h3SpectralFinHeatLerayDuhamel
        ν h hν
        (fun r => W (r + t))
        (fun r => W (r + t))
        i
    ContDiff ℝ 2
      (h3SpectralScalarC1Representative Dfresh) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let Dfresh : H3SpectralScalarState :=
    h3SpectralFinHeatLerayDuhamel
      ν h hν
      (fun r => W (r + t))
      (fun r => W (r + t))
      i

  let Total : H3FourierPoint3 → ℂ :=
    h3SpectralScalarC1Representative
      (h3SpectralFinHeatLerayDuhamel
        ν (t + h) hν W W i)

  let History : H3FourierPoint3 → ℂ :=
    h3SelectedDuhamelHistoryHeatRepresentative
      ν A t h hν U₀ hA hU₀ ht i

  let Fresh : H3FourierPoint3 → ℂ :=
    h3SpectralScalarC1Representative Dfresh

  have hth : 0 < t + h := add_pos ht hh

  have hCocycle :
      Total = History + Fresh := by
    dsimp only [Total, History, Fresh, Dfresh, W]
    exact
      h3SelectedDuhamelC1Representative_add_time_eq_history_add_fresh
        hν U₀ hA hU₀ ht hh i

  have hTotalClassical :
      Total =
        h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
          ν (t + h) W W i := by
    have hGeneric :=
      h3SelectedDuhamelC1Representative_eq_spectralScalarC1Representative
        hν U₀ hA hU₀ hth i
    have hClassical :=
      h3SelectedDuhamelC1Representative_eq_C3Duhamel
        hν U₀ hA hU₀ hth hthR i
    dsimp only at hGeneric hClassical
    dsimp only [Total, W]
    exact hGeneric.symm.trans hClassical

  have hTotalC2 : ContDiff ℝ 2 Total := by
    rw [hTotalClassical]
    exact
      h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_contDiff_two
        hν U₀ hA hU₀ hth hthR i

  let Dt : H3SpectralScalarState :=
    h3SpectralFinHeatLerayDuhamel ν t hν W W i

  have hHistoryEq :
      History =
        h3SpectralScalarHeatC3Representative
          ν h Dt := by
    dsimp only [History, Dt, W]
    exact
      h3SelectedDuhamelHistoryHeatRepresentative_eq_heatC3Representative
        hν U₀ hA hU₀ ht i

  have hHistoryC2 : ContDiff ℝ 2 History := by
    rw [hHistoryEq]
    exact
      (h3SpectralScalarHeatC3Representative_contDiff_three
        hν hh Dt).of_le (by norm_num)

  have hFreshEq :
      Fresh = Total - History := by
    apply funext
    intro x
    have hx := congrFun hCocycle x
    dsimp only [Pi.add_apply] at hx
    change Fresh x = Total x - History x
    rw [eq_sub_iff_add_eq]
    simpa [add_comm] using hx.symm

  have hFreshC2 : ContDiff ℝ 2 Fresh := by
    rw [hFreshEq]
    exact hTotalC2.sub hHistoryC2

  simpa only [Fresh, Dfresh, W] using hFreshC2

/-- Twice differentiating the exact selected Duhamel cocycle gives the ordered
second-Fréchet coordinate split into old history plus fresh remainder. -/
theorem h3SelectedDuhamelC1Representative_add_time_secondFrechet_coordinate_eq_history_add_fresh
    {ν A t h : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (hh : 0 < h)
    (hthR : t + h ≤ h3FinHeatLerayRestartRadius ν A)
    (i a b : Fin 3)
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
    let m : Fin 2 → H3FourierPoint3 :=
      ![
        h3FourierAxisDirection (h3AxisOfFin3 a),
        h3FourierAxisDirection (h3AxisOfFin3 b)
      ]
    iteratedFDeriv ℝ 2
        (h3SpectralScalarC1Representative
          (h3SpectralFinHeatLerayDuhamel
            ν (t + h) hν W W i))
        x m
      =
    iteratedFDeriv ℝ 2
        (h3SelectedDuhamelHistoryHeatRepresentative
          ν A t h hν U₀ hA hU₀ ht i)
        x m
      +
    iteratedFDeriv ℝ 2
        (h3SpectralScalarC1Representative Dfresh)
        x m := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let Dfresh : H3SpectralScalarState :=
    h3SpectralFinHeatLerayDuhamel
      ν h hν
      (fun r => W (r + t))
      (fun r => W (r + t))
      i

  let Total : H3FourierPoint3 → ℂ :=
    h3SpectralScalarC1Representative
      (h3SpectralFinHeatLerayDuhamel
        ν (t + h) hν W W i)

  let History : H3FourierPoint3 → ℂ :=
    h3SelectedDuhamelHistoryHeatRepresentative
      ν A t h hν U₀ hA hU₀ ht i

  let Fresh : H3FourierPoint3 → ℂ :=
    h3SpectralScalarC1Representative Dfresh

  let m : Fin 2 → H3FourierPoint3 :=
    ![
      h3FourierAxisDirection (h3AxisOfFin3 a),
      h3FourierAxisDirection (h3AxisOfFin3 b)
    ]

  have hth : 0 < t + h := add_pos ht hh

  have hCocycle :
      Total = History + Fresh := by
    dsimp only [Total, History, Fresh, Dfresh, W]
    exact
      h3SelectedDuhamelC1Representative_add_time_eq_history_add_fresh
        hν U₀ hA hU₀ ht hh i

  have hTotalClassical :
      Total =
        h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
          ν (t + h) W W i := by
    have hGeneric :=
      h3SelectedDuhamelC1Representative_eq_spectralScalarC1Representative
        hν U₀ hA hU₀ hth i
    have hClassical :=
      h3SelectedDuhamelC1Representative_eq_C3Duhamel
        hν U₀ hA hU₀ hth hthR i
    dsimp only at hGeneric hClassical
    dsimp only [Total, W]
    exact hGeneric.symm.trans hClassical

  have hTotalC2 : ContDiff ℝ 2 Total := by
    rw [hTotalClassical]
    exact
      h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_contDiff_two
        hν U₀ hA hU₀ hth hthR i

  let Dt : H3SpectralScalarState :=
    h3SpectralFinHeatLerayDuhamel ν t hν W W i

  have hHistoryEq :
      History =
        h3SpectralScalarHeatC3Representative
          ν h Dt := by
    dsimp only [History, Dt, W]
    exact
      h3SelectedDuhamelHistoryHeatRepresentative_eq_heatC3Representative
        hν U₀ hA hU₀ ht i

  have hHistoryC2 : ContDiff ℝ 2 History := by
    rw [hHistoryEq]
    exact
      (h3SpectralScalarHeatC3Representative_contDiff_three
        hν hh Dt).of_le (by norm_num)

  have hFreshEq :
      Fresh = Total - History := by
    apply funext
    intro y
    have hy := congrFun hCocycle y
    dsimp only [Pi.add_apply] at hy
    change Fresh y = Total y - History y
    rw [eq_sub_iff_add_eq]
    simpa [add_comm] using hy.symm

  have hSub :=
    iteratedFDeriv_sub_apply
      (𝕜 := ℝ)
      (i := 2)
      (x := x)
      hTotalC2.contDiffAt
      hHistoryC2.contDiffAt

  have hSubEval :=
    congrArg
      (fun T => T m)
      hSub

  rw [← hFreshEq] at hSubEval

  have hSubEval' :
      iteratedFDeriv ℝ 2 Fresh x m
        =
      iteratedFDeriv ℝ 2 Total x m
        -
      iteratedFDeriv ℝ 2 History x m := by
    simpa [sub_eq_add_neg] using hSubEval

  have hAdd :
      iteratedFDeriv ℝ 2 Fresh x m
        +
      iteratedFDeriv ℝ 2 History x m
        =
      iteratedFDeriv ℝ 2 Total x m :=
    (eq_sub_iff_add_eq).1 hSubEval'

  change
    iteratedFDeriv ℝ 2 Total x m
      =
    iteratedFDeriv ℝ 2 History x m
      +
    iteratedFDeriv ℝ 2 Fresh x m

  calc
    iteratedFDeriv ℝ 2 Total x m
        =
      iteratedFDeriv ℝ 2 Fresh x m
        +
      iteratedFDeriv ℝ 2 History x m := hAdd.symm
    _ =
      iteratedFDeriv ℝ 2 History x m
        +
      iteratedFDeriv ℝ 2 Fresh x m := add_comm _ _

end

end Euclidean
end Bridge
end PrimeTensor
