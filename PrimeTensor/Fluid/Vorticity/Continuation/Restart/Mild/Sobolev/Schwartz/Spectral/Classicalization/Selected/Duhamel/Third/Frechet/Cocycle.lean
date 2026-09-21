import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Second.Frechet.Cocycle
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Third.Frechet.Mild

/-!
# Classicalization: third-Fréchet Duhamel cocycle

The exact selected `C¹` Duhamel cocycle is already available as an equality of
spatial functions,

    Total(t+h) = History(h) + Fresh(t,h).

At order three the shifted spectral fresh remainder is not asserted to be
`C³` by a generic H³ reconstruction theorem.  Instead its regularity again
comes from the exact cocycle:

* `Total(t+h)` equals `Heat(t+h) - Selected(t+h)`, and both terms are spatially
  `C³`;
* `History(h)` is a positive-time heat reconstruction and is spatially `C³`;
* therefore `Fresh = Total - History` is spatially `C³`.

Mathlib's `iteratedFDeriv_sub_apply` then differentiates the exact cocycle
three times and gives

    D³ Total[e_a,e_b,e_c]
      =
    D³ History[e_a,e_b,e_c] + D³ Fresh[e_a,e_b,e_c].

This is the exact algebraic split needed by the third-Fréchet right quotient.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelThirdFrechetCocycle
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- The shifted spectral fresh remainder in the exact selected Duhamel cocycle
is spatially `C³`. -/
theorem h3SelectedDuhamelFresh_C1Representative_contDiff_three
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
    ContDiff ℝ 3
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

  let H : H3FourierPoint3 → ℂ :=
    h3SpectralScalarHeatC3Representative
      ν (t + h) (U₀ i)

  let S : H3FourierPoint3 → ℂ :=
    h3SpectralScalarC1Representative
      (W (t + h) i)

  let D : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
      ν (t + h) W W i

  have hMild :
      S = H - D := by
    dsimp only [S, H, D, W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_mild_at
        hν U₀ hA hU₀ hth hthR i

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
        hν hth (U₀ i)

  have hSelectedC3 :
      ContDiff ℝ 3 S := by
    dsimp only [S, W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_contDiff_nat
        3 hν U₀ hA hU₀ hth hthR i

  have hDuhamelC3 :
      ContDiff ℝ 3 D := by
    rw [hDuhamel]
    exact hHeatC3.sub hSelectedC3

  have hTotalClassical :
      Total = D := by
    have hGeneric :=
      h3SelectedDuhamelC1Representative_eq_spectralScalarC1Representative
        hν U₀ hA hU₀ hth i
    have hClassical :=
      h3SelectedDuhamelC1Representative_eq_C3Duhamel
        hν U₀ hA hU₀ hth hthR i
    dsimp only at hGeneric hClassical
    dsimp only [Total, D, W]
    exact hGeneric.symm.trans hClassical

  have hTotalC3 :
      ContDiff ℝ 3 Total := by
    rw [hTotalClassical]
    exact hDuhamelC3

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

  have hHistoryC3 :
      ContDiff ℝ 3 History := by
    rw [hHistoryEq]
    exact
      h3SpectralScalarHeatC3Representative_contDiff_three
        hν hh Dt

  have hFreshEq :
      Fresh = Total - History := by
    apply funext
    intro x
    have hx := congrFun hCocycle x
    dsimp only [Pi.add_apply] at hx
    change Fresh x = Total x - History x
    rw [eq_sub_iff_add_eq]
    simpa [add_comm] using hx.symm

  have hFreshC3 :
      ContDiff ℝ 3 Fresh := by
    rw [hFreshEq]
    exact hTotalC3.sub hHistoryC3

  simpa only [Fresh, Dfresh, W] using hFreshC3

/-- Three spatial derivatives of the exact selected Duhamel cocycle split into
old history plus the shifted fresh remainder. -/
theorem h3SelectedDuhamelC1Representative_add_time_thirdFrechet_coordinate_eq_history_add_fresh
    {ν A t h : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (hh : 0 < h)
    (hthR : t + h ≤ h3FinHeatLerayRestartRadius ν A)
    (i a b c : Fin 3)
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
    let m : Fin 3 → H3FourierPoint3 :=
      ![
        h3FourierAxisDirection (h3AxisOfFin3 a),
        h3FourierAxisDirection (h3AxisOfFin3 b),
        h3FourierAxisDirection (h3AxisOfFin3 c)
      ]
    iteratedFDeriv ℝ 3
        (h3SpectralScalarC1Representative
          (h3SpectralFinHeatLerayDuhamel
            ν (t + h) hν W W i))
        x m
      =
    iteratedFDeriv ℝ 3
        (h3SelectedDuhamelHistoryHeatRepresentative
          ν A t h hν U₀ hA hU₀ ht i)
        x m
      +
    iteratedFDeriv ℝ 3
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

  let m : Fin 3 → H3FourierPoint3 :=
    ![
      h3FourierAxisDirection (h3AxisOfFin3 a),
      h3FourierAxisDirection (h3AxisOfFin3 b),
      h3FourierAxisDirection (h3AxisOfFin3 c)
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

  have hTotalC3 :
      ContDiff ℝ 3 Total := by
    let H : H3FourierPoint3 → ℂ :=
      h3SpectralScalarHeatC3Representative
        ν (t + h) (U₀ i)
    let S : H3FourierPoint3 → ℂ :=
      h3SpectralScalarC1Representative
        (W (t + h) i)
    let D : H3FourierPoint3 → ℂ :=
      h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
        ν (t + h) W W i

    have hMild :
        S = H - D := by
      dsimp only [S, H, D, W]
      exact
        h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_mild_at
          hν U₀ hA hU₀ hth hthR i

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
          hν hth (U₀ i)

    have hSelectedC3 :
        ContDiff ℝ 3 S := by
      dsimp only [S, W]
      exact
        h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_contDiff_nat
          3 hν U₀ hA hU₀ hth hthR i

    have hDuhamelC3 :
        ContDiff ℝ 3 D := by
      rw [hDuhamel]
      exact hHeatC3.sub hSelectedC3

    rw [hTotalClassical]
    exact hDuhamelC3

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

  have hHistoryC3 :
      ContDiff ℝ 3 History := by
    rw [hHistoryEq]
    exact
      h3SpectralScalarHeatC3Representative_contDiff_three
        hν hh Dt

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
      (i := 3)
      (x := x)
      hTotalC3.contDiffAt
      hHistoryC3.contDiffAt

  have hSubEval :=
    congrArg
      (fun T => T m)
      hSub

  rw [← hFreshEq] at hSubEval

  have hSubEval' :
      iteratedFDeriv ℝ 3 Fresh x m
        =
      iteratedFDeriv ℝ 3 Total x m
        -
      iteratedFDeriv ℝ 3 History x m := by
    simpa [sub_eq_add_neg] using hSubEval

  have hAdd :
      iteratedFDeriv ℝ 3 Fresh x m
        +
      iteratedFDeriv ℝ 3 History x m
        =
      iteratedFDeriv ℝ 3 Total x m :=
    (eq_sub_iff_add_eq).1 hSubEval'

  change
    iteratedFDeriv ℝ 3 Total x m
      =
    iteratedFDeriv ℝ 3 History x m
      +
    iteratedFDeriv ℝ 3 Fresh x m

  calc
    iteratedFDeriv ℝ 3 Total x m
        =
      iteratedFDeriv ℝ 3 Fresh x m
        +
      iteratedFDeriv ℝ 3 History x m := hAdd.symm
    _ =
      iteratedFDeriv ℝ 3 History x m
        +
      iteratedFDeriv ℝ 3 Fresh x m := add_comm _ _

end

end Euclidean
end Bridge
end PrimeTensor
