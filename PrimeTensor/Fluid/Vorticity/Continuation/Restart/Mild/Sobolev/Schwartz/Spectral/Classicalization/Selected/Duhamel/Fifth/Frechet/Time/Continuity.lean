import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Fifth.Frechet.Mild
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Quintic.Fifth.Frechet.Time.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Time.Fifth.Coordinate.Continuity

/-!
# Classicalization: time continuity of the selected Duhamel fifth Fréchet jet

The selected fifth-order mild identity gives, at every strict positive restart
time,

    D⁵ Duhamel = D⁵ Heat - D⁵ Selected.

The two terms on the right are separately time-continuous for every fixed
ordered quintuple of canonical coordinate directions:

* `Heat.Time.Fifth.Coordinate.Continuity` handles the positive-time heat term;
* `Quintic.Fifth.Frechet.Time.Continuity` handles the selected inverse-Fourier
  term.

Since the fifth-order mild identity is available throughout the open restart
interval, it is an eventual equality near every strict positive interior base
time. Continuity therefore transports directly to the evaluated Duhamel fifth
jet.

No new estimate, derivative, or interchange theorem is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelFifthFrechetTimeContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

attribute [local instance 1100] NormedSpace.complexToReal

/-- Every fixed ordered canonical-coordinate evaluation of the selected
Duhamel fifth spatial Fréchet derivative is time-continuous at every strict
positive interior restart time. -/
theorem h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_fifthFrechet_coordinate_eval_continuousAt_time
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s < h3FinHeatLerayRestartRadius ν A)
    (i a b c d e : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ContinuousAt
      (fun r : ℝ =>
        iteratedFDeriv ℝ 5
          (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
            ν r W W i)
          x
          ![
            h3FourierAxisDirection (h3AxisOfFin3 a),
            h3FourierAxisDirection (h3AxisOfFin3 b),
            h3FourierAxisDirection (h3AxisOfFin3 c),
            h3FourierAxisDirection (h3AxisOfFin3 d),
            h3FourierAxisDirection (h3AxisOfFin3 e)
          ])
      s := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let m : Fin 5 → H3FourierPoint3 :=
    ![
      h3FourierAxisDirection (h3AxisOfFin3 a),
      h3FourierAxisDirection (h3AxisOfFin3 b),
      h3FourierAxisDirection (h3AxisOfFin3 c),
      h3FourierAxisDirection (h3AxisOfFin3 d),
      h3FourierAxisDirection (h3AxisOfFin3 e)
    ]

  let D : ℝ → ℂ :=
    fun r =>
      iteratedFDeriv ℝ 5
        (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
          ν r W W i)
        x m

  let H : ℝ → ℂ :=
    fun r =>
      iteratedFDeriv ℝ 5
        (h3SpectralScalarHeatC3Representative
          ν r (U₀ i))
        x m

  let S : ℝ → ℂ :=
    fun r =>
      iteratedFDeriv ℝ 5
        (h3SpectralScalarC1Representative
          (W r i))
        x m

  have hHeat :
      ContinuousAt H s := by
    dsimp only [H, m]
    exact
      h3SpectralScalarHeatC3Representative_fifthFrechet_coordinate_eval_continuousAt_time
        hν hs (U₀ i) a b c d e x

  have hSelected :
      ContinuousAt S s := by
    dsimp only [S, m, W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_fifthFrechet_eval_continuousAt
        hν U₀ hA hU₀ hs hsR i x
        ![
          h3FourierAxisDirection (h3AxisOfFin3 a),
          h3FourierAxisDirection (h3AxisOfFin3 b),
          h3FourierAxisDirection (h3AxisOfFin3 c),
          h3FourierAxisDirection (h3AxisOfFin3 d),
          h3FourierAxisDirection (h3AxisOfFin3 e)
        ]

  have hRHS :
      ContinuousAt
        (fun r : ℝ => H r - S r)
        s :=
    hHeat.sub hSelected

  have hInterior :
      Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν A)
        ∈ 𝓝 s :=
    Ioo_mem_nhds hs hsR

  have hEq :
      D =ᶠ[𝓝 s]
        (fun r : ℝ => H r - S r) := by
    filter_upwards [hInterior] with r hr
    dsimp only [D, H, S, m, W]
    exact
      h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_iteratedFDeriv_five_eval_eq_heat_sub_selected
        hν U₀ hA hU₀ hr.1 hr.2.le i x
        ![
          h3FourierAxisDirection (h3AxisOfFin3 a),
          h3FourierAxisDirection (h3AxisOfFin3 b),
          h3FourierAxisDirection (h3AxisOfFin3 c),
          h3FourierAxisDirection (h3AxisOfFin3 d),
          h3FourierAxisDirection (h3AxisOfFin3 e)
        ]

  change ContinuousAt D s
  exact hRHS.congr_of_eventuallyEq hEq

end

end Euclidean
end Bridge
end PrimeTensor
