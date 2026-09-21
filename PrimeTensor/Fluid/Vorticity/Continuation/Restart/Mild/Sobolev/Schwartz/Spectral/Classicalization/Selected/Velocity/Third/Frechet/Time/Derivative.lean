import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Time.Third.Coordinate.Generator.Trace
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Third.Frechet.Ordinary.Time.Derivative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Fifth.Frechet.Mild

/-!
# Classicalization: ordinary time derivative of the selected third Fréchet derivative

The positive-time heat third coordinate and the selected Duhamel third
coordinate now both have ordinary time derivatives.

On the open restart interval,

    D³u = D³Heat - D³Duhamel.

Subtracting the two compiled temporal derivatives gives

    ν * tr_abc(D⁵Heat)
      - (ν * tr_abc(D⁵Duhamel) + D³N_abc).

The selected fifth-Fréchet mild identity gives

    D⁵Duhamel = D⁵Heat - D⁵u.

After summing the three diagonal fifth-order coordinates, the heat terms
cancel and the coefficient becomes

    ν * tr_abc(D⁵u) - D³N_abc.

Thus each fixed ordered coordinate evaluation of the selected third spatial
Fréchet derivative has the exact order-three temporal PDE derivative.

No new estimate, limit, or time/space interchange theorem is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedVelocityThirdFrechetTimeDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- At every strict positive interior restart time, one ordered canonical
coordinate evaluation of the selected velocity third spatial Fréchet
derivative has an ordinary time derivative equal to viscosity times the
selected fifth spatial trace minus the instantaneous forcing third derivative. -/
theorem h3SelectedVelocity_C1_thirdFrechet_coordinate_hasDerivAt_time
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i a b c : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let ea : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 a)
    let eb : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 b)
    let ec : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 c)
    let m : Fin 3 → H3FourierPoint3 :=
      ![ea, eb, ec]
    HasDerivAt
      (fun r : ℝ =>
        iteratedFDeriv ℝ 3
          (h3SpectralScalarC1Representative
            (W r i))
          x m)
      ((ν : ℂ) *
          (∑ k : Fin 3,
            iteratedFDeriv ℝ 5
              (h3SpectralScalarC1Representative
                (W t i))
              x
              ![
                ea,
                eb,
                ec,
                h3FourierAxisDirection (h3AxisOfFin3 k),
                h3FourierAxisDirection (h3AxisOfFin3 k)
              ])
        -
      iteratedFDeriv ℝ 3
        (h3RawFinLerayOuterProductDivergenceC0Representative
          (W t) (W t) i)
        x m)
      t := by
  dsimp only

  let R : ℝ :=
    h3FinHeatLerayRestartRadius ν A

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let ea : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 a)

  let eb : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 b)

  let ec : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 c)

  let m : Fin 3 → H3FourierPoint3 :=
    ![ea, eb, ec]

  let H : ℝ → ℂ :=
    fun r =>
      h3SpectralScalarHeatThirdCoordinateRepresentative
        ν r (U₀ i) a b c x

  let D : ℝ → ℂ :=
    fun r =>
      iteratedFDeriv ℝ 3
        (h3SpectralScalarC1Representative
          (h3SpectralFinHeatLerayDuhamel
            ν r hν W W i))
        x m

  let S : ℝ → ℂ :=
    fun r =>
      iteratedFDeriv ℝ 3
        (h3SpectralScalarC1Representative
          (W r i))
        x m

  let heatTrace : ℂ :=
    ∑ k : Fin 3,
      iteratedFDeriv ℝ 5
        (h3SpectralScalarHeatC3Representative
          ν t (U₀ i))
        x
        ![
          ea,
          eb,
          ec,
          h3FourierAxisDirection (h3AxisOfFin3 k),
          h3FourierAxisDirection (h3AxisOfFin3 k)
        ]

  let duhamelTrace : ℂ :=
    ∑ k : Fin 3,
      iteratedFDeriv ℝ 5
        (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
          ν t W W i)
        x
        ![
          ea,
          eb,
          ec,
          h3FourierAxisDirection (h3AxisOfFin3 k),
          h3FourierAxisDirection (h3AxisOfFin3 k)
        ]

  let selectedTrace : ℂ :=
    ∑ k : Fin 3,
      iteratedFDeriv ℝ 5
        (h3SpectralScalarC1Representative
          (W t i))
        x
        ![
          ea,
          eb,
          ec,
          h3FourierAxisDirection (h3AxisOfFin3 k),
          h3FourierAxisDirection (h3AxisOfFin3 k)
        ]

  let forcingThird : ℂ :=
    iteratedFDeriv ℝ 3
      (h3RawFinLerayOuterProductDivergenceC0Representative
        (W t) (W t) i)
      x m

  have hHeat :
      HasDerivAt H
        ((ν : ℂ) * heatTrace)
        t := by
    dsimp only [H, heatTrace, ea, eb, ec]
    exact
      h3SpectralScalarHeatThirdCoordinateRepresentative_hasDerivAt_time_eq_viscosity_fifthTrace
        hν ht (U₀ i) a b c x

  have hDuhamel :
      HasDerivAt D
        ((ν : ℂ) * duhamelTrace + forcingThird)
        t := by
    dsimp only [D, duhamelTrace, forcingThird, W, ea, eb, ec, m]
    exact
      h3SelectedDuhamel_C1_thirdFrechet_coordinate_hasDerivAt_time
        hν U₀ hA hU₀ ht htR i a b c x

  have hSub :
      HasDerivAt
        (fun r : ℝ => H r - D r)
        ((ν : ℂ) * heatTrace -
          ((ν : ℂ) * duhamelTrace + forcingThird))
        t :=
    hHeat.sub hDuhamel

  have hFifth
      (k : Fin 3) :
      iteratedFDeriv ℝ 5
          (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
            ν t W W i)
          x
          ![
            ea,
            eb,
            ec,
            h3FourierAxisDirection (h3AxisOfFin3 k),
            h3FourierAxisDirection (h3AxisOfFin3 k)
          ]
        =
      iteratedFDeriv ℝ 5
          (h3SpectralScalarHeatC3Representative
            ν t (U₀ i))
          x
          ![
            ea,
            eb,
            ec,
            h3FourierAxisDirection (h3AxisOfFin3 k),
            h3FourierAxisDirection (h3AxisOfFin3 k)
          ]
        -
      iteratedFDeriv ℝ 5
          (h3SpectralScalarC1Representative
            (W t i))
          x
          ![
            ea,
            eb,
            ec,
            h3FourierAxisDirection (h3AxisOfFin3 k),
            h3FourierAxisDirection (h3AxisOfFin3 k)
          ] := by
    dsimp only [W, ea, eb, ec]
    exact
      h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_iteratedFDeriv_five_eval_eq_heat_sub_selected
        hν U₀ hA hU₀ ht htR.le i x
        ![
          h3FourierAxisDirection (h3AxisOfFin3 a),
          h3FourierAxisDirection (h3AxisOfFin3 b),
          h3FourierAxisDirection (h3AxisOfFin3 c),
          h3FourierAxisDirection (h3AxisOfFin3 k),
          h3FourierAxisDirection (h3AxisOfFin3 k)
        ]

  have hTrace :
      duhamelTrace = heatTrace - selectedTrace := by
    dsimp only [duhamelTrace, heatTrace, selectedTrace]
    calc
      (∑ k : Fin 3,
        iteratedFDeriv ℝ 5
          (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
            ν t W W i)
          x
          ![
            ea,
            eb,
            ec,
            h3FourierAxisDirection (h3AxisOfFin3 k),
            h3FourierAxisDirection (h3AxisOfFin3 k)
          ])
          =
        ∑ k : Fin 3,
          (iteratedFDeriv ℝ 5
              (h3SpectralScalarHeatC3Representative
                ν t (U₀ i))
              x
              ![
                ea,
                eb,
                ec,
                h3FourierAxisDirection (h3AxisOfFin3 k),
                h3FourierAxisDirection (h3AxisOfFin3 k)
              ]
            -
          iteratedFDeriv ℝ 5
              (h3SpectralScalarC1Representative
                (W t i))
              x
              ![
                ea,
                eb,
                ec,
                h3FourierAxisDirection (h3AxisOfFin3 k),
                h3FourierAxisDirection (h3AxisOfFin3 k)
              ]) := by
            apply Finset.sum_congr rfl
            intro k hk
            exact hFifth k
      _ =
        (∑ k : Fin 3,
          iteratedFDeriv ℝ 5
            (h3SpectralScalarHeatC3Representative
              ν t (U₀ i))
            x
            ![
              ea,
              eb,
              ec,
              h3FourierAxisDirection (h3AxisOfFin3 k),
              h3FourierAxisDirection (h3AxisOfFin3 k)
            ])
          -
        (∑ k : Fin 3,
          iteratedFDeriv ℝ 5
            (h3SpectralScalarC1Representative
              (W t i))
            x
            ![
              ea,
              eb,
              ec,
              h3FourierAxisDirection (h3AxisOfFin3 k),
              h3FourierAxisDirection (h3AxisOfFin3 k)
            ]) := by
              rw [Finset.sum_sub_distrib]

  have hCoefficient :
      (ν : ℂ) * heatTrace -
          ((ν : ℂ) * duhamelTrace + forcingThird)
        =
      (ν : ℂ) * selectedTrace - forcingThird := by
    rw [hTrace]
    ring

  have hSub' :
      HasDerivAt
        (fun r : ℝ => H r - D r)
        ((ν : ℂ) * selectedTrace - forcingThird)
        t :=
    hSub.congr_deriv hCoefficient

  have htR' : t < R := by
    simpa only [R] using htR

  have hInterior :
      Set.Ioo (0 : ℝ) R ∈ 𝓝 t :=
    IsOpen.mem_nhds isOpen_Ioo ⟨ht, htR'⟩

  have hPathEq :
      S =ᶠ[𝓝 t]
        (fun r : ℝ => H r - D r) := by
    filter_upwards [hInterior] with r hr

    have hHeatRep :=
      h3SpectralScalarHeatThirdCoordinateRepresentative_eq_iteratedFDeriv
        hν hr.1 (U₀ i) a b c x

    have hGeneric :=
      h3SelectedDuhamelC1Representative_eq_spectralScalarC1Representative
        hν U₀ hA hU₀ hr.1 i

    have hClassical :=
      h3SelectedDuhamelC1Representative_eq_C3Duhamel
        hν U₀ hA hU₀ hr.1
        (by
          simpa only [R] using hr.2.le)
        i

    dsimp only at hGeneric hClassical

    have hDuhamelFunction :
        h3SpectralScalarC1Representative
            (h3SpectralFinHeatLerayDuhamel
              ν r hν W W i)
          =
        h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
          ν r W W i := by
      dsimp only [W]
      exact hGeneric.symm.trans hClassical

    have hDuhamelOperator :=
      congrArg
        (fun f =>
          iteratedFDeriv ℝ 3 f x)
        hDuhamelFunction

    have hDuhamelEval :=
      congrArg
        (fun T => T m)
        hDuhamelOperator

    have hMildThird :=
      h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_iteratedFDeriv_three_eval_eq_heat_sub_selected
        hν U₀ hA hU₀ hr.1
        (by
          simpa only [R] using hr.2.le)
        i x
        ![
          h3FourierAxisDirection (h3AxisOfFin3 a),
          h3FourierAxisDirection (h3AxisOfFin3 b),
          h3FourierAxisDirection (h3AxisOfFin3 c)
        ]

    dsimp only [S, H, D, m, ea, eb, ec]
    rw [hHeatRep]
    rw [hDuhamelEval]
    dsimp only [W, ea, eb, ec, m] at hMildThird
    rw [hMildThird]
    ring

  have hSelected :
      HasDerivAt S
        ((ν : ℂ) * selectedTrace - forcingThird)
        t :=
    hSub'.congr_of_eventuallyEq hPathEq

  dsimp only [S, selectedTrace, forcingThird, W, ea, eb, ec, m] at hSelected ⊢
  exact hSelected

end

end Euclidean
end Bridge
end PrimeTensor
