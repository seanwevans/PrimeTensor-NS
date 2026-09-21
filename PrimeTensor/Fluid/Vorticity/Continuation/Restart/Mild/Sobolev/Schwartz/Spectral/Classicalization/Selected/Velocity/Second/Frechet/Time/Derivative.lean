import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Time.Second.Coordinate.Generator.Trace
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Second.Frechet.Ordinary.Time.Derivative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Fourth.Frechet.Mild

/-!
# Classicalization: ordinary time derivative of the selected second Fréchet derivative

The positive-time heat Hessian coordinate and the selected Duhamel Hessian
coordinate now both have ordinary time derivatives.

On the open restart interval the twice-spatially differentiated mild identity
gives

    D²u = D²Heat - D²Duhamel.

Subtracting the two compiled temporal derivatives yields the raw coefficient

    ν * tr_ab(D⁴Heat)
      - (ν * tr_ab(D⁴Duhamel) + D²N_ab).

The selected fourth-Fréchet mild identity gives

    D⁴Duhamel = D⁴Heat - D⁴u.

After summing the three diagonal fourth-order coordinates, the heat terms
cancel and the coefficient becomes

    ν * tr_ab(D⁴u) - D²N_ab.

Thus each fixed ordered coordinate evaluation of the selected second spatial
Fréchet derivative has an ordinary time derivative equal to the exact
order-two spatial derivative of the selected temporal PDE candidate.

No new estimate, limit, or time/space interchange theorem is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedVelocitySecondFrechetTimeDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- At every strict positive interior restart time, one ordered canonical
coordinate evaluation of the selected velocity second spatial Fréchet
derivative has an ordinary time derivative equal to viscosity times the
selected fourth spatial trace minus the instantaneous forcing Hessian
coordinate. -/
theorem h3SelectedVelocity_C1_secondFrechet_coordinate_hasDerivAt_time
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i a b : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let ea : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 a)
    let eb : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 b)
    let m : Fin 2 → H3FourierPoint3 :=
      ![ea, eb]
    HasDerivAt
      (fun r : ℝ =>
        iteratedFDeriv ℝ 2
          (h3SpectralScalarC1Representative
            (W r i))
          x m)
      ((ν : ℂ) *
          (∑ k : Fin 3,
            iteratedFDeriv ℝ 4
              (h3SpectralScalarC1Representative
                (W t i))
              x
              ![
                ea,
                eb,
                h3FourierAxisDirection (h3AxisOfFin3 k),
                h3FourierAxisDirection (h3AxisOfFin3 k)
              ])
        -
      iteratedFDeriv ℝ 2
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

  let m : Fin 2 → H3FourierPoint3 :=
    ![ea, eb]

  let H : ℝ → ℂ :=
    fun r =>
      h3SpectralScalarHeatSecondCoordinateRepresentative
        ν r (U₀ i) a b x

  let D : ℝ → ℂ :=
    fun r =>
      iteratedFDeriv ℝ 2
        (h3SpectralScalarC1Representative
          (h3SpectralFinHeatLerayDuhamel
            ν r hν W W i))
        x m

  let S : ℝ → ℂ :=
    fun r =>
      iteratedFDeriv ℝ 2
        (h3SpectralScalarC1Representative
          (W r i))
        x m

  let heatTrace : ℂ :=
    ∑ k : Fin 3,
      iteratedFDeriv ℝ 4
        (h3SpectralScalarHeatC3Representative
          ν t (U₀ i))
        x
        ![
          ea,
          eb,
          h3FourierAxisDirection (h3AxisOfFin3 k),
          h3FourierAxisDirection (h3AxisOfFin3 k)
        ]

  let duhamelTrace : ℂ :=
    ∑ k : Fin 3,
      iteratedFDeriv ℝ 4
        (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
          ν t W W i)
        x
        ![
          ea,
          eb,
          h3FourierAxisDirection (h3AxisOfFin3 k),
          h3FourierAxisDirection (h3AxisOfFin3 k)
        ]

  let selectedTrace : ℂ :=
    ∑ k : Fin 3,
      iteratedFDeriv ℝ 4
        (h3SpectralScalarC1Representative
          (W t i))
        x
        ![
          ea,
          eb,
          h3FourierAxisDirection (h3AxisOfFin3 k),
          h3FourierAxisDirection (h3AxisOfFin3 k)
        ]

  let forcingSecond : ℂ :=
    iteratedFDeriv ℝ 2
      (h3RawFinLerayOuterProductDivergenceC0Representative
        (W t) (W t) i)
      x m

  have hHeat :
      HasDerivAt H
        ((ν : ℂ) * heatTrace)
        t := by
    dsimp only [H, heatTrace, ea, eb]
    exact
      h3SpectralScalarHeatSecondCoordinateRepresentative_hasDerivAt_time_eq_viscosity_fourthTrace
        hν ht (U₀ i) a b x

  have hDuhamel :
      HasDerivAt D
        ((ν : ℂ) * duhamelTrace + forcingSecond)
        t := by
    dsimp only [D, duhamelTrace, forcingSecond, W, ea, eb, m]
    exact
      h3SelectedDuhamel_C1_secondFrechet_coordinate_hasDerivAt_time
        hν U₀ hA hU₀ ht htR i a b x

  have hSub :
      HasDerivAt
        (fun r : ℝ => H r - D r)
        ((ν : ℂ) * heatTrace -
          ((ν : ℂ) * duhamelTrace + forcingSecond))
        t :=
    hHeat.sub hDuhamel

  have hFourth
      (k : Fin 3) :
      iteratedFDeriv ℝ 4
          (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
            ν t W W i)
          x
          ![
            ea,
            eb,
            h3FourierAxisDirection (h3AxisOfFin3 k),
            h3FourierAxisDirection (h3AxisOfFin3 k)
          ]
        =
      iteratedFDeriv ℝ 4
          (h3SpectralScalarHeatC3Representative
            ν t (U₀ i))
          x
          ![
            ea,
            eb,
            h3FourierAxisDirection (h3AxisOfFin3 k),
            h3FourierAxisDirection (h3AxisOfFin3 k)
          ]
        -
      iteratedFDeriv ℝ 4
          (h3SpectralScalarC1Representative
            (W t i))
          x
          ![
            ea,
            eb,
            h3FourierAxisDirection (h3AxisOfFin3 k),
            h3FourierAxisDirection (h3AxisOfFin3 k)
          ] := by
    dsimp only [W, ea, eb]
    exact
      h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_iteratedFDeriv_four_eval_eq_heat_sub_selected
        hν U₀ hA hU₀ ht htR.le i x
        ![
          h3FourierAxisDirection (h3AxisOfFin3 a),
          h3FourierAxisDirection (h3AxisOfFin3 b),
          h3FourierAxisDirection (h3AxisOfFin3 k),
          h3FourierAxisDirection (h3AxisOfFin3 k)
        ]

  have hTrace :
      duhamelTrace = heatTrace - selectedTrace := by
    dsimp only [duhamelTrace, heatTrace, selectedTrace]
    calc
      (∑ k : Fin 3,
        iteratedFDeriv ℝ 4
          (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
            ν t W W i)
          x
          ![
            ea,
            eb,
            h3FourierAxisDirection (h3AxisOfFin3 k),
            h3FourierAxisDirection (h3AxisOfFin3 k)
          ])
          =
        ∑ k : Fin 3,
          (iteratedFDeriv ℝ 4
              (h3SpectralScalarHeatC3Representative
                ν t (U₀ i))
              x
              ![
                ea,
                eb,
                h3FourierAxisDirection (h3AxisOfFin3 k),
                h3FourierAxisDirection (h3AxisOfFin3 k)
              ]
            -
          iteratedFDeriv ℝ 4
              (h3SpectralScalarC1Representative
                (W t i))
              x
              ![
                ea,
                eb,
                h3FourierAxisDirection (h3AxisOfFin3 k),
                h3FourierAxisDirection (h3AxisOfFin3 k)
              ]) := by
            apply Finset.sum_congr rfl
            intro k hk
            exact hFourth k
      _ =
        (∑ k : Fin 3,
          iteratedFDeriv ℝ 4
            (h3SpectralScalarHeatC3Representative
              ν t (U₀ i))
            x
            ![
              ea,
              eb,
              h3FourierAxisDirection (h3AxisOfFin3 k),
              h3FourierAxisDirection (h3AxisOfFin3 k)
            ])
          -
        (∑ k : Fin 3,
          iteratedFDeriv ℝ 4
            (h3SpectralScalarC1Representative
              (W t i))
            x
            ![
              ea,
              eb,
              h3FourierAxisDirection (h3AxisOfFin3 k),
              h3FourierAxisDirection (h3AxisOfFin3 k)
            ]) := by
              rw [Finset.sum_sub_distrib]

  have hCoefficient :
      (ν : ℂ) * heatTrace -
          ((ν : ℂ) * duhamelTrace + forcingSecond)
        =
      (ν : ℂ) * selectedTrace - forcingSecond := by
    rw [hTrace]
    ring

  have hSub' :
      HasDerivAt
        (fun r : ℝ => H r - D r)
        ((ν : ℂ) * selectedTrace - forcingSecond)
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
      h3SpectralScalarHeatSecondCoordinateRepresentative_eq_iteratedFDeriv
        hν hr.1 (U₀ i) a b x

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
          iteratedFDeriv ℝ 2 f x)
        hDuhamelFunction

    have hDuhamelEval :=
      congrArg
        (fun T => T m)
        hDuhamelOperator

    have hMildSecond :=
      h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_iteratedFDeriv_two_coordinate_eval_eq_heat_sub_selected
        hν U₀ hA hU₀ hr.1
        (by
          simpa only [R] using hr.2.le)
        i a b x

    dsimp only [S, H, D, m, ea, eb]
    rw [hHeatRep]
    rw [hDuhamelEval]
    dsimp only [W, ea, eb, m] at hMildSecond
    rw [hMildSecond]
    ring

  have hSelected :
      HasDerivAt S
        ((ν : ℂ) * selectedTrace - forcingSecond)
        t :=
    hSub'.congr_of_eventuallyEq hPathEq

  dsimp only [S, selectedTrace, forcingSecond, W, ea, eb, m] at hSelected ⊢
  exact hSelected

end

end Euclidean
end Bridge
end PrimeTensor
