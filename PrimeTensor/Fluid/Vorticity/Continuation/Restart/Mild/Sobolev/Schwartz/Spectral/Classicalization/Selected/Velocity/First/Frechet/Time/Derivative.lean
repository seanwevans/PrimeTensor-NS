import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Time.First.Coordinate.Time.Derivative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.First.Frechet.Ordinary.Time.Derivative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Third.Frechet.Mild

/-!
# Classicalization: ordinary time derivative of the selected first Fréchet derivative

The positive-time heat first-coordinate derivative and the selected Duhamel
first-coordinate derivative now both have ordinary time derivatives.

On the open restart interval, the pointwise mild identity gives

    D_a u = D_a H - D_a Duhamel.

Subtracting the two already-compiled time derivatives therefore differentiates
`D_a u` in time.  Its raw coefficient is

    ν tr_a(D³H) - (ν tr_a(D³Duhamel) + D_a N).

The selected third-Fréchet mild identity says

    D³Duhamel = D³H - D³u.

After summing the three diagonal coordinate evaluations, the heat terms cancel
and the coefficient becomes

    ν tr_a(D³u) - D_a N.

This is the complex spectral mixed-derivative candidate.  No new estimate,
limit, or derivative interchange is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedVelocityFirstFrechetTimeDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- At every strict positive interior restart time, one coordinate evaluation
of the selected velocity first spatial Fréchet derivative has an ordinary time
derivative equal to viscosity times the selected third spatial trace minus the
instantaneous forcing coordinate derivative. -/
theorem h3SelectedVelocity_C1_fderiv_coordinate_hasDerivAt_time
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i a : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let ea : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 a)
    HasDerivAt
      (fun r : ℝ =>
        (fderiv ℝ
            (h3SpectralScalarC1Representative
              (W r i))
            x) ea)
      ((ν : ℂ) *
          (∑ k : Fin 3,
            iteratedFDeriv ℝ 3
              (h3SpectralScalarC1Representative
                (W t i))
              x
              ![
                ea,
                h3FourierAxisDirection (h3AxisOfFin3 k),
                h3FourierAxisDirection (h3AxisOfFin3 k)
              ])
        -
      (fderiv ℝ
          (h3RawFinLerayOuterProductDivergenceC0Representative
            (W t) (W t) i)
          x) ea)
      t := by
  dsimp only

  let R : ℝ :=
    h3FinHeatLerayRestartRadius ν A

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let ea : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 a)

  let H : ℝ → ℂ :=
    fun r =>
      h3SpectralScalarHeatFirstCoordinateRepresentative
        ν r (U₀ i) a x

  let D : ℝ → ℂ :=
    fun r =>
      (fderiv ℝ
          (h3SpectralScalarC1Representative
            (h3SpectralFinHeatLerayDuhamel
              ν r hν W W i))
          x) ea

  let S : ℝ → ℂ :=
    fun r =>
      (fderiv ℝ
          (h3SpectralScalarC1Representative
            (W r i))
          x) ea

  let heatTrace : ℂ :=
    (∑ k : Fin 3,
      iteratedFDeriv ℝ 3
        (h3SpectralScalarHeatC3Representative
          ν t (U₀ i))
        x
        ![
          ea,
          h3FourierAxisDirection (h3AxisOfFin3 k),
          h3FourierAxisDirection (h3AxisOfFin3 k)
        ])

  let duhamelTrace : ℂ :=
    (∑ k : Fin 3,
      iteratedFDeriv ℝ 3
        (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
          ν t W W i)
        x
        ![
          ea,
          h3FourierAxisDirection (h3AxisOfFin3 k),
          h3FourierAxisDirection (h3AxisOfFin3 k)
        ])

  let selectedTrace : ℂ :=
    (∑ k : Fin 3,
      iteratedFDeriv ℝ 3
        (h3SpectralScalarC1Representative
          (W t i))
        x
        ![
          ea,
          h3FourierAxisDirection (h3AxisOfFin3 k),
          h3FourierAxisDirection (h3AxisOfFin3 k)
        ])

  let forcingDerivative : ℂ :=
    (fderiv ℝ
        (h3RawFinLerayOuterProductDivergenceC0Representative
          (W t) (W t) i)
        x) ea

  have hHeat :
      HasDerivAt H
        ((ν : ℂ) * heatTrace)
        t := by
    dsimp only [H, heatTrace, ea]
    exact
      h3SpectralScalarHeatFirstCoordinateRepresentative_hasDerivAt_time_eq_viscosity_thirdTrace
        hν ht (U₀ i) a x

  have hDuhamel :
      HasDerivAt D
        ((ν : ℂ) * duhamelTrace + forcingDerivative)
        t := by
    dsimp only [D, duhamelTrace, forcingDerivative, W, ea]
    exact
      h3SelectedDuhamel_C1_fderiv_coordinate_hasDerivAt_time
        hν U₀ hA hU₀ ht htR i a x

  have hSub :
      HasDerivAt
        (fun r : ℝ => H r - D r)
        ((ν : ℂ) * heatTrace -
          ((ν : ℂ) * duhamelTrace + forcingDerivative))
        t :=
    hHeat.sub hDuhamel

  have hThird
      (k : Fin 3) :
      iteratedFDeriv ℝ 3
          (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
            ν t W W i)
          x
          ![
            ea,
            h3FourierAxisDirection (h3AxisOfFin3 k),
            h3FourierAxisDirection (h3AxisOfFin3 k)
          ]
        =
      iteratedFDeriv ℝ 3
          (h3SpectralScalarHeatC3Representative
            ν t (U₀ i))
          x
          ![
            ea,
            h3FourierAxisDirection (h3AxisOfFin3 k),
            h3FourierAxisDirection (h3AxisOfFin3 k)
          ]
        -
      iteratedFDeriv ℝ 3
          (h3SpectralScalarC1Representative
            (W t i))
          x
          ![
            ea,
            h3FourierAxisDirection (h3AxisOfFin3 k),
            h3FourierAxisDirection (h3AxisOfFin3 k)
          ] := by
    dsimp only [W, ea]
    exact
      h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_iteratedFDeriv_three_eval_eq_heat_sub_selected
        hν U₀ hA hU₀ ht htR.le i x
        ![
          h3FourierAxisDirection (h3AxisOfFin3 a),
          h3FourierAxisDirection (h3AxisOfFin3 k),
          h3FourierAxisDirection (h3AxisOfFin3 k)
        ]

  have hTrace :
      duhamelTrace = heatTrace - selectedTrace := by
    dsimp only [duhamelTrace, heatTrace, selectedTrace]
    calc
      (∑ k : Fin 3,
        iteratedFDeriv ℝ 3
          (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
            ν t W W i)
          x
          ![
            ea,
            h3FourierAxisDirection (h3AxisOfFin3 k),
            h3FourierAxisDirection (h3AxisOfFin3 k)
          ])
          =
        ∑ k : Fin 3,
          (iteratedFDeriv ℝ 3
              (h3SpectralScalarHeatC3Representative
                ν t (U₀ i))
              x
              ![
                ea,
                h3FourierAxisDirection (h3AxisOfFin3 k),
                h3FourierAxisDirection (h3AxisOfFin3 k)
              ]
            -
          iteratedFDeriv ℝ 3
              (h3SpectralScalarC1Representative
                (W t i))
              x
              ![
                ea,
                h3FourierAxisDirection (h3AxisOfFin3 k),
                h3FourierAxisDirection (h3AxisOfFin3 k)
              ]) := by
            apply Finset.sum_congr rfl
            intro k hk
            exact hThird k
      _ =
        (∑ k : Fin 3,
          iteratedFDeriv ℝ 3
            (h3SpectralScalarHeatC3Representative
              ν t (U₀ i))
            x
            ![
              ea,
              h3FourierAxisDirection (h3AxisOfFin3 k),
              h3FourierAxisDirection (h3AxisOfFin3 k)
            ])
          -
        (∑ k : Fin 3,
          iteratedFDeriv ℝ 3
            (h3SpectralScalarC1Representative
              (W t i))
            x
            ![
              ea,
              h3FourierAxisDirection (h3AxisOfFin3 k),
              h3FourierAxisDirection (h3AxisOfFin3 k)
            ]) := by
              rw [Finset.sum_sub_distrib]

  have hCoefficient :
      (ν : ℂ) * heatTrace -
          ((ν : ℂ) * duhamelTrace + forcingDerivative)
        =
      (ν : ℂ) * selectedTrace - forcingDerivative := by
    rw [hTrace]
    ring

  have hSub' :
      HasDerivAt
        (fun r : ℝ => H r - D r)
        ((ν : ℂ) * selectedTrace - forcingDerivative)
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

    have hMild :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_mild_at
        hν U₀ hA hU₀ hr.1
        (by
          simpa only [R] using hr.2.le)
        i

    have hGeneric :=
      h3SelectedDuhamelC1Representative_eq_spectralScalarC1Representative
        hν U₀ hA hU₀ hr.1 i

    have hClassical :=
      h3SelectedDuhamelC1Representative_eq_C3Duhamel
        hν U₀ hA hU₀ hr.1
        (by
          simpa only [R] using hr.2.le)
        i

    dsimp only at hMild hGeneric hClassical

    have hDuhamelRep :
        h3SpectralScalarC1Representative
            (h3SpectralFinHeatLerayDuhamel
              ν r hν W W i)
          =
        h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
          ν r W W i := by
      dsimp only [W]
      exact hGeneric.symm.trans hClassical

    rw [← hDuhamelRep] at hMild

    have hHeatDiff :
        DifferentiableAt ℝ
          (h3SpectralScalarHeatC3Representative
            ν r (U₀ i))
          x :=
      ((h3SpectralScalarHeatC3Representative_contDiff_three
        hν hr.1 (U₀ i)).of_le (by norm_num)).differentiable_one.differentiableAt

    have hDuhamelDiff :
        DifferentiableAt ℝ
          (h3SpectralScalarC1Representative
            (h3SpectralFinHeatLerayDuhamel
              ν r hν W W i))
          x :=
      (h3SpectralScalarC1Representative_contDiff_one
        (h3SpectralFinHeatLerayDuhamel
          ν r hν W W i)).differentiable_one.differentiableAt

    have hF :=
      congrArg
        (fun f : H3FourierPoint3 → ℂ =>
          (fderiv ℝ f x) ea)
        hMild

    change
      (fderiv ℝ
          (h3SpectralScalarC1Representative
            (W r i))
          x) ea
        =
      (fderiv ℝ
          (fun y : H3FourierPoint3 =>
            h3SpectralScalarHeatC3Representative
                ν r (U₀ i) y
              -
            h3SpectralScalarC1Representative
                (h3SpectralFinHeatLerayDuhamel
                  ν r hν W W i) y)
          x) ea
      at hF

    rw [fderiv_fun_sub hHeatDiff hDuhamelDiff] at hF

    have hHeatRep :=
      h3SpectralScalarHeatFirstCoordinateRepresentative_eq_fderiv
        hν hr.1 (U₀ i) a x

    dsimp only [S, H, D]
    rw [hHeatRep]
    exact hF

  have hSelected :
      HasDerivAt S
        ((ν : ℂ) * selectedTrace - forcingDerivative)
        t :=
    hSub'.congr_of_eventuallyEq hPathEq

  dsimp only [S, selectedTrace, forcingDerivative, W, ea] at hSelected ⊢
  exact hSelected

end

end Euclidean
end Bridge
end PrimeTensor
