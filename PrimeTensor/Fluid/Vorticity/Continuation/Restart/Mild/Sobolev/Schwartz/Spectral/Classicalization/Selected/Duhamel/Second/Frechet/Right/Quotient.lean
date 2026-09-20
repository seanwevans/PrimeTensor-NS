import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Second.Frechet.History.Generator.Trace
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Second.Frechet.Fresh.Spectral.Quotient
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Second.Frechet.Right.Quotient.Split

/-!
# Classicalization: selected Duhamel second-Fréchet right quotient

Both pieces of the selected Duhamel second spatial Fréchet right quotient are
now closed separately.

The old-history quotient converges to

    ν * Σ_k D⁴D(t,x)[e_a,e_b,e_k,e_k],

while the actual shifted spectral fresh quotient converges to

    D²N(W(t),W(t))(x)[e_a,e_b].

The exact positive-increment second-Fréchet quotient split identifies the full
difference quotient with the sum of those two terms.  Near zero on the right,
`t + h` remains inside the restart interval, so the split applies eventually.

Adding the two `Tendsto` statements therefore closes the complete selected
Duhamel second-Fréchet right-quotient limit.

No new estimate or reconstruction argument is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelSecondFrechetRightQuotient
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- The complete selected Duhamel second spatial Fréchet difference quotient
converges from the right to viscosity times the fourth spatial trace plus the
instantaneous forcing Hessian coordinate. -/
theorem tendsto_inv_smul_sub_h3SelectedDuhamel_C1_secondFrechet_coordinate_zero_right
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
    Tendsto
      (fun h : ℝ =>
        h⁻¹ •
          (iteratedFDeriv ℝ 2
              (h3SpectralScalarC1Representative
                (h3SpectralFinHeatLerayDuhamel
                  ν (t + h) hν W W i))
              x m
            -
          iteratedFDeriv ℝ 2
              (h3SpectralScalarC1Representative
                (h3SpectralFinHeatLerayDuhamel
                  ν t hν W W i))
              x m))
      (𝓝[Set.Ioi (0 : ℝ)] 0)
      (𝓝
        ((ν : ℂ) *
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
          +
        iteratedFDeriv ℝ 2
          (h3RawFinLerayOuterProductDivergenceC0Representative
            (W t) (W t) i)
          x m)) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let ea : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 a)

  let eb : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 b)

  let m : Fin 2 → H3FourierPoint3 :=
    ![ea, eb]

  have hHistory :=
    tendsto_inv_smul_sub_h3SelectedDuhamelHistoryHeat_secondFrechet_coordinate_zero_right_eq_viscosity_fourthTrace
      hν U₀ hA hU₀ ht htR.le i a b x

  have hFresh :=
    tendsto_inv_smul_h3SelectedDuhamelFresh_secondFrechet_coordinate_zero_right
      hν U₀ hA hU₀ ht htR i a b x

  dsimp only at hHistory hFresh

  have hSum :=
    hHistory.add hFresh

  have hGap :
      0 <
        h3FinHeatLerayRestartRadius ν A - t := by
    linarith

  have hSmall :
      Set.Iio
          (h3FinHeatLerayRestartRadius ν A - t)
        ∈
      (𝓝[Set.Ioi (0 : ℝ)] 0) := by
    exact
      mem_inf_of_left
        (Iio_mem_nhds hGap)

  have hEq :
      (fun h : ℝ =>
        h⁻¹ •
          (iteratedFDeriv ℝ 2
              (h3SpectralScalarC1Representative
                (h3SpectralFinHeatLerayDuhamel
                  ν (t + h) hν W W i))
              x m
            -
          iteratedFDeriv ℝ 2
              (h3SpectralScalarC1Representative
                (h3SpectralFinHeatLerayDuhamel
                  ν t hν W W i))
              x m))
        =ᶠ[𝓝[Set.Ioi (0 : ℝ)] 0]
      (fun h : ℝ =>
        h⁻¹ •
            (iteratedFDeriv ℝ 2
                (h3SelectedDuhamelHistoryHeatRepresentative
                  ν A t h hν U₀ hA hU₀ ht i)
                x m
              -
            iteratedFDeriv ℝ 2
                (h3SpectralScalarC1Representative
                  (h3SpectralFinHeatLerayDuhamel
                    ν t hν W W i))
                x m)
          +
        h⁻¹ •
          iteratedFDeriv ℝ 2
            (h3SpectralScalarC1Representative
              (h3SpectralFinHeatLerayDuhamel
                ν h hν
                (fun r => W (r + t))
                (fun r => W (r + t))
                i))
            x m) := by
    filter_upwards
      [self_mem_nhdsWithin, hSmall]
      with h hh hsmall

    have hthR :
        t + h ≤
          h3FinHeatLerayRestartRadius ν A := by
      change
        h <
          h3FinHeatLerayRestartRadius ν A - t
        at hsmall
      linarith

    dsimp only [W, ea, eb, m]

    exact
      inv_smul_sub_h3SelectedDuhamel_secondFrechet_coordinate_eq_history_add_fresh
        hν U₀ hA hU₀ ht hh hthR i a b x

  exact
    Tendsto.congr'
      hEq.symm
      hSum

end

end Euclidean
end Bridge
end PrimeTensor
