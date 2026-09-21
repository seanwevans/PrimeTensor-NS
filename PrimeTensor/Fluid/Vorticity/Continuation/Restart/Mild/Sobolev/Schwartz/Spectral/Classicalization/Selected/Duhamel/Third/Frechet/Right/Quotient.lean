import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Third.Frechet.History.Generator.Trace
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Third.Frechet.Fresh.Spectral.Quotient
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Third.Frechet.Right.Quotient.Split

/-!
# Classicalization: selected Duhamel third-Fréchet right quotient

Both pieces of the selected Duhamel third spatial Fréchet right quotient are
now closed separately.

The old-history quotient converges to

    ν * Σ_k D⁵D(t,x)[e_a,e_b,e_c,e_k,e_k],

while the actual shifted spectral fresh quotient converges to

    D³N(W(t),W(t))(x)[e_a,e_b,e_c].

The exact positive-increment third-Fréchet quotient split identifies the full
difference quotient with the sum of those two terms.  Near zero on the right,
`t + h` remains inside the restart interval, so the split applies eventually.

Adding the two `Tendsto` statements therefore closes the complete selected
Duhamel third-Fréchet right-quotient limit.

No new estimate or reconstruction argument is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelThirdFrechetRightQuotient
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- The complete selected Duhamel third spatial Fréchet difference quotient
converges from the right to viscosity times the fifth spatial trace plus the
instantaneous forcing third-coordinate derivative. -/
theorem tendsto_inv_smul_sub_h3SelectedDuhamel_C1_thirdFrechet_coordinate_zero_right
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
    Tendsto
      (fun h : ℝ =>
        h⁻¹ •
          (iteratedFDeriv ℝ 3
              (h3SpectralScalarC1Representative
                (h3SpectralFinHeatLerayDuhamel
                  ν (t + h) hν W W i))
              x m
            -
          iteratedFDeriv ℝ 3
              (h3SpectralScalarC1Representative
                (h3SpectralFinHeatLerayDuhamel
                  ν t hν W W i))
              x m))
      (𝓝[Set.Ioi (0 : ℝ)] 0)
      (𝓝
        ((ν : ℂ) *
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
          +
        iteratedFDeriv ℝ 3
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

  let ec : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 c)

  let m : Fin 3 → H3FourierPoint3 :=
    ![ea, eb, ec]

  have hHistory :=
    tendsto_inv_smul_sub_h3SelectedDuhamelHistoryHeat_thirdFrechet_coordinate_zero_right_eq_viscosity_fifthTrace
      hν U₀ hA hU₀ ht htR.le i a b c x

  have hFresh :=
    tendsto_inv_smul_h3SelectedDuhamelFresh_thirdFrechet_coordinate_zero_right
      hν U₀ hA hU₀ ht htR i a b c x

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
          (iteratedFDeriv ℝ 3
              (h3SpectralScalarC1Representative
                (h3SpectralFinHeatLerayDuhamel
                  ν (t + h) hν W W i))
              x m
            -
          iteratedFDeriv ℝ 3
              (h3SpectralScalarC1Representative
                (h3SpectralFinHeatLerayDuhamel
                  ν t hν W W i))
              x m))
        =ᶠ[𝓝[Set.Ioi (0 : ℝ)] 0]
      (fun h : ℝ =>
        h⁻¹ •
            (iteratedFDeriv ℝ 3
                (h3SelectedDuhamelHistoryHeatRepresentative
                  ν A t h hν U₀ hA hU₀ ht i)
                x m
              -
            iteratedFDeriv ℝ 3
                (h3SpectralScalarC1Representative
                  (h3SpectralFinHeatLerayDuhamel
                    ν t hν W W i))
                x m)
          +
        h⁻¹ •
          iteratedFDeriv ℝ 3
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

    dsimp only [W, ea, eb, ec, m]

    exact
      inv_smul_sub_h3SelectedDuhamel_thirdFrechet_coordinate_eq_history_add_fresh
        hν U₀ hA hU₀ ht hh hthR i a b c x

  exact
    Tendsto.congr'
      hEq.symm
      hSum

end

end Euclidean
end Bridge
end PrimeTensor
