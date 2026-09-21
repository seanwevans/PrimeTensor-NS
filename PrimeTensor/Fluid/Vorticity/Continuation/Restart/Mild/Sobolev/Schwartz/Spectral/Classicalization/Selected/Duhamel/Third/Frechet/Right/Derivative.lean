import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Third.Frechet.Right.Quotient
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Derivative.Diagonal.Right.Derivative

/-!
# Classicalization: selected Duhamel third-Fréchet right derivative

The preceding checkpoint closed the normalized right difference quotient of one
ordered coordinate evaluation of the selected Duhamel third spatial Fréchet
derivative:

    h⁻¹ • (D³D(t+h,x)[e_a,e_b,e_c] - D³D(t,x)[e_a,e_b,e_c])
      ⟶
    ν * Σ_k D⁵D(t,x)[e_a,e_b,e_c,e_k,e_k]
      + D³N(W(t),W(t))(x)[e_a,e_b,e_c].

`DiagonalRightDerivative` already contains the generic conversion from exactly
this zero-right quotient form to Mathlib's

    HasDerivWithinAt ... (Ioi t) t.

This file applies that conversion and introduces no new estimate, limit, or
reconstruction argument.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelThirdFrechetRightDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- At every strict positive interior restart time, one ordered canonical
coordinate of the selected Duhamel third spatial Fréchet derivative has the
expected right time derivative. -/
theorem h3SelectedDuhamel_C1_thirdFrechet_coordinate_hasDerivWithinAt_right
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
    HasDerivWithinAt
      (fun r : ℝ =>
        iteratedFDeriv ℝ 3
          (h3SpectralScalarC1Representative
            (h3SpectralFinHeatLerayDuhamel
              ν r hν W W i))
          x m)
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
        x m)
      (Set.Ioi t)
      t := by
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

  let D : ℝ → ℂ :=
    fun r =>
      iteratedFDeriv ℝ 3
        (h3SpectralScalarC1Representative
          (h3SpectralFinHeatLerayDuhamel
            ν r hν W W i))
        x m

  let G : ℂ :=
    (ν : ℂ) *
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
      x m

  have hQ :=
    tendsto_inv_smul_sub_h3SelectedDuhamel_C1_thirdFrechet_coordinate_zero_right
      hν U₀ hA hU₀ ht htR i a b c x

  have hQt :
      Tendsto
        (fun h : ℝ =>
          h⁻¹ • (D (t + h) - D t))
        (𝓝[Set.Ioi (0 : ℝ)] 0)
        (𝓝 G) := by
    dsimp only [D, G, W, ea, eb, ec, m]
    exact hQ

  have hDeriv :
      HasDerivWithinAt D G (Set.Ioi t) t :=
    hasDerivWithinAt_Ioi_of_tendsto_slope_zero_right hQt

  dsimp only [D, G, W, ea, eb, ec, m] at hDeriv ⊢
  exact hDeriv

end

end Euclidean
end Bridge
end PrimeTensor
