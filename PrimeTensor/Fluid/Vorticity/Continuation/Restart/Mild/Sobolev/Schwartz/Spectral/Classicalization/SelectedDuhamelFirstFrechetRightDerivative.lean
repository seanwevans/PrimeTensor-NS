import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedDuhamelFirstFrechetRightQuotient
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Derivative.DiagonalRightDerivative

/-!
# Classicalization: selected Duhamel first-Fréchet right derivative

The preceding checkpoint closed the normalized right difference quotient of one
coordinate evaluation of the selected Duhamel first spatial Fréchet derivative:

    h⁻¹ • (Dₐ(t+h,x) - Dₐ(t,x))
      ⟶
    ν * Σₖ D³D(t,x)[eₐ,eₖ,eₖ] + DₐN(W(t),W(t))(x).

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

noncomputable local instance axisFintypeH3SelectedDuhamelFirstFrechetRightDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- At every strict positive interior restart time, one canonical coordinate
of the selected Duhamel first spatial Fréchet derivative has the expected
right time derivative. -/
theorem h3SelectedDuhamel_C1_fderiv_coordinate_hasDerivWithinAt_right
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
    HasDerivWithinAt
      (fun r : ℝ =>
        (fderiv ℝ
            (h3SpectralScalarC1Representative
              (h3SpectralFinHeatLerayDuhamel
                ν r hν W W i))
            x) ea)
      ((ν : ℂ) *
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
        +
      (fderiv ℝ
          (h3RawFinLerayOuterProductDivergenceC0Representative
            (W t) (W t) i)
          x) ea)
      (Set.Ioi t)
      t := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let ea : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 a)

  let D : ℝ → ℂ :=
    fun r =>
      (fderiv ℝ
          (h3SpectralScalarC1Representative
            (h3SpectralFinHeatLerayDuhamel
              ν r hν W W i))
          x) ea

  let G : ℂ :=
    (ν : ℂ) *
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
      +
    (fderiv ℝ
        (h3RawFinLerayOuterProductDivergenceC0Representative
          (W t) (W t) i)
        x) ea

  have hQ :=
    tendsto_inv_smul_sub_h3SelectedDuhamel_C1_fderiv_coordinate_zero_right
      hν U₀ hA hU₀ ht htR i a x

  have hQt :
      Tendsto
        (fun h : ℝ =>
          h⁻¹ • (D (t + h) - D t))
        (𝓝[Set.Ioi (0 : ℝ)] 0)
        (𝓝 G) := by
    dsimp only [D, G, W, ea]
    exact hQ

  have hDeriv :
      HasDerivWithinAt D G (Set.Ioi t) t :=
    hasDerivWithinAt_Ioi_of_tendsto_slope_zero_right hQt

  dsimp only [D, G, W, ea] at hDeriv ⊢
  exact hDeriv

end

end Euclidean
end Bridge
end PrimeTensor
