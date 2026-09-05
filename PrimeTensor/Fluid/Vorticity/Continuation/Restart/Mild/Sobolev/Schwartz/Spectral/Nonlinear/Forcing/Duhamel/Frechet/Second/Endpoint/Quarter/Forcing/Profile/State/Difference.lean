import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.Profile.Frozen.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.Profile.State.Variation

/-!
# Same-lag state variation of the scalar second-moment profile

At a fixed positive heat lag, `ProfileStateVariation` controls the Fourier-L¹
second moment of the complex forcing difference.  This file transfers that
bound through the scalar norm integral:

    | ∫ |ξ|² |H_a N(U,U)| - ∫ |ξ|² |H_a N(V,V)| |
      <= ∫ |ξ|² |H_a (N(U,U)-N(V,V))|.

The right-hand side is already bounded quantitatively by the H³ state
difference.  This is the state-variation half of continuity of the selected
source-time profile.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3SchwartzQuarterForcingProfileStateDifference
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The fixed-lag second-moment integrand of the diagonal forcing difference is
integrable. -/
theorem h3RawFinLerayOuterProductDivergenceHeat_diagonalDifference_secondMoment_integrable
    {ν a : ℝ}
    (hν : 0 < ν)
    (ha : 0 < a)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ 2 *
          ‖h3HeatFourierSymbol ν a ξ *
            (h3RawFinLerayOuterProductDivergence U U i ξ -
              h3RawFinLerayOuterProductDivergence V V i ξ)‖)
      (volume : Measure H3FourierPoint3) := by
  let C : ℝ := (Real.sqrt (ν * (a / 3)))⁻¹
  let D : H3FourierPoint3 → ℂ := fun ξ =>
    h3RawFinLerayOuterProductDivergence U U i ξ -
      h3RawFinLerayOuterProductDivergence V V i ξ

  have hD :
      Integrable D (volume : Measure H3FourierPoint3) := by
    dsimp only [D]
    exact
      (h3RawFinLerayOuterProductDivergence_integrable U U i).sub
        (h3RawFinLerayOuterProductDivergence_integrable V V i)

  have hMajorant :
      Integrable
        (fun ξ : H3FourierPoint3 => C ^ 2 * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hD.norm.const_mul (C ^ 2)

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν a ξ * D ξ‖)
        (volume : Measure H3FourierPoint3) := by
    exact
      ((continuous_norm.pow 2).aestronglyMeasurable).mul
        ((continuous_h3HeatFourierSymbol ν a).aestronglyMeasurable.mul
          hD.aestronglyMeasurable).norm

  refine hMajorant.mono' hTargetMeas ?_
  filter_upwards with ξ

  have hMoment :=
    h3HeatFourierMomentMultiplier_le_three
      hν ha 2 (by norm_num) ξ

  have hnonneg :
      0 ≤
        ‖ξ‖ ^ 2 *
          ‖h3HeatFourierSymbol ν a ξ * D ξ‖ := by
    positivity

  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  rw [norm_mul]

  calc
    ‖ξ‖ ^ 2 *
        (‖h3HeatFourierSymbol ν a ξ‖ * ‖D ξ‖)
        =
      (‖ξ‖ ^ 2 * ‖h3HeatFourierSymbol ν a ξ‖) * ‖D ξ‖ := by
      ring
    _ ≤ C ^ 2 * ‖D ξ‖ := by
      exact
        mul_le_mul_of_nonneg_right
          hMoment
          (norm_nonneg (D ξ))

/-- Same-lag scalar profile difference controlled by the quantitative
second-moment forcing state-variation estimate. -/
theorem abs_h3NonlinearForcingHeatSecondMomentFrozenProfile_sub_le_stateDifference
    {ν a : ℝ}
    (hν : 0 < ν)
    (ha : 0 < a)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    |h3NonlinearForcingHeatSecondMomentFrozenProfile ν U i a -
        h3NonlinearForcingHeatSecondMomentFrozenProfile ν V i a|
      ≤
    ((Real.sqrt (ν * (a / 3)))⁻¹) ^ 2 *
      (h3NonlinearForcingL1Coefficient * ‖U - V‖ * ‖U‖ +
        h3NonlinearForcingL1Coefficient * ‖V‖ * ‖U - V‖) := by
  let fU : H3FourierPoint3 → ℝ := fun ξ =>
    ‖ξ‖ ^ 2 *
      ‖h3HeatFourierSymbol ν a ξ *
        h3RawFinLerayOuterProductDivergence U U i ξ‖
  let fV : H3FourierPoint3 → ℝ := fun ξ =>
    ‖ξ‖ ^ 2 *
      ‖h3HeatFourierSymbol ν a ξ *
        h3RawFinLerayOuterProductDivergence V V i ξ‖
  let D : H3FourierPoint3 → ℝ := fun ξ =>
    ‖ξ‖ ^ 2 *
      ‖h3HeatFourierSymbol ν a ξ *
        (h3RawFinLerayOuterProductDivergence U U i ξ -
          h3RawFinLerayOuterProductDivergence V V i ξ)‖

  have hfU : Integrable fU (volume : Measure H3FourierPoint3) := by
    have hMoment :=
      h3RawFinLerayOuterProductDivergenceHeatRepresentative_moment_integrable
        hν ha U U i 2 (by norm_num)
    simpa only [
      fU,
      h3RawFinLerayOuterProductDivergenceHeatRepresentative
    ] using hMoment

  have hfV : Integrable fV (volume : Measure H3FourierPoint3) := by
    have hMoment :=
      h3RawFinLerayOuterProductDivergenceHeatRepresentative_moment_integrable
        hν ha V V i 2 (by norm_num)
    simpa only [
      fV,
      h3RawFinLerayOuterProductDivergenceHeatRepresentative
    ] using hMoment

  have hD : Integrable D (volume : Measure H3FourierPoint3) := by
    dsimp only [D]
    exact
      h3RawFinLerayOuterProductDivergenceHeat_diagonalDifference_secondMoment_integrable
        hν ha U V i

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        ‖fU ξ - fV ξ‖ ≤ D ξ := by
    intro ξ
    have hw : 0 ≤ ‖ξ‖ ^ 2 := sq_nonneg ‖ξ‖

    dsimp only [fU, fV, D]
    rw [← mul_sub]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]

    calc
      ‖ξ‖ ^ 2 *
          |‖h3HeatFourierSymbol ν a ξ *
                h3RawFinLerayOuterProductDivergence U U i ξ‖ -
            ‖h3HeatFourierSymbol ν a ξ *
                h3RawFinLerayOuterProductDivergence V V i ξ‖|
          ≤
        ‖ξ‖ ^ 2 *
          ‖h3HeatFourierSymbol ν a ξ *
                h3RawFinLerayOuterProductDivergence U U i ξ -
            h3HeatFourierSymbol ν a ξ *
                h3RawFinLerayOuterProductDivergence V V i ξ‖ := by
        exact
          mul_le_mul_of_nonneg_left
            (abs_norm_sub_norm_le _ _)
            hw
      _ =
        ‖ξ‖ ^ 2 *
          ‖h3HeatFourierSymbol ν a ξ *
            (h3RawFinLerayOuterProductDivergence U U i ξ -
              h3RawFinLerayOuterProductDivergence V V i ξ)‖ := by
        congr 2 <;> ring

  unfold h3NonlinearForcingHeatSecondMomentFrozenProfile
  rw [← Real.norm_eq_abs]
  rw [← integral_sub hfU hfV]

  calc
    ‖∫ ξ : H3FourierPoint3, fU ξ - fV ξ‖
        ≤
      ∫ ξ : H3FourierPoint3, ‖fU ξ - fV ξ‖ :=
      norm_integral_le_integral_norm _
    _ ≤
      ∫ ξ : H3FourierPoint3, D ξ := by
      exact
        integral_mono_ae
          (hfU.sub hfV).norm
          hD
          (Eventually.of_forall hPoint)
    _ ≤
      ((Real.sqrt (ν * (a / 3)))⁻¹) ^ 2 *
        (h3NonlinearForcingL1Coefficient * ‖U - V‖ * ‖U‖ +
          h3NonlinearForcingL1Coefficient * ‖V‖ * ‖U - V‖) := by
      dsimp only [D]
      exact
        h3RawFinLerayOuterProductDivergenceHeat_diagonalDifference_secondMoment_integral_le_stateDifference
          hν ha U V i

end

end Euclidean
end Bridge
end PrimeTensor
