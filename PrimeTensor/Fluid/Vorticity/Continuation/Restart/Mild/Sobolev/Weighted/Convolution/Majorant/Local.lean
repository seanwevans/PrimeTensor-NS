import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Weighted.Convolution.Majorant.States
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Local control of the weighted H³ Young majorants

The real endpoint-Young states constructed in `WeightedConvolutionMajorantStates` are already
bounded in `L²`.  To identify those bundled states with the scalar majorants, Mathlib's
set-integral uniqueness theorem asks for local integrability on every measurable set of finite
measure.

That local hypothesis follows from the complementary endpoint estimate

    L² * L² → L∞.

For each output frequency, Hölder with exponents `2,2` bounds the scalar convolution by a constant
independent of the output frequency.  Translation/reflection invariance removes the shifted square
integral.  Hence each scalar majorant is bounded and therefore integrable on every finite-measure
set.  The candidate `L²` states are locally integrable there as well.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3WeightedConvolutionMajorantLocal
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Uniform `L² * L² → L∞` bound for the first scalar Young majorant. -/
noncomputable def h3FirstYoungMajorantLinfBound
    (F G : H3SpectralScalarState) : ℝ :=
  ((∫ η : H3FourierPoint3,
      ‖h3SpectralScalarRawFourier G η‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ))) *
    ((∫ η : H3FourierPoint3,
      ‖F η‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)))

/-- Uniform `L² * L² → L∞` bound for the second scalar Young majorant. -/
noncomputable def h3SecondYoungMajorantLinfBound
    (F G : H3SpectralScalarState) : ℝ :=
  ((∫ η : H3FourierPoint3,
      ‖h3SpectralScalarRawFourier F η‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ))) *
    ((∫ η : H3FourierPoint3,
      ‖G η‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)))

/-- Pointwise `L² * L² → L∞` estimate for the first scalar majorant. -/
theorem h3FirstYoungMajorant_le_linfBound
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    h3FirstYoungMajorant F G ξ
      ≤ h3FirstYoungMajorantLinfBound F G := by
  have hRaw :
      MemLp
        (h3SpectralScalarRawFourier G)
        (ENNReal.ofReal (2 : ℝ))
        (volume : Measure H3FourierPoint3) := by
    simpa using h3SpectralScalarRawFourier_memLp2 G

  have hShift :
      MemLp
        (fun η : H3FourierPoint3 => F (ξ - η))
        (ENNReal.ofReal (2 : ℝ))
        (volume : Measure H3FourierPoint3) := by
    simpa using h3SpectralScalarState_reflectedShift_memLp2 F ξ

  have hHolder :=
    integral_mul_norm_le_Lp_mul_Lq
      (μ := (volume : Measure H3FourierPoint3))
      Real.HolderConjugate.two_two
      hRaw
      hShift

  have hShiftSq :
      (∫ η : H3FourierPoint3,
          ‖F (ξ - η)‖ ^ (2 : ℝ))
        =
      ∫ η : H3FourierPoint3,
        ‖F η‖ ^ (2 : ℝ) := by
    simpa using
      (integral_sub_left_eq_self
        (fun η : H3FourierPoint3 => ‖F η‖ ^ (2 : ℝ))
        (volume : Measure H3FourierPoint3)
        ξ)

  rw [hShiftSq] at hHolder
  simpa [h3FirstYoungMajorant, h3FirstYoungMajorantLinfBound] using hHolder

/-- Pointwise `L² * L² → L∞` estimate for the second scalar majorant. -/
theorem h3SecondYoungMajorant_le_linfBound
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    h3SecondYoungMajorant F G ξ
      ≤ h3SecondYoungMajorantLinfBound F G := by
  have hRaw :
      MemLp
        (h3SpectralScalarRawFourier F)
        (ENNReal.ofReal (2 : ℝ))
        (volume : Measure H3FourierPoint3) := by
    simpa using h3SpectralScalarRawFourier_memLp2 F

  have hShift :
      MemLp
        (fun η : H3FourierPoint3 => G (ξ - η))
        (ENNReal.ofReal (2 : ℝ))
        (volume : Measure H3FourierPoint3) := by
    simpa using h3SpectralScalarState_reflectedShift_memLp2 G ξ

  have hHolder :=
    integral_mul_norm_le_Lp_mul_Lq
      (μ := (volume : Measure H3FourierPoint3))
      Real.HolderConjugate.two_two
      hRaw
      hShift

  have hShiftSq :
      (∫ η : H3FourierPoint3,
          ‖G (ξ - η)‖ ^ (2 : ℝ))
        =
      ∫ η : H3FourierPoint3,
        ‖G η‖ ^ (2 : ℝ) := by
    simpa using
      (integral_sub_left_eq_self
        (fun η : H3FourierPoint3 => ‖G η‖ ^ (2 : ℝ))
        (volume : Measure H3FourierPoint3)
        ξ)

  rw [hShiftSq] at hHolder
  simpa [h3SecondYoungMajorant, h3SecondYoungMajorantLinfBound] using hHolder

/-- The first scalar majorant is integrable on every measurable finite-measure set. -/
theorem h3FirstYoungMajorant_integrableOn_finite
    (F G : H3SpectralScalarState)
    (s : Set H3FourierPoint3)
    (hs : MeasurableSet s)
    (hμs : (volume : Measure H3FourierPoint3) s < ∞) :
    IntegrableOn
      (h3FirstYoungMajorant F G)
      s
      (volume : Measure H3FourierPoint3) := by
  refine IntegrableOn.of_bound hμs ?_ (h3FirstYoungMajorantLinfBound F G) ?_
  · exact
      (h3FirstYoungMajorant_aestronglyMeasurable F G).mono_measure
        Measure.restrict_le_self
  · filter_upwards with ξ
    rw [Real.norm_eq_abs,
      abs_of_nonneg (h3FirstYoungMajorant_nonneg F G ξ)]
    exact h3FirstYoungMajorant_le_linfBound F G ξ

/-- The second scalar majorant is integrable on every measurable finite-measure set. -/
theorem h3SecondYoungMajorant_integrableOn_finite
    (F G : H3SpectralScalarState)
    (s : Set H3FourierPoint3)
    (hs : MeasurableSet s)
    (hμs : (volume : Measure H3FourierPoint3) s < ∞) :
    IntegrableOn
      (h3SecondYoungMajorant F G)
      s
      (volume : Measure H3FourierPoint3) := by
  refine IntegrableOn.of_bound hμs ?_ (h3SecondYoungMajorantLinfBound F G) ?_
  · exact
      (h3SecondYoungMajorant_aestronglyMeasurable F G).mono_measure
        Measure.restrict_le_self
  · filter_upwards with ξ
    rw [Real.norm_eq_abs,
      abs_of_nonneg (h3SecondYoungMajorant_nonneg F G ξ)]
    exact h3SecondYoungMajorant_le_linfBound F G ξ

/-- The first bundled Young candidate is locally integrable on finite-measure sets. -/
theorem h3FirstYoungMajorantCandidateL2_integrableOn_finite
    (F G : H3SpectralScalarState)
    (s : Set H3FourierPoint3)
    (_hs : MeasurableSet s)
    (hμs : (volume : Measure H3FourierPoint3) s < ∞) :
    IntegrableOn
      (h3FirstYoungMajorantCandidateL2 F G : H3FourierPoint3 → ℝ)
      s
      (volume : Measure H3FourierPoint3) := by
  exact
    integrableOn_Lp_of_measure_ne_top
      (h3FirstYoungMajorantCandidateL2 F G)
      fact_one_le_two_ennreal.elim
      hμs.ne

/-- The second bundled Young candidate is locally integrable on finite-measure sets. -/
theorem h3SecondYoungMajorantCandidateL2_integrableOn_finite
    (F G : H3SpectralScalarState)
    (s : Set H3FourierPoint3)
    (_hs : MeasurableSet s)
    (hμs : (volume : Measure H3FourierPoint3) s < ∞) :
    IntegrableOn
      (h3SecondYoungMajorantCandidateL2 F G : H3FourierPoint3 → ℝ)
      s
      (volume : Measure H3FourierPoint3) := by
  exact
    integrableOn_Lp_of_measure_ne_top
      (h3SecondYoungMajorantCandidateL2 F G)
      fact_one_le_two_ennreal.elim
      hμs.ne

end

end Euclidean
end Bridge
end PrimeTensor
