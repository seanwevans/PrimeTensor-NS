import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.ProfileStateVariation

/-!
# Second-moment control of frozen-forcing heat-lag variation

The complementary continuity term freezes the nonlinear forcing and changes
only the positive heat lag.  `Quarter.Heat.SecondMomentIncrement` already gives
the required two-moment L1 estimate for an arbitrary integrable amplitude.

Here that amplitude is the raw diagonal finite Leray forcing.  Its established
Fourier-L1 bound then turns the heat-time increment into an explicit H3
bilinear estimate.

Together with `Forcing.ProfileStateVariation`, this closes the two quantitative
pieces needed to prove local continuity of the named selected second-moment
profile at every strict retarded time.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3SchwartzQuarterForcingProfileLagVariation
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Frozen diagonal forcing: changing the positive heat lag is controlled by
the universal positive-lag second-moment increment coefficient times the raw
forcing L1 mass. -/
theorem h3RawFinLerayOuterProductDivergenceHeat_frozen_secondMoment_add_sub_integral_le
    {ν a h : ℝ}
    (hν : 0 < ν)
    (ha : 0 < a)
    (hh : 0 ≤ h)
    (U : H3SpectralFinVectorState)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3HeatFourierSymbol ν (a + h) ξ *
                h3RawFinLerayOuterProductDivergence U U i ξ -
              h3HeatFourierSymbol ν a ξ *
                h3RawFinLerayOuterProductDivergence U U i ξ‖)
      ≤
    h3HeatPositiveLagSecondMomentIncrementCoefficient ν a h *
      h3RawFinLerayOuterProductDivergenceL1Mass U U i := by
  have hRaw :
      Integrable
        (h3RawFinLerayOuterProductDivergence U U i)
        (volume : Measure H3FourierPoint3) :=
    h3RawFinLerayOuterProductDivergence_integrable U U i

  have hInc :=
    h3HeatFourierSymbol_add_sub_secondMoment_norm_integral_le_positiveLag
      hν ha hh
      (h3RawFinLerayOuterProductDivergence U U i)
      hRaw

  simpa only [
    sub_mul,
    h3RawFinLerayOuterProductDivergenceL1Mass
  ] using hInc

/-- H3-bilinear specialization of the frozen-forcing heat-lag variation
estimate. -/
theorem h3RawFinLerayOuterProductDivergenceHeat_frozen_secondMoment_add_sub_integral_le_bilinear
    {ν a h : ℝ}
    (hν : 0 < ν)
    (ha : 0 < a)
    (hh : 0 ≤ h)
    (U : H3SpectralFinVectorState)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3HeatFourierSymbol ν (a + h) ξ *
                h3RawFinLerayOuterProductDivergence U U i ξ -
              h3HeatFourierSymbol ν a ξ *
                h3RawFinLerayOuterProductDivergence U U i ξ‖)
      ≤
    h3HeatPositiveLagSecondMomentIncrementCoefficient ν a h *
      (h3NonlinearForcingL1Coefficient * ‖U‖ * ‖U‖) := by
  have hLag :=
    h3RawFinLerayOuterProductDivergenceHeat_frozen_secondMoment_add_sub_integral_le
      hν ha hh U i

  have hMass :=
    h3RawFinLerayOuterProductDivergenceL1Mass_le U U i

  have hCoeff :
      0 ≤ h3HeatPositiveLagSecondMomentIncrementCoefficient ν a h :=
    h3HeatPositiveLagSecondMomentIncrementCoefficient_nonneg
      hν.le ha.le hh

  exact
    hLag.trans
      (mul_le_mul_of_nonneg_left hMass hCoeff)

end

end Euclidean
end Bridge
end PrimeTensor
