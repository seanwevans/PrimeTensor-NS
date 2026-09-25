import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.CharacteristicFrequencyIntegrability

/-!
# Characteristic-frequency continuation criterion

The preceding theorem established the necessary terminal pathology

    no smooth continuation across T
      ->
    Λ₃^3 is nonintegrable on every strict terminal subtail.

This file records the logically equivalent positive continuation criterion:

    if Λ₃^3 is integrable on any strict terminal subtail,
    then the H³ path admits a smooth continuation across T.

It also packages the neutral terminal dichotomy:

    smooth continuation across T

or

    Λ₃^3 is nonintegrable on every strict terminal subtail.

No branch is asserted a priori.  The second branch is only the necessary
alternative under hypothetical nonextension.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Positive continuation criteria -/

/--
Integrability of the intrinsic characteristic-frequency cube on any strict
terminal subtail rules out the nonextension branch.
-/
theorem exists_smoothContinuationExtension_of_integrableOn_characteristicFrequency_pow_three_on_strictSubtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hIntegrable :
      MeasureTheory.IntegrableOn
        (
          fun t : ℝ =>
            h3TopCharacteristicFrequencyAt u t ^ 3
        )
        (Set.Ioo b T)) :
    ∃
      v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  by_contra hNoExtension

  exact
    (
      not_integrableOn_characteristicFrequency_pow_three_on_strictSubtail_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
        hb
    )
      hIntegrable

/--
In particular, integrability of the characteristic-frequency cube on the
original H³ energy-class terminal tail forces smooth continuation.
-/
theorem exists_smoothContinuationExtension_of_integrableOn_characteristicFrequency_pow_three_on_energyClassTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hIntegrable :
      MeasureTheory.IntegrableOn
        (
          fun t : ℝ =>
            h3TopCharacteristicFrequencyAt u t ^ 3
        )
        (Set.Ioo a T)) :
    ∃
      v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  by_contra hNoExtension

  exact
    (
      not_integrableOn_characteristicFrequency_pow_three_on_energyClassTail_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
    )
      hIntegrable

/-! ## Neutral terminal continuation dichotomies -/

/--
For any fixed strict terminal subtail, exactly the useful neutral alternative
is available:

* either the path admits a smooth continuation across `T`;
* or `Λ₃^3` is nonintegrable on that subtail.

The theorem does not select a branch.
-/
theorem smoothContinuationExtension_or_not_integrableOn_characteristicFrequency_pow_three_on_strictSubtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    (
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
    )
      ∨
    ¬ MeasureTheory.IntegrableOn
        (
          fun t : ℝ =>
            h3TopCharacteristicFrequencyAt u t ^ 3
        )
        (Set.Ioo b T) := by

  classical

  by_cases hExtension :
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact
      Or.inl
        hExtension

  · exact
      Or.inr
        (
          not_integrableOn_characteristicFrequency_pow_three_on_strictSubtail_of_noH3PathExtension
            hH3
            hExtension
            hClass
            hb
        )

/--
Global strict-subtail form of the neutral terminal dichotomy:

* either smooth continuation exists across `T`;
* or the characteristic-frequency cube is nonintegrable on every strict
  terminal subtail of the energy-class interval.

Again, the theorem does not assert which branch occurs.
-/
theorem smoothContinuationExtension_or_characteristicFrequency_pow_three_nonintegrable_on_every_strictSubtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
    )
      ∨
    (
      ∀ b : ℝ,
        b ∈ Set.Ioo a T →
        ¬ MeasureTheory.IntegrableOn
            (
              fun t : ℝ =>
                h3TopCharacteristicFrequencyAt u t ^ 3
            )
            (Set.Ioo b T)
    ) := by

  classical

  by_cases hExtension :
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact
      Or.inl
        hExtension

  · refine
      Or.inr
        ?_

    intro b hb

    exact
      not_integrableOn_characteristicFrequency_pow_three_on_strictSubtail_of_noH3PathExtension
        hH3
        hExtension
        hClass
        hb

end

end Euclidean
end Bridge
end PrimeTensor
