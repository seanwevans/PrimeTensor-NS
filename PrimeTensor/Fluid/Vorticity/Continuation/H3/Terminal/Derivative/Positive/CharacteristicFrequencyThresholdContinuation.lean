import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.CharacteristicFrequencyContinuation

/-!
# Quantitative characteristic-frequency threshold continuation criteria

The intrinsic terminal frequency rate established earlier says that hypothetical
nonextension forces, on some sufficiently late terminal tail,

    1
      ≤
    3 K^2 (E₀(b)+1) (T-t)^2 Λ₃(t)^6.

Equivalently, the reciprocal characteristic length must eventually satisfy

    ℓ₃(t)^6
      ≤
    3 K^2 (E₀(b)+1) (T-t)^2.

This file records the exact positive contrapositives.

If the rescaled characteristic frequency remains subcritical at arbitrarily
late times, then smooth continuation across `T` exists.

Dually, if the characteristic length violates the forced collapse rate at
arbitrarily late times, then smooth continuation across `T` exists.

It also packages the corresponding neutral dichotomies.  No theorem selects
one branch a priori.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Arbitrarily-late subcritical frequency implies continuation -/

/--
If for every terminal restart `c` beyond a fixed anchor `b` there is a still
later time at which

    3 K² (E₀(b)+1) (T-t)² Λ₃(t)^6 < 1,

then the H³ path admits a smooth continuation across `T`.
-/
theorem exists_smoothContinuationExtension_of_characteristicFrequency_pow_six_subcritical_arbitrarilyLate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hSubcritical :
      ∀ c : ℝ,
        c ∈ Set.Ioo b T →
        ∃ t : ℝ,
          t ∈ Set.Ioo c T
            ∧
          3
              *
            h3PathSqrtEnergyRiccatiCoefficient ^ 2
              *
            (
              velocityH3Energy0At u b
                +
              1
            )
              *
            (T - t) ^ 2
              *
            h3TopCharacteristicFrequencyAt u t ^ 6
            <
          1) :
    ∃
      v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  by_contra hNoExtension

  obtain
    ⟨c, hc, hRate⟩ :=
    exists_terminalTail_characteristicFrequency_pow_six_rate_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hb

  obtain
    ⟨t, ht, hSub⟩ :=
    hSubcritical
      c
      hc

  have hForced :=
    hRate
      t
      ht

  exact
    (not_lt_of_ge hForced)
      hSub

/-! ## Arbitrarily-late failure of length collapse implies continuation -/

/--
If for every terminal restart `c` beyond `b` there is a still later time at
which the characteristic length violates the nonextension collapse rate,

    3 K² (E₀(b)+1) (T-t)² < ℓ₃(t)^6,

then smooth continuation across `T` exists.
-/
theorem exists_smoothContinuationExtension_of_characteristicLength_pow_six_supercritical_arbitrarilyLate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hSupercritical :
      ∀ c : ℝ,
        c ∈ Set.Ioo b T →
        ∃ t : ℝ,
          t ∈ Set.Ioo c T
            ∧
          3
              *
            h3PathSqrtEnergyRiccatiCoefficient ^ 2
              *
            (
              velocityH3Energy0At u b
                +
              1
            )
              *
            (T - t) ^ 2
            <
          h3TopCharacteristicLengthAt u t ^ 6) :
    ∃
      v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  by_contra hNoExtension

  obtain
    ⟨c, hc, hRate⟩ :=
    exists_terminalTail_characteristicLength_pow_six_le_terminalDistance_sq_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hb

  obtain
    ⟨t, ht, hSuper⟩ :=
    hSupercritical
      c
      hc

  have hForced :=
    hRate
      t
      ht

  exact
    (not_lt_of_ge hForced)
      hSuper

/-! ## Neutral quantitative terminal dichotomies -/

/--
For a fixed strict terminal anchor, either smooth continuation exists or the
rescaled characteristic-frequency lower bound holds throughout some terminal
tail.
-/
theorem smoothContinuationExtension_or_eventual_characteristicFrequency_pow_six_rate
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
    (
      ∃ c : ℝ,
        c ∈ Set.Ioo b T
          ∧
        ∀ t : ℝ,
          t ∈ Set.Ioo c T →
          1
            ≤
          3
              *
            h3PathSqrtEnergyRiccatiCoefficient ^ 2
              *
            (
              velocityH3Energy0At u b
                +
              1
            )
              *
            (T - t) ^ 2
              *
            h3TopCharacteristicFrequencyAt u t ^ 6
    ) := by

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
          exists_terminalTail_characteristicFrequency_pow_six_rate_of_noH3PathExtension
            hH3
            hExtension
            hClass
            hb
        )

/--
Dual neutral form: either smooth continuation exists or the characteristic
length obeys the forced terminal collapse rate throughout some terminal tail.
-/
theorem smoothContinuationExtension_or_eventual_characteristicLength_pow_six_collapse
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
    (
      ∃ c : ℝ,
        c ∈ Set.Ioo b T
          ∧
        ∀ t : ℝ,
          t ∈ Set.Ioo c T →
          h3TopCharacteristicLengthAt u t ^ 6
            ≤
          3
              *
            h3PathSqrtEnergyRiccatiCoefficient ^ 2
              *
            (
              velocityH3Energy0At u b
                +
              1
            )
              *
            (T - t) ^ 2
    ) := by

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
          exists_terminalTail_characteristicLength_pow_six_le_terminalDistance_sq_of_noH3PathExtension
            hH3
            hExtension
            hClass
            hb
        )

/-! ## Canonical midpoint specializations -/

/--
Canonical midpoint-anchor form of the arbitrarily-late subcritical-frequency
continuation criterion.
-/
theorem exists_smoothContinuationExtension_of_characteristicFrequency_pow_six_subcritical_arbitrarilyLate_midpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hSubcritical :
      ∀ c : ℝ,
        c ∈
          Set.Ioo
            (h3BKMKineticTailMidpoint a T)
            T →
        ∃ t : ℝ,
          t ∈ Set.Ioo c T
            ∧
          3
              *
            h3PathSqrtEnergyRiccatiCoefficient ^ 2
              *
            (
              velocityH3Energy0At
                  u
                  (h3BKMKineticTailMidpoint a T)
                +
              1
            )
              *
            (T - t) ^ 2
              *
            h3TopCharacteristicFrequencyAt u t ^ 6
            <
          1) :
    ∃
      v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  exact
    exists_smoothContinuationExtension_of_characteristicFrequency_pow_six_subcritical_arbitrarilyLate
      hH3
      hClass
      (h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2)
      hSubcritical

/--
Canonical midpoint-anchor form of the arbitrarily-late failure-of-length-
collapse continuation criterion.
-/
theorem exists_smoothContinuationExtension_of_characteristicLength_pow_six_supercritical_arbitrarilyLate_midpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hSupercritical :
      ∀ c : ℝ,
        c ∈
          Set.Ioo
            (h3BKMKineticTailMidpoint a T)
            T →
        ∃ t : ℝ,
          t ∈ Set.Ioo c T
            ∧
          3
              *
            h3PathSqrtEnergyRiccatiCoefficient ^ 2
              *
            (
              velocityH3Energy0At
                  u
                  (h3BKMKineticTailMidpoint a T)
                +
              1
            )
              *
            (T - t) ^ 2
            <
          h3TopCharacteristicLengthAt u t ^ 6) :
    ∃
      v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  exact
    exists_smoothContinuationExtension_of_characteristicLength_pow_six_supercritical_arbitrarilyLate
      hH3
      hClass
      (h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2)
      hSupercritical

end

end Euclidean
end Bridge
end PrimeTensor
