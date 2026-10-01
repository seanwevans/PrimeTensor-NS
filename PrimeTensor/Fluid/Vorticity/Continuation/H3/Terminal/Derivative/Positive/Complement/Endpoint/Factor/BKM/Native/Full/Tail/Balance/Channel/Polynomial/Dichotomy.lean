import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Scale.Rates

/-!
# Full-tail polynomial balance-channel dichotomy

The canonical branch-free balance amplitude

`B(t) = max (-E'(t)) (-T_H3(t))`

now carries three quantitative terminal rates under hypothetical nonextension:

* raw inverse-`8/3` scale;
* physical-clock inverse-`5/3` scale;
* full-energy normalized inverse-`2/3` scale.

Because the same pointwise maximum defines all three quantities, one does not
need separate channel selections at different scales.  After synchronizing the
three terminal tails, every sufficiently late physical time has one of two
possibilities:

* the negative H³ energy derivative carries all three rates; or
* adverse H³ transport carries all three rates.

The active channel may still switch with time.  Thus this theorem is a
full-tail quantitative dichotomy, not a fixed-branch assertion.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Under hypothetical nonextension, there is a single late terminal tail on
which, at every time, either negative H³ energy derivative or adverse H³
transport simultaneously carries the raw, physical-clock, and full-energy
normalized polynomial balance-amplitude rates. -/
theorem exists_terminalTail_balanceChannel_polynomialRateDichotomy_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    ∃ c : ℝ,
      c ∈ Set.Ioo b T
        ∧
      ∀ t : ℝ,
        t ∈ Set.Ioo c T →
        (
          1 ≤
            81
              * h3PathSqrtEnergyRiccatiCoefficient ^ 8
              * (T - t) ^ 8
              * velocityH3Energy0At u b
              * (- deriv (velocityH3EnergyAt u) t) ^ 3
          ∧
          1 ≤
            81
              * h3PathSqrtEnergyRiccatiCoefficient ^ 8
              * velocityH3Energy0At u b
              * (T - t) ^ 5
              * ((T - t) * (- deriv (velocityH3EnergyAt u) t)) ^ 3
          ∧
          1 ≤
            3
              * h3PathSqrtEnergyRiccatiCoefficient ^ 2
              * (velocityH3Energy0At u b + 1)
              * (4 + 3 * velocityH3Energy0At u b) ^ 3
              * (T - t) ^ 2
              *
                ((- deriv (velocityH3EnergyAt u) t) /
                  velocityH3EnergyAt u t) ^ 3
        )
          ∨
        (
          1 ≤
            81
              * h3PathSqrtEnergyRiccatiCoefficient ^ 8
              * (T - t) ^ 8
              * velocityH3Energy0At u b
              * (- velocityH3TransportDerivativeAt u t) ^ 3
          ∧
          1 ≤
            81
              * h3PathSqrtEnergyRiccatiCoefficient ^ 8
              * velocityH3Energy0At u b
              * (T - t) ^ 5
              * ((T - t) * (- velocityH3TransportDerivativeAt u t)) ^ 3
          ∧
          1 ≤
            3
              * h3PathSqrtEnergyRiccatiCoefficient ^ 2
              * (velocityH3Energy0At u b + 1)
              * (4 + 3 * velocityH3Energy0At u b) ^ 3
              * (T - t) ^ 2
              *
                ((- velocityH3TransportDerivativeAt u t) /
                  velocityH3EnergyAt u t) ^ 3
        ) := by
  obtain ⟨cRaw, hcRaw, hRaw⟩ :=
    exists_terminalTail_balanceAmplitude_raw_cubicRate_of_noH3PathExtension
      hH3 hNoExtension hClass hb

  obtain ⟨cPhysical, hcPhysical, hPhysical⟩ :=
    exists_terminalTail_balanceAmplitude_physicalClock_cubicRate_of_noH3PathExtension
      hH3 hNoExtension hClass hb

  obtain ⟨cNormalized, hcNormalized, hNormalized⟩ :=
    exists_terminalTail_balanceAmplitude_div_energy_cubicRate_of_noH3PathExtension
      hH3 hNoExtension hClass hb

  let c : ℝ :=
    max cRaw (max cPhysical cNormalized)

  have hcLower : b < c := by
    dsimp only [c]
    exact
      lt_of_lt_of_le
        hcRaw.1
        (le_max_left cRaw (max cPhysical cNormalized))

  have hcUpper : c < T := by
    dsimp only [c]
    exact
      max_lt
        hcRaw.2
        (max_lt hcPhysical.2 hcNormalized.2)

  refine ⟨c, ⟨hcLower, hcUpper⟩, ?_⟩

  intro t ht

  have htRaw : t ∈ Set.Ioo cRaw T := by
    constructor
    · exact
        lt_of_le_of_lt
          (le_max_left cRaw (max cPhysical cNormalized))
          ht.1
    · exact ht.2

  have htPhysical : t ∈ Set.Ioo cPhysical T := by
    constructor
    · exact
        lt_of_le_of_lt
          (le_trans
            (le_max_left cPhysical cNormalized)
            (le_max_right cRaw (max cPhysical cNormalized)))
          ht.1
    · exact ht.2

  have htNormalized : t ∈ Set.Ioo cNormalized T := by
    constructor
    · exact
        lt_of_le_of_lt
          (le_trans
            (le_max_right cPhysical cNormalized)
            (le_max_right cRaw (max cPhysical cNormalized)))
          ht.1
    · exact ht.2

  have hRawAt := hRaw t htRaw
  have hPhysicalAt := hPhysical t htPhysical
  have hNormalizedAt := hNormalized t htNormalized

  rcases
    le_total
      (- deriv (velocityH3EnergyAt u) t)
      (- velocityH3TransportDerivativeAt u t)
    with hDecayLeTransport | hTransportLeDecay

  · right

    have hRawTransport :
        1 ≤
          81
            * h3PathSqrtEnergyRiccatiCoefficient ^ 8
            * (T - t) ^ 8
            * velocityH3Energy0At u b
            * (- velocityH3TransportDerivativeAt u t) ^ 3 := by
      simpa only [h3TerminalBalanceAmplitudeAt, max_eq_right hDecayLeTransport] using
        hRawAt

    have hPhysicalTransport :
        1 ≤
          81
            * h3PathSqrtEnergyRiccatiCoefficient ^ 8
            * velocityH3Energy0At u b
            * (T - t) ^ 5
            * ((T - t) * (- velocityH3TransportDerivativeAt u t)) ^ 3 := by
      simpa only [h3TerminalBalanceAmplitudeAt, max_eq_right hDecayLeTransport] using
        hPhysicalAt

    have hNormalizedTransport :
        1 ≤
          3
            * h3PathSqrtEnergyRiccatiCoefficient ^ 2
            * (velocityH3Energy0At u b + 1)
            * (4 + 3 * velocityH3Energy0At u b) ^ 3
            * (T - t) ^ 2
            *
              ((- velocityH3TransportDerivativeAt u t) /
                velocityH3EnergyAt u t) ^ 3 := by
      simpa only [h3TerminalBalanceAmplitudeAt, max_eq_right hDecayLeTransport] using
        hNormalizedAt

    exact
      ⟨
        hRawTransport,
        hPhysicalTransport,
        hNormalizedTransport
      ⟩

  · left

    have hRawDecay :
        1 ≤
          81
            * h3PathSqrtEnergyRiccatiCoefficient ^ 8
            * (T - t) ^ 8
            * velocityH3Energy0At u b
            * (- deriv (velocityH3EnergyAt u) t) ^ 3 := by
      simpa only [h3TerminalBalanceAmplitudeAt, max_eq_left hTransportLeDecay] using
        hRawAt

    have hPhysicalDecay :
        1 ≤
          81
            * h3PathSqrtEnergyRiccatiCoefficient ^ 8
            * velocityH3Energy0At u b
            * (T - t) ^ 5
            * ((T - t) * (- deriv (velocityH3EnergyAt u) t)) ^ 3 := by
      simpa only [h3TerminalBalanceAmplitudeAt, max_eq_left hTransportLeDecay] using
        hPhysicalAt

    have hNormalizedDecay :
        1 ≤
          3
            * h3PathSqrtEnergyRiccatiCoefficient ^ 2
            * (velocityH3Energy0At u b + 1)
            * (4 + 3 * velocityH3Energy0At u b) ^ 3
            * (T - t) ^ 2
            *
              ((- deriv (velocityH3EnergyAt u) t) /
                velocityH3EnergyAt u t) ^ 3 := by
      simpa only [h3TerminalBalanceAmplitudeAt, max_eq_left hTransportLeDecay] using
        hNormalizedAt

    exact
      ⟨
        hRawDecay,
        hPhysicalDecay,
        hNormalizedDecay
      ⟩

/-- Neutral form: either smooth continuation exists, or one of the two exact
H³ balance channels carries all three polynomial scales at every sufficiently
late time, with the active channel allowed to switch from time to time. -/
theorem smoothContinuationExtension_or_eventual_balanceChannel_polynomialRateDichotomy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    (
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
    )
      ∨
    (
      ∃ c : ℝ,
        c ∈ Set.Ioo b T
          ∧
        ∀ t : ℝ,
          t ∈ Set.Ioo c T →
          (
            1 ≤
              81
                * h3PathSqrtEnergyRiccatiCoefficient ^ 8
                * (T - t) ^ 8
                * velocityH3Energy0At u b
                * (- deriv (velocityH3EnergyAt u) t) ^ 3
            ∧
            1 ≤
              81
                * h3PathSqrtEnergyRiccatiCoefficient ^ 8
                * velocityH3Energy0At u b
                * (T - t) ^ 5
                * ((T - t) * (- deriv (velocityH3EnergyAt u) t)) ^ 3
            ∧
            1 ≤
              3
                * h3PathSqrtEnergyRiccatiCoefficient ^ 2
                * (velocityH3Energy0At u b + 1)
                * (4 + 3 * velocityH3Energy0At u b) ^ 3
                * (T - t) ^ 2
                *
                  ((- deriv (velocityH3EnergyAt u) t) /
                    velocityH3EnergyAt u t) ^ 3
          )
            ∨
          (
            1 ≤
              81
                * h3PathSqrtEnergyRiccatiCoefficient ^ 8
                * (T - t) ^ 8
                * velocityH3Energy0At u b
                * (- velocityH3TransportDerivativeAt u t) ^ 3
            ∧
            1 ≤
              81
                * h3PathSqrtEnergyRiccatiCoefficient ^ 8
                * velocityH3Energy0At u b
                * (T - t) ^ 5
                * ((T - t) * (- velocityH3TransportDerivativeAt u t)) ^ 3
            ∧
            1 ≤
              3
                * h3PathSqrtEnergyRiccatiCoefficient ^ 2
                * (velocityH3Energy0At u b + 1)
                * (4 + 3 * velocityH3Energy0At u b) ^ 3
                * (T - t) ^ 2
                *
                  ((- velocityH3TransportDerivativeAt u t) /
                    velocityH3EnergyAt u t) ^ 3
          )
    ) := by
  classical

  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact Or.inl hExtension

  · exact
      Or.inr
        (exists_terminalTail_balanceChannel_polynomialRateDichotomy_of_noH3PathExtension
          hH3 hExtension hClass hb)

/-- Canonical midpoint-anchor specialization of the synchronized full-tail
polynomial balance-channel dichotomy. -/
theorem exists_terminalTail_balanceChannel_polynomialRateDichotomy_midpoint_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∃ c : ℝ,
      c ∈ Set.Ioo (h3BKMKineticTailMidpoint a T) T
        ∧
      ∀ t : ℝ,
        t ∈ Set.Ioo c T →
        (
          1 ≤
            81
              * h3PathSqrtEnergyRiccatiCoefficient ^ 8
              * (T - t) ^ 8
              *
                velocityH3Energy0At
                  u
                  (h3BKMKineticTailMidpoint a T)
              * (- deriv (velocityH3EnergyAt u) t) ^ 3
          ∧
          1 ≤
            81
              * h3PathSqrtEnergyRiccatiCoefficient ^ 8
              *
                velocityH3Energy0At
                  u
                  (h3BKMKineticTailMidpoint a T)
              * (T - t) ^ 5
              * ((T - t) * (- deriv (velocityH3EnergyAt u) t)) ^ 3
          ∧
          1 ≤
            3
              * h3PathSqrtEnergyRiccatiCoefficient ^ 2
              *
                (velocityH3Energy0At
                    u
                    (h3BKMKineticTailMidpoint a T)
                  + 1)
              *
                (4
                  + 3
                    * velocityH3Energy0At
                        u
                        (h3BKMKineticTailMidpoint a T)) ^ 3
              * (T - t) ^ 2
              *
                ((- deriv (velocityH3EnergyAt u) t) /
                  velocityH3EnergyAt u t) ^ 3
        )
          ∨
        (
          1 ≤
            81
              * h3PathSqrtEnergyRiccatiCoefficient ^ 8
              * (T - t) ^ 8
              *
                velocityH3Energy0At
                  u
                  (h3BKMKineticTailMidpoint a T)
              * (- velocityH3TransportDerivativeAt u t) ^ 3
          ∧
          1 ≤
            81
              * h3PathSqrtEnergyRiccatiCoefficient ^ 8
              *
                velocityH3Energy0At
                  u
                  (h3BKMKineticTailMidpoint a T)
              * (T - t) ^ 5
              * ((T - t) * (- velocityH3TransportDerivativeAt u t)) ^ 3
          ∧
          1 ≤
            3
              * h3PathSqrtEnergyRiccatiCoefficient ^ 2
              *
                (velocityH3Energy0At
                    u
                    (h3BKMKineticTailMidpoint a T)
                  + 1)
              *
                (4
                  + 3
                    * velocityH3Energy0At
                        u
                        (h3BKMKineticTailMidpoint a T)) ^ 3
              * (T - t) ^ 2
              *
                ((- velocityH3TransportDerivativeAt u t) /
                  velocityH3EnergyAt u t) ^ 3
        ) := by
  exact
    exists_terminalTail_balanceChannel_polynomialRateDichotomy_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      (h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2)

end

end Euclidean
end Bridge
end PrimeTensor
