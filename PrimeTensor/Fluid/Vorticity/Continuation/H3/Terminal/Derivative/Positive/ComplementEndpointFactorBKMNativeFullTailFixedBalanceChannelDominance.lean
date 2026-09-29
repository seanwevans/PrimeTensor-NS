import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailFixedBalanceChannelPolynomialFrequency
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeScaleRates

/-!
# Retaining dominance in the cofinal polynomial balance channel

The earlier fixed-channel package records that one of the two exact H³ balance
channels carries all three polynomial terminal rates cofinally.  For later
exact-balance comparisons we also need to remember that the chosen channel was
actually the pointwise maximum defining the canonical balance amplitude.

This file retains that missing order information.  On one full terminal tail,
every time belongs to one of two dominant polynomial channels:

* decay dominates transport and carries all three rates; or
* transport dominates decay and carries all three rates.

Since these two dominant sets cover an eventual left terminal neighborhood, at
least one fixed dominant channel occurs frequently in `𝓝[<] T`.

The result remains neutral between decay and transport.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The decay channel carries all three polynomial rates and is at least as
large as the adverse-transport channel. -/
def H3TerminalDecayDominantPolynomialRatesAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T b t : ℝ) : Prop :=
  H3TerminalDecayPolynomialRatesAt u T b t
    ∧
  (- velocityH3TransportDerivativeAt u t)
    ≤
  (- deriv (velocityH3EnergyAt u) t)

/-- The adverse-transport channel carries all three polynomial rates and is at
least as large as the negative-energy-derivative channel. -/
def H3TerminalTransportDominantPolynomialRatesAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T b t : ℝ) : Prop :=
  H3TerminalTransportPolynomialRatesAt u T b t
    ∧
  (- deriv (velocityH3EnergyAt u) t)
    ≤
  (- velocityH3TransportDerivativeAt u t)

/-- Under hypothetical nonextension, every sufficiently late physical time lies
in one of the two dominant polynomial balance channels.  The dominance clause
records which argument realizes the canonical maximum at that time. -/
theorem exists_terminalTail_dominantBalanceChannel_polynomialRateDichotomy_of_noH3PathExtension
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
        H3TerminalDecayDominantPolynomialRatesAt u T b t
          ∨
        H3TerminalTransportDominantPolynomialRatesAt u T b t := by
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
    exact
      ⟨
        lt_of_le_of_lt
          (le_max_left cRaw (max cPhysical cNormalized))
          ht.1,
        ht.2
      ⟩

  have htPhysical : t ∈ Set.Ioo cPhysical T := by
    exact
      ⟨
        lt_of_le_of_lt
          (le_trans
            (le_max_left cPhysical cNormalized)
            (le_max_right cRaw (max cPhysical cNormalized)))
          ht.1,
        ht.2
      ⟩

  have htNormalized : t ∈ Set.Ioo cNormalized T := by
    exact
      ⟨
        lt_of_le_of_lt
          (le_trans
            (le_max_right cPhysical cNormalized)
            (le_max_right cRaw (max cPhysical cNormalized)))
          ht.1,
        ht.2
      ⟩

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

    have hRates :
        H3TerminalTransportPolynomialRatesAt u T b t := by
      exact
        ⟨
          hRawTransport,
          hPhysicalTransport,
          hNormalizedTransport
        ⟩

    exact
      ⟨
        hRates,
        hDecayLeTransport
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

    have hRates :
        H3TerminalDecayPolynomialRatesAt u T b t := by
      exact
        ⟨
          hRawDecay,
          hPhysicalDecay,
          hNormalizedDecay
        ⟩

    exact
      ⟨
        hRates,
        hTransportLeDecay
      ⟩

/-- One fixed dominant balance mechanism occurs arbitrarily close to `T` while
carrying all three polynomial rates.  Unlike the previous fixed-channel
predicate, this statement retains the ordering that identifies the active
argument of the canonical maximum. -/
theorem frequently_fixedDominantBalanceChannel_polynomialRates_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    (∃ᶠ t : ℝ in 𝓝[<] T,
      H3TerminalDecayDominantPolynomialRatesAt u T b t)
      ∨
    (∃ᶠ t : ℝ in 𝓝[<] T,
      H3TerminalTransportDominantPolynomialRatesAt u T b t) := by
  obtain ⟨c, hc, hChannels⟩ :=
    exists_terminalTail_dominantBalanceChannel_polynomialRateDichotomy_of_noH3PathExtension
      hH3 hNoExtension hClass hb

  have hEventuallyOr :
      ∀ᶠ t : ℝ in 𝓝[<] T,
        H3TerminalDecayDominantPolynomialRatesAt u T b t
          ∨
        H3TerminalTransportDominantPolynomialRatesAt u T b t := by
    filter_upwards [Ioo_mem_nhdsLT hc.2] with t ht
    exact hChannels t ht

  by_cases hDecayFrequently :
      ∃ᶠ t : ℝ in 𝓝[<] T,
        H3TerminalDecayDominantPolynomialRatesAt u T b t

  · exact Or.inl hDecayFrequently

  · right

    have hEventuallyNotDecay :
        ∀ᶠ t : ℝ in 𝓝[<] T,
          ¬ H3TerminalDecayDominantPolynomialRatesAt u T b t :=
      (not_frequently).1 hDecayFrequently

    have hEventuallyTransport :
        ∀ᶠ t : ℝ in 𝓝[<] T,
          H3TerminalTransportDominantPolynomialRatesAt u T b t := by
      filter_upwards [hEventuallyOr, hEventuallyNotDecay] with t hEither hNotDecay
      exact hEither.resolve_left hNotDecay

    exact hEventuallyTransport.frequently

/-- Neutral positive form of the fixed dominant polynomial channel. -/
theorem smoothContinuationExtension_or_frequently_fixedDominantBalanceChannel_polynomialRates
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
      (∃ᶠ t : ℝ in 𝓝[<] T,
        H3TerminalDecayDominantPolynomialRatesAt u T b t)
        ∨
      (∃ᶠ t : ℝ in 𝓝[<] T,
        H3TerminalTransportDominantPolynomialRatesAt u T b t)
    ) := by
  classical

  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact Or.inl hExtension

  · exact
      Or.inr
        (frequently_fixedDominantBalanceChannel_polynomialRates_of_noH3PathExtension
          hH3 hExtension hClass hb)

/-- Midpoint-anchor specialization of the fixed dominant polynomial channel. -/
theorem frequently_fixedDominantBalanceChannel_polynomialRates_midpoint_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∃ᶠ t : ℝ in 𝓝[<] T,
      H3TerminalDecayDominantPolynomialRatesAt
        u T (h3BKMKineticTailMidpoint a T) t)
      ∨
    (∃ᶠ t : ℝ in 𝓝[<] T,
      H3TerminalTransportDominantPolynomialRatesAt
        u T (h3BKMKineticTailMidpoint a T) t) := by
  exact
    frequently_fixedDominantBalanceChannel_polynomialRates_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      (h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2)

end

end Euclidean
end Bridge
end PrimeTensor
