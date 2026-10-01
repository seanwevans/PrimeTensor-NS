import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Channel.Polynomial.Dichotomy

/-!
# Cofinal fixed polynomial balance channel on the full physical terminal tail

The preceding full-tail theorem says that, under hypothetical nonextension,
every sufficiently late physical time lies in one of two polynomial balance
channels:

* rapid H³ energy decay, or
* adverse H³ transport.

Each active channel carries the same three quantitative terminal scales:

* raw inverse-`8/3` rate;
* physical-clock inverse-`5/3` rate;
* full-energy normalized inverse-`2/3` rate.

The active channel may switch from time to time, but there are only two
channels.  Since their union is eventually all of the left terminal
neighborhood, at least one channel occurs frequently in `𝓝[<] T`.  Thus one
fixed mechanism occurs arbitrarily close to the terminal time while carrying
all three polynomial rates.

This remains neutral: the theorem does not decide which channel is cofinal.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The three polynomial terminal rates carried by the negative-energy-
derivative channel at time `t`, relative to anchor `b`. -/
def H3TerminalDecayPolynomialRatesAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T b t : ℝ) : Prop :=
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

/-- The three polynomial terminal rates carried by the adverse-transport
channel at time `t`, relative to anchor `b`. -/
def H3TerminalTransportPolynomialRatesAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T b t : ℝ) : Prop :=
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

/-- Named-predicate form of the synchronized full-tail polynomial channel
dichotomy. -/
theorem exists_terminalTail_namedBalanceChannel_polynomialRateDichotomy_of_noH3PathExtension
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
        H3TerminalDecayPolynomialRatesAt u T b t
          ∨
        H3TerminalTransportPolynomialRatesAt u T b t := by
  obtain ⟨c, hc, hRates⟩ :=
    exists_terminalTail_balanceChannel_polynomialRateDichotomy_of_noH3PathExtension
      hH3 hNoExtension hClass hb
  refine ⟨c, hc, ?_⟩
  intro t ht
  simpa only [
    H3TerminalDecayPolynomialRatesAt,
    H3TerminalTransportPolynomialRatesAt
  ] using hRates t ht

/-- Under hypothetical nonextension, one fixed balance mechanism carries all
three polynomial terminal rates frequently in the left-neighborhood filter.
Equivalently, that fixed mechanism occurs arbitrarily close to `T` in physical
time.  The theorem does not choose between decay and transport. -/
theorem frequently_fixedBalanceChannel_polynomialRates_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    (∃ᶠ t : ℝ in 𝓝[<] T,
      H3TerminalDecayPolynomialRatesAt u T b t)
      ∨
    (∃ᶠ t : ℝ in 𝓝[<] T,
      H3TerminalTransportPolynomialRatesAt u T b t) := by
  obtain ⟨c, hc, hRates⟩ :=
    exists_terminalTail_namedBalanceChannel_polynomialRateDichotomy_of_noH3PathExtension
      hH3 hNoExtension hClass hb

  have hEventuallyOr :
      ∀ᶠ t : ℝ in 𝓝[<] T,
        H3TerminalDecayPolynomialRatesAt u T b t
          ∨
        H3TerminalTransportPolynomialRatesAt u T b t := by
    filter_upwards [Ioo_mem_nhdsLT hc.2] with t ht
    exact hRates t ht

  by_cases hDecayFrequently :
      ∃ᶠ t : ℝ in 𝓝[<] T,
        H3TerminalDecayPolynomialRatesAt u T b t

  · exact Or.inl hDecayFrequently

  · right

    have hEventuallyNotDecay :
        ∀ᶠ t : ℝ in 𝓝[<] T,
          ¬ H3TerminalDecayPolynomialRatesAt u T b t :=
      (not_frequently).1 hDecayFrequently

    have hEventuallyTransport :
        ∀ᶠ t : ℝ in 𝓝[<] T,
          H3TerminalTransportPolynomialRatesAt u T b t := by
      filter_upwards [hEventuallyOr, hEventuallyNotDecay] with t hEither hNotDecay
      exact hEither.resolve_left hNotDecay

    exact hEventuallyTransport.frequently

/-- Neutral positive form: either smooth continuation exists, or one fixed
balance mechanism is cofinal in physical time and carries all three polynomial
rates arbitrarily close to `T`. -/
theorem smoothContinuationExtension_or_frequently_fixedBalanceChannel_polynomialRates
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
        H3TerminalDecayPolynomialRatesAt u T b t)
        ∨
      (∃ᶠ t : ℝ in 𝓝[<] T,
        H3TerminalTransportPolynomialRatesAt u T b t)
    ) := by
  classical

  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact Or.inl hExtension

  · exact
      Or.inr
        (frequently_fixedBalanceChannel_polynomialRates_of_noH3PathExtension
          hH3 hExtension hClass hb)

/-- Canonical midpoint-anchor specialization of the cofinal fixed polynomial
balance-channel theorem. -/
theorem frequently_fixedBalanceChannel_polynomialRates_midpoint_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∃ᶠ t : ℝ in 𝓝[<] T,
      H3TerminalDecayPolynomialRatesAt
        u T (h3BKMKineticTailMidpoint a T) t)
      ∨
    (∃ᶠ t : ℝ in 𝓝[<] T,
      H3TerminalTransportPolynomialRatesAt
        u T (h3BKMKineticTailMidpoint a T) t) := by
  exact
    frequently_fixedBalanceChannel_polynomialRates_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      (h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2)

end

end Euclidean
end Bridge
end PrimeTensor
