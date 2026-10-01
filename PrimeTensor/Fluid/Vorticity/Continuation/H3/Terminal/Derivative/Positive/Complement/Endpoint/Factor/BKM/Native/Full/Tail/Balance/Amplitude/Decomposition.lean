import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Fixed.Balance.Channel.Dominance
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Normalized.Balance.Gap

/-!
# Exact decomposition of the canonical H³ balance amplitude

Write

`x(t) = -E'(t)` and `y(t) = -T_H3(t)`.

The exact H³ balance gives

`x(t) + y(t) = 2 D(t)`.

The canonical branch-free balance amplitude is

`B(t) = max x(t) y(t)`.

For two real numbers with fixed sum, their maximum is the mean plus half their
absolute difference.  Consequently the H³ balance amplitude admits the exact
pointwise decomposition

`2 B(t) = 2 D(t) + |x(t) - y(t)|`.

Thus the excess of the dominant balance channel above full dissipation is
exactly one half of the channel imbalance.  This identity is independent of
which channel dominates and introduces no asymptotic assumption.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Absolute imbalance between the two signed channels in the exact H³ balance. -/
def h3TerminalBalanceImbalanceAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) : ℝ :=
  |(- deriv (velocityH3EnergyAt u) t)
      - (- velocityH3TransportDerivativeAt u t)|

/-- The balance imbalance is nonnegative. -/
theorem h3TerminalBalanceImbalanceAt_nonneg
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) :
    0 ≤ h3TerminalBalanceImbalanceAt u t := by
  unfold h3TerminalBalanceImbalanceAt
  exact abs_nonneg _

/-- Exact branch-free decomposition of the canonical balance amplitude:
`2 B = 2 D + imbalance`. -/
theorem two_mul_h3TerminalBalanceAmplitudeAt_eq_two_mul_dissipation_add_imbalance
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    2 * h3TerminalBalanceAmplitudeAt u t
      =
    2 * velocityH3DissipationAt u t
      + h3TerminalBalanceImbalanceAt u t := by
  have hBalance :=
    deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3 hClass ht

  have hSum :
      (- deriv (velocityH3EnergyAt u) t)
          + (- velocityH3TransportDerivativeAt u t)
        =
      2 * velocityH3DissipationAt u t := by
    linarith

  rcases
    le_total
      (- deriv (velocityH3EnergyAt u) t)
      (- velocityH3TransportDerivativeAt u t)
    with hDecayLeTransport | hTransportLeDecay

  · rw [h3TerminalBalanceAmplitudeAt]
    rw [max_eq_right hDecayLeTransport]
    unfold h3TerminalBalanceImbalanceAt
    rw [abs_of_nonpos (sub_nonpos.mpr hDecayLeTransport)]
    linarith

  · rw [h3TerminalBalanceAmplitudeAt]
    rw [max_eq_left hTransportLeDecay]
    unfold h3TerminalBalanceImbalanceAt
    rw [abs_of_nonneg (sub_nonneg.mpr hTransportLeDecay)]
    linarith

/-- Equivalent mean-plus-half-imbalance form of the canonical balance
amplitude. -/
theorem h3TerminalBalanceAmplitudeAt_eq_dissipation_add_half_imbalance
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3TerminalBalanceAmplitudeAt u t
      =
    velocityH3DissipationAt u t
      + h3TerminalBalanceImbalanceAt u t / 2 := by
  have hExact :=
    two_mul_h3TerminalBalanceAmplitudeAt_eq_two_mul_dissipation_add_imbalance
      hH3 hClass ht
  linarith

/-- If decay is the dominant balance channel, its excess above full
dissipation is exactly half the channel imbalance. -/
theorem two_mul_decay_excess_eq_balanceImbalance_of_dominant
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hDominant : H3TerminalDecayDominantPolynomialRatesAt u T b t) :
    2 *
        ((- deriv (velocityH3EnergyAt u) t)
          - velocityH3DissipationAt u t)
      =
    h3TerminalBalanceImbalanceAt u t := by
  have hBalance :=
    deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3 hClass ht

  have hOrder := hDominant.2

  unfold h3TerminalBalanceImbalanceAt
  rw [abs_of_nonneg (sub_nonneg.mpr hOrder)]
  linarith

/-- A dominant decay channel is at least the full H³ dissipation. -/
theorem dissipation_le_negativeEnergyDerivative_of_decayDominant
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hDominant : H3TerminalDecayDominantPolynomialRatesAt u T b t) :
    velocityH3DissipationAt u t
      ≤
    - deriv (velocityH3EnergyAt u) t := by
  have hBalance :=
    deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3 hClass ht
  have hOrder := hDominant.2
  linarith

/-- If adverse transport is the dominant balance channel, its excess above
full dissipation is exactly half the channel imbalance. -/
theorem two_mul_transport_excess_eq_balanceImbalance_of_dominant
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hDominant : H3TerminalTransportDominantPolynomialRatesAt u T b t) :
    2 *
        ((- velocityH3TransportDerivativeAt u t)
          - velocityH3DissipationAt u t)
      =
    h3TerminalBalanceImbalanceAt u t := by
  have hBalance :=
    deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3 hClass ht

  have hOrder := hDominant.2

  unfold h3TerminalBalanceImbalanceAt
  rw [abs_of_nonpos (sub_nonpos.mpr hOrder)]
  linarith

/-- A dominant adverse-transport channel is at least the full H³ dissipation. -/
theorem dissipation_le_negativeTransport_of_transportDominant
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hDominant : H3TerminalTransportDominantPolynomialRatesAt u T b t) :
    velocityH3DissipationAt u t
      ≤
    - velocityH3TransportDerivativeAt u t := by
  have hBalance :=
    deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3 hClass ht
  have hOrder := hDominant.2
  linarith

end

end Euclidean
end Bridge
end PrimeTensor
