import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.TransportExcessRateCascade
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Transport.Excess.Full
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Third.Rate.Dissipation.TransportIntegrability

/-!
# Exact decomposition of the one-copy H³ transport excess

The one-copy transport excess is

    q(t) =
      max 0 ((-T_H3(t) - D(t)) / E(t)).

On every strict H³ energy-class slice, exact balance gives

    -T_H3(t) = E'(t) + 2 D(t),

hence

    q(t) =
      max 0 ((E'(t) + D(t)) / E(t)).

This identifies the precise active set for the one-copy excess:

* if `E'(t) + D(t) ≤ 0`, then `q(t) = 0`;
* if `0 < E'(t) + D(t)`, then
  `q(t) = (E'(t) + D(t)) / E(t)`;
* in particular, if `E'(t) ≥ 0`, then

      q(t) = E'(t)/E(t) + D(t)/E(t).

The genuinely minimal scalar continuation coefficient remains the positive
logarithmic energy-growth rate

    r(t) = max(0, E'(t)/E(t)),

and pointwise `r(t) ≤ q(t)` on every strict energy-class slice.

Finally, integrability of `q` on even one terminal energy-class tail already
forces continuation, so hypothetical nonextension makes `q` nonintegrable on
every such tail.

This file is deliberately a reduction, not a new analytic estimate: it
prevents the larger one-copy coefficient from being mistaken for a smaller
frontier than positive logarithmic H³-energy variation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Exact balance form -/

/--
Exact balance rewrites the one-copy transport excess as the positive part of

    (E' + D) / E.
-/
theorem h3PathTransportExcessRate_eq_max_zero_deriv_add_dissipation_div_energy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3PathTransportExcessRate u t
      =
    max
      0
      (
        (
          deriv (velocityH3EnergyAt u) t
            +
          velocityH3DissipationAt u t
        )
          /
        velocityH3EnergyAt u t
      ) := by

  have hBalance :=
    deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3
      hClass
      ht

  have hNumerator :
      - velocityH3TransportDerivativeAt u t
          - velocityH3DissipationAt u t
        =
      deriv (velocityH3EnergyAt u) t
          + velocityH3DissipationAt u t := by
    linarith

  unfold h3PathTransportExcessRate

  rw [hNumerator]

/-! ## Active / inactive sign split -/

/--
If the energy derivative plus one copy of dissipation is nonpositive, the
one-copy transport excess vanishes exactly.
-/
theorem h3PathTransportExcessRate_eq_zero_of_deriv_add_dissipation_nonpos
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hInactive :
      deriv (velocityH3EnergyAt u) t
          +
        velocityH3DissipationAt u t
        ≤
      0) :
    h3PathTransportExcessRate u t = 0 := by

  have hEOne :
      1 ≤ velocityH3EnergyAt u t :=
    one_le_velocityH3EnergyAt u t

  have hENonneg :
      0 ≤ velocityH3EnergyAt u t := by
    linarith

  rw [
    h3PathTransportExcessRate_eq_max_zero_deriv_add_dissipation_div_energy
      hH3
      hClass
      ht
  ]

  have hRatioNonpos :
      (
        deriv (velocityH3EnergyAt u) t
            +
          velocityH3DissipationAt u t
      )
          /
        velocityH3EnergyAt u t
        ≤
      0 :=
    div_nonpos_of_nonpos_of_nonneg
      hInactive
      hENonneg

  exact
    max_eq_left
      hRatioNonpos

/--
On the active set `0 < E' + D`, the max disappears and the one-copy transport
excess is exactly `(E' + D) / E`.
-/
theorem h3PathTransportExcessRate_eq_deriv_add_dissipation_div_energy_of_pos
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hActive :
      0
        <
      deriv (velocityH3EnergyAt u) t
        +
      velocityH3DissipationAt u t) :
    h3PathTransportExcessRate u t
      =
    (
      deriv (velocityH3EnergyAt u) t
        +
      velocityH3DissipationAt u t
    )
      /
    velocityH3EnergyAt u t := by

  have hEOne :
      1 ≤ velocityH3EnergyAt u t :=
    one_le_velocityH3EnergyAt u t

  have hEPos :
      0 < velocityH3EnergyAt u t := by
    linarith

  rw [
    h3PathTransportExcessRate_eq_max_zero_deriv_add_dissipation_div_energy
      hH3
      hClass
      ht
  ]

  have hRatioPos :
      0
        <
      (
        deriv (velocityH3EnergyAt u) t
            +
          velocityH3DissipationAt u t
      )
        /
      velocityH3EnergyAt u t :=
    div_pos
      hActive
      hEPos

  exact
    max_eq_right
      (le_of_lt hRatioPos)

/--
At nonnegative H³-energy growth times, the one-copy excess splits exactly into

    E'/E + D/E.
-/
theorem h3PathTransportExcessRate_eq_deriv_div_energy_add_dissipation_div_energy_of_nonnegative_deriv
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hDerivative :
      0 ≤ deriv (velocityH3EnergyAt u) t) :
    h3PathTransportExcessRate u t
      =
    deriv (velocityH3EnergyAt u) t
        /
      velocityH3EnergyAt u t
      +
    velocityH3DissipationAt u t
        /
      velocityH3EnergyAt u t := by

  have hDNonneg :
      0 ≤ velocityH3DissipationAt u t :=
    velocityH3DissipationAt_nonneg
      u t

  have hEOne :
      1 ≤ velocityH3EnergyAt u t :=
    one_le_velocityH3EnergyAt u t

  have hENonneg :
      0 ≤ velocityH3EnergyAt u t := by
    linarith

  have hNumeratorNonneg :
      0
        ≤
      deriv (velocityH3EnergyAt u) t
        +
      velocityH3DissipationAt u t :=
    add_nonneg
      hDerivative
      hDNonneg

  rw [
    h3PathTransportExcessRate_eq_max_zero_deriv_add_dissipation_div_energy
      hH3
      hClass
      ht
  ]

  have hRatioNonneg :
      0
        ≤
      (
        deriv (velocityH3EnergyAt u) t
            +
          velocityH3DissipationAt u t
      )
        /
      velocityH3EnergyAt u t :=
    div_nonneg
      hNumeratorNonneg
      hENonneg

  rw [
    max_eq_right
      hRatioNonneg
  ]

  ring

/-! ## The positive logarithmic growth rate is the smaller frontier -/

/--
The positive logarithmic H³-energy growth rate is pointwise no larger than the
one-copy transport excess on every strict energy-class slice.
-/
theorem h3PathPositiveLogEnergyGrowthRate_le_transportExcessRate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3PathPositiveLogEnergyGrowthRate u t
      ≤
    h3PathTransportExcessRate u t := by

  rw [
    h3PathPositiveLogEnergyGrowthRate_eq_positiveEnergyGrowthRate
      hH3
      hClass
      ht
  ]

  exact
    h3PathPositiveEnergyGrowthRate_le_transportExcessRate
      hH3
      hClass
      ht

/-! ## Path-specific continuation and nonintegrability -/

/--
Integrability of the explicit one-copy transport excess on one terminal
H³-energy-class tail already forces smooth continuation of that path.
-/
theorem h3PathExtension_of_integrableTransportExcessRateOnTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hRate :
      MeasureTheory.IntegrableOn
        (h3PathTransportExcessRate u)
        (Set.Ioo a T)) :
    ∃
      v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  exact
    h3PathExtension_of_transportDissipationAbsorptionOnTail
      hH3
      hClass
      hRate
      (
        fun t _ht =>
          h3TransportDissipationAbsorptionAt_transportExcessRate
            u t
      )

/--
Hypothetical nonextension forces the explicit one-copy transport excess to be
nonintegrable on every terminal H³-energy-class tail.
-/
theorem not_integrableTransportExcessRateOnEveryTail_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T) :
    ∀
      (a : ℝ)
      (hClass : PreterminalH3EnergyClass u a T),
      ¬ MeasureTheory.IntegrableOn
          (h3PathTransportExcessRate u)
          (Set.Ioo a T) := by

  intro a hClass hRate

  exact
    hNoExtension
      (
        h3PathExtension_of_integrableTransportExcessRateOnTail
          hH3
          hClass
          hRate
      )

/--
Every strict subtail inherits the same one-copy excess nonintegrability
obstruction.
-/
theorem not_integrableTransportExcessRateOnStrictSubtail_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    ¬ MeasureTheory.IntegrableOn
        (h3PathTransportExcessRate u)
        (Set.Ioo b T) := by

  have hClassB :
      PreterminalH3EnergyClass u b T :=
    preterminalH3EnergyClass_restrict_left
      hClass
      (le_of_lt hb.1)
      hb.2

  exact
    not_integrableTransportExcessRateOnEveryTail_of_noH3PathExtension
      hH3
      hNoExtension
      b
      hClassB

end

end Euclidean
end Bridge
end PrimeTensor
