import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Log.Alternative

/-!
# Exact full-dissipation transport excess rate

The exact H³ balance is

    E'(t) + 2 D(t) = -T_H3(t).

Therefore the minimal positive normalized scalar growth rate is not merely
bounded by a transport excess: it is exactly the positive part of transport
growth left after spending the *full* viscous dissipation,

    max(0, E'(t) / E(t))
      =
    max(0, (-T_H3(t) - 2 D(t)) / E(t)).

This file names that exact PDE quantity.  It is pointwise no larger than the
earlier one-copy excess rate

    max(0, (-T_H3(t) - D(t)) / E(t)),

and its terminal-tail integrability is exactly sufficient for the already
closed logarithmic-growth continuation theorem.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Positive normalized transport growth remaining after the complete H³
viscous dissipation has been spent. -/
noncomputable def h3PathFullDissipationTransportExcessRate
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) :
    ℝ → ℝ :=
  fun t =>
    max
      0
      (
        (
          - velocityH3TransportDerivativeAt u t
            - 2 * velocityH3DissipationAt u t
        )
          /
        velocityH3EnergyAt u t
      )

theorem h3PathFullDissipationTransportExcessRate_nonneg
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) :
    0 ≤ h3PathFullDissipationTransportExcessRate u t := by
  unfold h3PathFullDissipationTransportExcessRate
  exact le_max_left _ _

/-- Exact balance identifies the full-dissipation transport excess with the
minimal positive normalized H³-energy growth rate. -/
theorem h3PathFullDissipationTransportExcessRate_eq_positiveEnergyGrowthRate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3PathFullDissipationTransportExcessRate u t
      =
    h3PathPositiveEnergyGrowthRate u t := by

  have hBalance :=
    deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3 hClass ht

  have hDeriv :
      deriv (velocityH3EnergyAt u) t
        =
      - velocityH3TransportDerivativeAt u t
        - 2 * velocityH3DissipationAt u t := by
    linarith

  unfold
    h3PathFullDissipationTransportExcessRate
    h3PathPositiveEnergyGrowthRate

  rw [hDeriv]

/-- Hence the full-dissipation transport excess is also exactly the positive
logarithmic H³-energy variation density. -/
theorem h3PathFullDissipationTransportExcessRate_eq_positiveLogEnergyGrowthRate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3PathFullDissipationTransportExcessRate u t
      =
    h3PathPositiveLogEnergyGrowthRate u t := by

  rw [
    h3PathPositiveLogEnergyGrowthRate_eq_positiveEnergyGrowthRate
      hH3 hClass ht
  ]

  exact
    h3PathFullDissipationTransportExcessRate_eq_positiveEnergyGrowthRate
      hH3 hClass ht

/-- Spending both copies of dissipation can only reduce the earlier one-copy
transport excess rate. -/
theorem h3PathFullDissipationTransportExcessRate_le_transportExcessRate
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) :
    h3PathFullDissipationTransportExcessRate u t
      ≤
    h3PathTransportExcessRate u t := by

  have hEOne :
      1 ≤ velocityH3EnergyAt u t :=
    one_le_velocityH3EnergyAt u t

  have hEPos :
      0 < velocityH3EnergyAt u t := by
    linarith

  have hD :
      0 ≤ velocityH3DissipationAt u t :=
    velocityH3DissipationAt_nonneg u t

  have hNumerator :
      - velocityH3TransportDerivativeAt u t
          - 2 * velocityH3DissipationAt u t
        ≤
      - velocityH3TransportDerivativeAt u t
          - velocityH3DissipationAt u t := by
    linarith

  have hDiv :
      (
        - velocityH3TransportDerivativeAt u t
          - 2 * velocityH3DissipationAt u t
      )
        /
      velocityH3EnergyAt u t
        ≤
      (
        - velocityH3TransportDerivativeAt u t
          - velocityH3DissipationAt u t
      )
        /
      velocityH3EnergyAt u t := by

    exact
      (div_le_div_iff_of_pos_right hEPos).2
        hNumerator

  unfold
    h3PathFullDissipationTransportExcessRate
    h3PathTransportExcessRate

  exact
    max_le_max_left 0 hDiv

/-- Exact PDE form of the remaining minimal continuation frontier. -/
def H3PathEnergyClassProducesIntegrableFullDissipationTransportExcessRate :
    Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalH3PathAdmissible u T →
      ∀ a : ℝ,
        ∀ hClass : PreterminalH3EnergyClass u a T,
          MeasureTheory.IntegrableOn
            (h3PathFullDissipationTransportExcessRate u)
            (Set.Ioo a T)

/-- Integrability of the exact full-dissipation PDE excess rate is the same
input needed by the positive logarithmic-growth continuation interface. -/
theorem h3PathEnergyClassProducesIntegrablePositiveLogEnergyGrowthRate_of_fullDissipationExcess
    (hRate :
      H3PathEnergyClassProducesIntegrableFullDissipationTransportExcessRate) :
    H3PathEnergyClassProducesIntegrablePositiveLogEnergyGrowthRate := by

  intro u T hH3 a hClass

  have hInt :
      MeasureTheory.IntegrableOn
        (h3PathFullDissipationTransportExcessRate u)
        (Set.Ioo a T) :=
    hRate u T hH3 a hClass

  exact
    IntegrableOn.congr_fun
      hInt
      (fun t ht =>
        h3PathFullDissipationTransportExcessRate_eq_positiveLogEnergyGrowthRate
          hH3 hClass ht)
      measurableSet_Ioo

/-- The exact full-dissipation transport excess frontier is sufficient for
smooth continuation of every admissible H³ path. -/
theorem everyH3PathPreterminalNavierStokesSolutionExtends_of_integrableFullDissipationTransportExcessRate
    (hRate :
      H3PathEnergyClassProducesIntegrableFullDissipationTransportExcessRate) :
    EveryH3PathPreterminalNavierStokesSolutionExtends := by

  exact
    everyH3PathPreterminalNavierStokesSolutionExtends_of_integrablePositiveLogEnergyGrowthRate
      (h3PathEnergyClassProducesIntegrablePositiveLogEnergyGrowthRate_of_fullDissipationExcess
        hRate)

/-- Path-specific contrapositive: a non-extendible H³ path must have
nonintegrable full-dissipation transport excess on every terminal energy-class
tail. -/
theorem not_integrableFullDissipationTransportExcessRateOnEveryTail_of_noH3PathExtension
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
          (h3PathFullDissipationTransportExcessRate u)
          (Set.Ioo a T) := by

  intro a hClass hInt

  have hLog :
      MeasureTheory.IntegrableOn
        (h3PathPositiveLogEnergyGrowthRate u)
        (Set.Ioo a T) := by

    exact
      IntegrableOn.congr_fun
        hInt
        (fun t ht =>
          h3PathFullDissipationTransportExcessRate_eq_positiveLogEnergyGrowthRate
            hH3 hClass ht)
        measurableSet_Ioo

  exact
    hNoExtension
      (h3PathExtension_of_integrablePositiveLogEnergyGrowthRateOnTail
        hH3 hClass hLog)

end

end Euclidean
end Bridge
end PrimeTensor
