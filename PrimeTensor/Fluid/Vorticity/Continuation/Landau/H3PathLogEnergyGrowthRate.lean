import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathPositiveEnergyGrowthRate

/-!
# Positive logarithmic H³-energy growth rate

The previous scalar frontier isolated

    r(t) = max(0, E'(t) / E(t)).

Because the normalized canonical H³ energy satisfies `E(t) ≥ 1`, every strict
H³ energy-class time has `E(t) ≠ 0`, and the ordinary logarithmic chain rule
gives

    deriv (log E) t = E'(t) / E(t).

Hence the minimal positive energy-growth rate is exactly

    r(t) = max(0, deriv (log E) t).

This removes even the quotient from the continuation frontier.  The remaining
scalar condition is simply integrability of the positive logarithmic variation
density of the H³ energy on each terminal energy-class tail.

This is a reformulation, not an additional estimate: proving this integrability
still carries the open-strength content.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Positive part of the time derivative of the logarithmic canonical H³
energy. -/
noncomputable def h3PathPositiveLogEnergyGrowthRate
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) :
    ℝ → ℝ :=
  fun t =>
    max
      0
      (
        deriv
          (fun s : ℝ =>
            Real.log (velocityH3EnergyAt u s))
          t
      )

theorem h3PathPositiveLogEnergyGrowthRate_nonneg
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) :
    0 ≤ h3PathPositiveLogEnergyGrowthRate u t := by
  unfold h3PathPositiveLogEnergyGrowthRate
  exact le_max_left _ _

/-- On every strict H³ energy-class slice, the logarithmic energy derivative is
exactly the normalized energy derivative. -/
theorem deriv_log_velocityH3EnergyAt_eq_div
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    deriv
        (fun s : ℝ =>
          Real.log (velocityH3EnergyAt u s))
        t
      =
    deriv (velocityH3EnergyAt u) t
      /
    velocityH3EnergyAt u t := by

  have hIds :
      H3OrderEnergyDerivativeIdentities u t :=
    h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed
      u T hH3
      a hClass
      t ht

  have hDeriv :
      deriv (velocityH3EnergyAt u) t
        =
      velocityH3FormalDerivativeAt u t :=
    deriv_velocityH3EnergyAt
      hIds

  have hEnergyDeriv :
      HasDerivAt
        (velocityH3EnergyAt u)
        (deriv (velocityH3EnergyAt u) t)
        t := by

    rw [hDeriv]

    exact
      hasDerivAt_velocityH3EnergyAt
        hIds

  have hEOne :
      1 ≤ velocityH3EnergyAt u t :=
    one_le_velocityH3EnergyAt u t

  have hENe :
      velocityH3EnergyAt u t ≠ 0 := by
    exact
      ne_of_gt
        (lt_of_lt_of_le
          zero_lt_one
          hEOne)

  exact
    (hEnergyDeriv.log hENe).deriv

/-- The previous minimal normalized positive growth rate is literally the
positive part of the logarithmic H³-energy derivative. -/
theorem h3PathPositiveLogEnergyGrowthRate_eq_positiveEnergyGrowthRate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3PathPositiveLogEnergyGrowthRate u t
      =
    h3PathPositiveEnergyGrowthRate u t := by

  unfold
    h3PathPositiveLogEnergyGrowthRate
    h3PathPositiveEnergyGrowthRate

  rw [
    deriv_log_velocityH3EnergyAt_eq_div
      hH3 hClass ht
  ]

/-- Pure logarithmic form of the remaining minimal scalar continuation
frontier. -/
def H3PathEnergyClassProducesIntegrablePositiveLogEnergyGrowthRate : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalH3PathAdmissible u T →
      ∀ a : ℝ,
        ∀ hClass : PreterminalH3EnergyClass u a T,
          MeasureTheory.IntegrableOn
            (h3PathPositiveLogEnergyGrowthRate u)
            (Set.Ioo a T)

/-- Integrability of the positive logarithmic variation density is exactly
enough to discharge the previous minimal scalar frontier. -/
theorem h3PathEnergyClassProducesIntegrablePositiveEnergyGrowthRate_of_log
    (hLog :
      H3PathEnergyClassProducesIntegrablePositiveLogEnergyGrowthRate) :
    H3PathEnergyClassProducesIntegrablePositiveEnergyGrowthRate := by

  intro u T hH3 a hClass

  have hInt :
      MeasureTheory.IntegrableOn
        (h3PathPositiveLogEnergyGrowthRate u)
        (Set.Ioo a T) :=
    hLog u T hH3 a hClass

  exact
    IntegrableOn.congr_fun
      hInt
      (fun t ht =>
        h3PathPositiveLogEnergyGrowthRate_eq_positiveEnergyGrowthRate
          hH3 hClass ht)
      measurableSet_Ioo

/-- Finite positive logarithmic H³-energy variation on every terminal
energy-class tail is sufficient for smooth continuation of every admissible
H³ path. -/
theorem everyH3PathPreterminalNavierStokesSolutionExtends_of_integrablePositiveLogEnergyGrowthRate
    (hLog :
      H3PathEnergyClassProducesIntegrablePositiveLogEnergyGrowthRate) :
    EveryH3PathPreterminalNavierStokesSolutionExtends := by

  exact
    everyH3PathPreterminalNavierStokesSolutionExtends_of_integrablePositiveEnergyGrowthRate
      (h3PathEnergyClassProducesIntegrablePositiveEnergyGrowthRate_of_log
        hLog)

/-- Contrapositive: failure of H³-path continuation forces failure of the
universal positive logarithmic variation integrability statement. -/
theorem not_integrablePositiveLogEnergyGrowthRate_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T) :
    ¬ H3PathEnergyClassProducesIntegrablePositiveLogEnergyGrowthRate := by

  intro hLog

  exact
    hNoExtension
      (
        everyH3PathPreterminalNavierStokesSolutionExtends_of_integrablePositiveLogEnergyGrowthRate
          hLog
          u T hH3
      )

end

end Euclidean
end Bridge
end PrimeTensor
