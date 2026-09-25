import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Third.Rate.Dissipation.TransportIntegrability

/-!
# Terminal nonintegrability of positive H³-energy variation

The exact full-dissipation transport excess already isolates the normalized
positive H³-energy growth rate.  Here we remove the normalization.

For any terminal H³ energy-class tail, an integrable scalar coefficient `c`
satisfying

    E'(t) ≤ c(t) E(t)

is enough for the existing scalar logarithmic Grönwall argument and closed
restart theorem to continue the path through `T`.

Apply this with the canonical raw positive energy derivative

    P(t) = max(0, E'(t)).

Because the normalized canonical H³ energy satisfies `E(t) ≥ 1`,

    E'(t) ≤ P(t) ≤ P(t) E(t).

Hence `P ∈ L¹(a,T)` would force continuation.  Contrapositively, hypothetical
nonextension forces

    max(0, E'(t)) ∉ L¹(a,T)

on every terminal H³ energy-class tail.

The exact dissipative balance

    E'(t) + 2 D(t) = -T_H3(t)

then identifies the same raw positive variation with

    max(0, -T_H3(t) - 2 D(t)).

Thus nonextension forces nonintegrability of the *unnormalized* transport
excess remaining after both copies of viscous dissipation are paid.

This is stronger than raw adverse-transport nonintegrability, while remaining
a necessary condition on the hypothetical nonextension branch.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## One-tail continuation from an integrable linear energy majorant -/

/--
A single terminal H³ energy-class tail with an integrable scalar coefficient
satisfying `E' ≤ c E` already gives smooth continuation.
-/
theorem h3PathExtension_of_integrableLinearEnergyGrowthMajorantOnTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    {c : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hcIntegrable :
      MeasureTheory.IntegrableOn
        c
        (Set.Ioo a T))
    (hLinear :
      ∀ t : ℝ,
        t ∈ Set.Ioo a T →
          deriv (velocityH3EnergyAt u) t
            ≤
          c t * velocityH3EnergyAt u t) :
    ∃
      v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  have ha :
      a ∈ Set.Ioo (0 : ℝ) T :=
    hClass.terminal_start

  have hProfile :
      H3EnergyProfileFrom
        u a T
        (velocityH3EnergyAt u) :=
    h3EnergyProfileFrom_h3Path
      hH3 ha

  have hEOne :
      ∀ t : ℝ,
        t ∈ Set.Ico a T →
          1 ≤ velocityH3EnergyAt u t := by

    intro t ht

    exact
      (hProfile t ht).1

  have hContinuous :
      ∀ q : ℝ,
        q ∈ Set.Ico a T →
          ContinuousOn
            (velocityH3EnergyAt u)
            (Set.Icc a q) :=
    hH3.canonicalH3EnergyContinuousOnTail
      ha

  have hDerivativeAt :
      ∀ s : ℝ,
        s ∈ Set.Ioo a T →
          HasDerivAt
            (velocityH3EnergyAt u)
            (deriv (velocityH3EnergyAt u) s)
            s := by

    intro s hs

    have hIds :
        H3OrderEnergyDerivativeIdentities u s :=
      h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed
        u T hH3
        a hClass
        s hs

    have hDeriv :
        deriv (velocityH3EnergyAt u) s
          =
        velocityH3FormalDerivativeAt u s :=
      deriv_velocityH3EnergyAt
        hIds

    rw [hDeriv]

    exact
      hasDerivAt_velocityH3EnergyAt
        hIds

  have hGrowth :
      BKMLogGrowthInequalityFrom
        a T
        c
        (velocityH3EnergyAt u)
        1 := by

    intro s hs

    have hEsOne :
        1 ≤ velocityH3EnergyAt u s :=
      hEOne
        s
        ⟨
          le_of_lt hs.1,
          hs.2
        ⟩

    have hEsNonneg :
        0 ≤ velocityH3EnergyAt u s := by
      linarith

    have hLogNonneg :
        0 ≤ Real.log (velocityH3EnergyAt u s) :=
      Real.log_nonneg
        hEsOne

    have hcUpper :
        c s ≤ 1 + |c s| := by
      have hle :
          c s ≤ |c s| :=
        le_abs_self (c s)
      linarith

    have hFirst :
        c s * velocityH3EnergyAt u s
          ≤
        (1 + |c s|)
          * velocityH3EnergyAt u s :=
      mul_le_mul_of_nonneg_right
        hcUpper
        hEsNonneg

    have hCoeffNonneg :
        0 ≤
          (1 + |c s|)
            * velocityH3EnergyAt u s :=
      mul_nonneg
        (by positivity)
        hEsNonneg

    have hLogFactor :
        1 ≤ 1 + Real.log (velocityH3EnergyAt u s) := by
      linarith

    calc
      deriv (velocityH3EnergyAt u) s
          ≤
        c s * velocityH3EnergyAt u s :=
        hLinear s hs

      _ ≤
        (1 + |c s|)
          * velocityH3EnergyAt u s :=
        hFirst

      _ ≤
        ((1 + |c s|)
          * velocityH3EnergyAt u s)
          *
        (1 + Real.log (velocityH3EnergyAt u s)) := by

        exact
          le_mul_of_one_le_right
            hCoeffNonneg
            hLogFactor

      _ =
        (1 : ℝ)
          * (1 + |c s|)
          * velocityH3EnergyAt u s
          * (1 + Real.log (velocityH3EnergyAt u s)) := by
        ring

  obtain
    ⟨M, hM, hEM⟩ :=
    logarithmicGronwallClosesEnergy_of_continuous_of_hasDeriv
      ha.2
      hcIntegrable
      (by norm_num)
      hEOne
      hContinuous
      hDerivativeAt
      hGrowth

  have hTail :
      TerminalTailH3Control u T := by

    refine
      ⟨
        a,
        M,
        ha,
        hM,
        ?_
      ⟩

    intro t ht

    exact
      velocityH3BoundAt_mono
        (hProfile t ht).2
        (hEM t ht)

  exact
    h3PathH3ControlProducesExtension
      u T hH3 hTail

/-! ## Raw positive H³-energy derivative -/

/-- Positive part of the raw canonical H³-energy time derivative. -/
noncomputable def h3PathPositiveEnergyTimeDerivativePart
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) :
    ℝ → ℝ :=
  fun t =>
    max
      0
      (deriv (velocityH3EnergyAt u) t)

theorem h3PathPositiveEnergyTimeDerivativePart_nonneg
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) :
    0 ≤ h3PathPositiveEnergyTimeDerivativePart u t := by

  unfold h3PathPositiveEnergyTimeDerivativePart

  exact
    le_max_left
      0
      (deriv (velocityH3EnergyAt u) t)

/--
The raw positive energy derivative is a valid linear growth coefficient because
the canonical normalized H³ energy is at least one.
-/
theorem deriv_velocityH3EnergyAt_le_positiveEnergyTimeDerivativePart_mul_energy
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) :
    deriv (velocityH3EnergyAt u) t
      ≤
    h3PathPositiveEnergyTimeDerivativePart u t
      * velocityH3EnergyAt u t := by

  have hDerivative :
      deriv (velocityH3EnergyAt u) t
        ≤
      h3PathPositiveEnergyTimeDerivativePart u t := by

    unfold h3PathPositiveEnergyTimeDerivativePart

    exact
      le_max_right
        0
        (deriv (velocityH3EnergyAt u) t)

  have hPartNonneg :
      0 ≤ h3PathPositiveEnergyTimeDerivativePart u t :=
    h3PathPositiveEnergyTimeDerivativePart_nonneg
      u t

  have hEOne :
      1 ≤ velocityH3EnergyAt u t :=
    one_le_velocityH3EnergyAt
      u t

  have hScale :
      h3PathPositiveEnergyTimeDerivativePart u t
        ≤
      h3PathPositiveEnergyTimeDerivativePart u t
        * velocityH3EnergyAt u t := by

    calc
      h3PathPositiveEnergyTimeDerivativePart u t
          =
        h3PathPositiveEnergyTimeDerivativePart u t * 1 := by
        ring

      _ ≤
        h3PathPositiveEnergyTimeDerivativePart u t
          * velocityH3EnergyAt u t :=
        mul_le_mul_of_nonneg_left
          hEOne
          hPartNonneg

  exact
    le_trans
      hDerivative
      hScale

/--
Integrability of the raw positive H³-energy derivative on one terminal
energy-class tail forces continuation.
-/
theorem h3PathExtension_of_integrablePositiveEnergyTimeDerivativePartOnTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hPositive :
      MeasureTheory.IntegrableOn
        (h3PathPositiveEnergyTimeDerivativePart u)
        (Set.Ioo a T)) :
    ∃
      v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  exact
    h3PathExtension_of_integrableLinearEnergyGrowthMajorantOnTail
      hH3
      hClass
      hPositive
      (fun t _ =>
        deriv_velocityH3EnergyAt_le_positiveEnergyTimeDerivativePart_mul_energy
          u t)

/--
Hypothetical nonextension forces infinite raw positive H³-energy variation on
every terminal H³ energy-class tail.
-/
theorem not_integrableOn_positiveEnergyTimeDerivativePart_on_energyClassTail_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ¬ MeasureTheory.IntegrableOn
        (h3PathPositiveEnergyTimeDerivativePart u)
        (Set.Ioo a T) := by

  intro hPositive

  exact
    hNoExtension
      (h3PathExtension_of_integrablePositiveEnergyTimeDerivativePartOnTail
        hH3
        hClass
        hPositive)

/-! ## Exact raw full-dissipation transport excess -/

/--
Unnormalized positive transport excess remaining after both copies of viscous
dissipation have been paid.
-/
noncomputable def h3PathRawFullDissipationTransportExcessPart
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) :
    ℝ → ℝ :=
  fun t =>
    max
      0
      (
        - velocityH3TransportDerivativeAt u t
          - 2 * velocityH3DissipationAt u t
      )

/--
Exact balance identifies raw full-dissipation transport excess with the raw
positive H³-energy derivative.
-/
theorem h3PathRawFullDissipationTransportExcessPart_eq_positiveEnergyTimeDerivativePart
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3PathRawFullDissipationTransportExcessPart u t
      =
    h3PathPositiveEnergyTimeDerivativePart u t := by

  have hBalance :=
    deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3
      hClass
      ht

  have hDerivative :
      deriv (velocityH3EnergyAt u) t
        =
      - velocityH3TransportDerivativeAt u t
        - 2 * velocityH3DissipationAt u t := by
    linarith

  unfold
    h3PathRawFullDissipationTransportExcessPart
    h3PathPositiveEnergyTimeDerivativePart

  rw [hDerivative]

/--
Consequently hypothetical nonextension forces the unnormalized positive
full-dissipation transport excess to be nonintegrable on every terminal H³
energy-class tail.
-/
theorem not_integrableOn_rawFullDissipationTransportExcessPart_on_energyClassTail_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ¬ MeasureTheory.IntegrableOn
        (h3PathRawFullDissipationTransportExcessPart u)
        (Set.Ioo a T) := by

  intro hRaw

  have hPositive :
      MeasureTheory.IntegrableOn
        (h3PathPositiveEnergyTimeDerivativePart u)
        (Set.Ioo a T) := by

    exact
      IntegrableOn.congr_fun
        hRaw
        (fun t ht =>
          h3PathRawFullDissipationTransportExcessPart_eq_positiveEnergyTimeDerivativePart
            hH3
            hClass
            ht)
        measurableSet_Ioo

  exact
    not_integrableOn_positiveEnergyTimeDerivativePart_on_energyClassTail_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hPositive

end

end Euclidean
end Bridge
end PrimeTensor
