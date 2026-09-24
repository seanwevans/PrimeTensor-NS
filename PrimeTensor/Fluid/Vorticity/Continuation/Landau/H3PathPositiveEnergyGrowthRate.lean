import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathTransportExcessRate

/-!
# Minimal positive H³ energy-growth rate

The transport excess rate is the minimal coefficient for the stronger mixed
coercive estimate

    -T_H3 ≤ D_H3 + q E_H3.

For continuation itself, the exact scalar requirement is weaker.  Since the
normalized canonical H³ energy satisfies `E_H3 ≥ 1`, define

    r(t) = max(0, E_H3'(t) / E_H3(t)).

Then

    E_H3'(t) ≤ r(t) E_H3(t),

and `r` is the pointwise minimal nonnegative coefficient with that property.

On every strict H³ energy-class slice, exact dissipative balance shows

    r(t) ≤ q(t),

so the transport excess frontier is genuinely stronger than the minimal scalar
continuation frontier.

If `r ∈ L¹(a,T)` on each terminal H³ energy-class tail, the existing scalar
Grönwall machinery gives uniform terminal H³ control and the already-closed
restart theorem yields smooth continuation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Minimal nonnegative normalized positive growth rate of the canonical H³
energy. -/
noncomputable def h3PathPositiveEnergyGrowthRate
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) :
    ℝ → ℝ :=
  fun t =>
    max
      0
      (
        deriv (velocityH3EnergyAt u) t
          /
        velocityH3EnergyAt u t
      )

theorem h3PathPositiveEnergyGrowthRate_nonneg
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) :
    0 ≤ h3PathPositiveEnergyGrowthRate u t := by
  unfold h3PathPositiveEnergyGrowthRate
  exact le_max_left _ _

/-- The canonical positive growth rate always controls the energy derivative. -/
theorem deriv_velocityH3EnergyAt_le_positiveEnergyGrowthRate_mul_energy
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) :
    deriv (velocityH3EnergyAt u) t
      ≤
    h3PathPositiveEnergyGrowthRate u t
      * velocityH3EnergyAt u t := by

  have hEOne :
      1 ≤ velocityH3EnergyAt u t :=
    one_le_velocityH3EnergyAt u t

  have hEPos :
      0 < velocityH3EnergyAt u t := by
    linarith

  have hDiv :
      deriv (velocityH3EnergyAt u) t
          /
        velocityH3EnergyAt u t
        ≤
      h3PathPositiveEnergyGrowthRate u t := by

    unfold h3PathPositiveEnergyGrowthRate

    exact
      le_max_right
        0
        (
          deriv (velocityH3EnergyAt u) t
            /
          velocityH3EnergyAt u t
        )

  exact
    (div_le_iff₀ hEPos).1
      hDiv

/-- Minimality: every nonnegative scalar coefficient controlling `E'` by `c E`
dominates the canonical positive growth rate. -/
theorem h3PathPositiveEnergyGrowthRate_le_of_deriv_bound
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {c : ℝ → ℝ}
    {t : ℝ}
    (hc : 0 ≤ c t)
    (hGrowth :
      deriv (velocityH3EnergyAt u) t
        ≤
      c t * velocityH3EnergyAt u t) :
    h3PathPositiveEnergyGrowthRate u t ≤ c t := by

  have hEOne :
      1 ≤ velocityH3EnergyAt u t :=
    one_le_velocityH3EnergyAt u t

  have hEPos :
      0 < velocityH3EnergyAt u t := by
    linarith

  have hDiv :
      deriv (velocityH3EnergyAt u) t
          /
        velocityH3EnergyAt u t
        ≤
      c t := by

    exact
      (div_le_iff₀ hEPos).2
        hGrowth

  unfold h3PathPositiveEnergyGrowthRate

  exact
    max_le
      hc
      hDiv

/-- Exact dissipative balance shows that the scalar positive energy-growth rate
is pointwise no larger than the stronger transport excess rate. -/
theorem h3PathPositiveEnergyGrowthRate_le_transportExcessRate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3PathPositiveEnergyGrowthRate u t
      ≤
    h3PathTransportExcessRate u t := by

  have hGrowth :
      deriv (velocityH3EnergyAt u) t
        ≤
      h3PathTransportExcessRate u t
        * velocityH3EnergyAt u t :=
    deriv_velocityH3EnergyAt_le_of_transportAbsorption
      hH3
      hClass
      ht
      (h3TransportDissipationAbsorptionAt_transportExcessRate
        u t)

  exact
    h3PathPositiveEnergyGrowthRate_le_of_deriv_bound
      (h3PathTransportExcessRate_nonneg u t)
      hGrowth

/-- Explicit minimal scalar continuation frontier. -/
def H3PathEnergyClassProducesIntegrablePositiveEnergyGrowthRate : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalH3PathAdmissible u T →
      ∀ a : ℝ,
        ∀ hClass : PreterminalH3EnergyClass u a T,
          MeasureTheory.IntegrableOn
            (h3PathPositiveEnergyGrowthRate u)
            (Set.Ioo a T)

/-- Integrability of the minimal positive normalized energy-growth rate gives
uniform terminal H³ control directly. -/
theorem terminalTailH3Control_of_integrablePositiveEnergyGrowthRate
    (hRate :
      H3PathEnergyClassProducesIntegrablePositiveEnergyGrowthRate)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) :
    TerminalTailH3Control u T := by

  obtain
    ⟨a, hClass⟩ :=
    h3Preterminal_energyClass_of_h3PathAdmissible
      hH3

  have ha :
      a ∈ Set.Ioo (0 : ℝ) T :=
    hClass.terminal_start

  have hRateIntegrable :
      MeasureTheory.IntegrableOn
        (h3PathPositiveEnergyGrowthRate u)
        (Set.Ioo a T) :=
    hRate
      u T hH3
      a hClass

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
    exact (hProfile t ht).1

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
        (h3PathPositiveEnergyGrowthRate u)
        (velocityH3EnergyAt u)
        1 := by

    intro s hs

    have hLinear :
        deriv (velocityH3EnergyAt u) s
          ≤
        h3PathPositiveEnergyGrowthRate u s
          * velocityH3EnergyAt u s :=
      deriv_velocityH3EnergyAt_le_positiveEnergyGrowthRate_mul_energy
        u s

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

    have hRateNonneg :
        0 ≤ h3PathPositiveEnergyGrowthRate u s :=
      h3PathPositiveEnergyGrowthRate_nonneg u s

    have hRateAbs :
        |h3PathPositiveEnergyGrowthRate u s|
          =
        h3PathPositiveEnergyGrowthRate u s :=
      abs_of_nonneg hRateNonneg

    have hCoeff :
        h3PathPositiveEnergyGrowthRate u s
          ≤
        1 + |h3PathPositiveEnergyGrowthRate u s| := by
      rw [hRateAbs]
      linarith

    have hFirst :
        h3PathPositiveEnergyGrowthRate u s
            * velocityH3EnergyAt u s
          ≤
        (1 + |h3PathPositiveEnergyGrowthRate u s|)
            * velocityH3EnergyAt u s :=
      mul_le_mul_of_nonneg_right
        hCoeff
        hEsNonneg

    have hLogNonneg :
        0 ≤ Real.log (velocityH3EnergyAt u s) :=
      Real.log_nonneg hEsOne

    have hCoeffNonneg :
        0 ≤
          (1 + |h3PathPositiveEnergyGrowthRate u s|)
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
        h3PathPositiveEnergyGrowthRate u s
          * velocityH3EnergyAt u s :=
        hLinear

      _ ≤
        (1 + |h3PathPositiveEnergyGrowthRate u s|)
          * velocityH3EnergyAt u s :=
        hFirst

      _ ≤
        ((1 + |h3PathPositiveEnergyGrowthRate u s|)
          * velocityH3EnergyAt u s)
          *
        (1 + Real.log (velocityH3EnergyAt u s)) := by
        exact
          le_mul_of_one_le_right
            hCoeffNonneg
            hLogFactor

      _ =
        (1 : ℝ)
          * (1 + |h3PathPositiveEnergyGrowthRate u s|)
          * velocityH3EnergyAt u s
          * (1 + Real.log (velocityH3EnergyAt u s)) := by
        ring

  obtain
    ⟨M, hM, hEM⟩ :=
    logarithmicGronwallClosesEnergy_of_continuous_of_hasDeriv
      ha.2
      hRateIntegrable
      (by norm_num)
      hEOne
      hContinuous
      hDerivativeAt
      hGrowth

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

/-- The minimal scalar growth-rate frontier is sufficient for smooth
continuation of every admissible H³ path. -/
theorem everyH3PathPreterminalNavierStokesSolutionExtends_of_integrablePositiveEnergyGrowthRate
    (hRate :
      H3PathEnergyClassProducesIntegrablePositiveEnergyGrowthRate) :
    EveryH3PathPreterminalNavierStokesSolutionExtends := by

  intro u T hH3

  have hTail :
      TerminalTailH3Control u T :=
    terminalTailH3Control_of_integrablePositiveEnergyGrowthRate
      hRate
      hH3

  exact
    h3PathH3ControlProducesExtension
      u T
      hH3
      hTail

/-- Contrapositive: failure of H³-path continuation forces failure of the
universal integrability statement for the minimal positive normalized energy
growth rate. -/
theorem not_integrablePositiveEnergyGrowthRate_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T) :
    ¬ H3PathEnergyClassProducesIntegrablePositiveEnergyGrowthRate := by

  intro hRate

  exact
    hNoExtension
      (
        everyH3PathPreterminalNavierStokesSolutionExtends_of_integrablePositiveEnergyGrowthRate
          hRate
          u T hH3
      )

end

end Euclidean
end Bridge
end PrimeTensor
