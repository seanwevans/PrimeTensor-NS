import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Growth.Log

/-!
# Path-specific logarithmic H³ growth blowup alternative

The universal proposition-level contrapositive is weaker than what the scalar
argument actually proves.  A single terminal H³ energy-class tail with finite

    ∫ max(0, d/dt log E_H3(t)) dt

already yields a uniform H³ bound on that tail and hence smooth continuation.

Therefore, if one particular admissible H³ path does not extend through its
terminal time, then the positive logarithmic H³-energy growth rate is
nonintegrable on every terminal energy-class tail of that path.

This is the sharp path-specific scalar blowup alternative associated with the
current continuation architecture.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- One-tail integrability of the positive logarithmic H³-energy growth rate is
already sufficient for terminal H³ control. -/
theorem terminalTailH3Control_of_integrablePositiveLogEnergyGrowthRateOnTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hLog :
      MeasureTheory.IntegrableOn
        (h3PathPositiveLogEnergyGrowthRate u)
        (Set.Ioo a T)) :
    TerminalTailH3Control u T := by

  have ha :
      a ∈ Set.Ioo (0 : ℝ) T :=
    hClass.terminal_start

  have hRateIntegrable :
      MeasureTheory.IntegrableOn
        (h3PathPositiveEnergyGrowthRate u)
        (Set.Ioo a T) := by

    exact
      IntegrableOn.congr_fun
        hLog
        (fun t ht =>
          h3PathPositiveLogEnergyGrowthRate_eq_positiveEnergyGrowthRate
            hH3 hClass ht)
        measurableSet_Ioo

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

/-- One-tail finite positive logarithmic H³-energy variation is sufficient for
smooth continuation of the given path. -/
theorem h3PathExtension_of_integrablePositiveLogEnergyGrowthRateOnTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hLog :
      MeasureTheory.IntegrableOn
        (h3PathPositiveLogEnergyGrowthRate u)
        (Set.Ioo a T)) :
    ∃
      v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  have hTail :
      TerminalTailH3Control u T :=
    terminalTailH3Control_of_integrablePositiveLogEnergyGrowthRateOnTail
      hH3 hClass hLog

  exact
    h3PathH3ControlProducesExtension
      u T
      hH3
      hTail

/-- Sharp path-specific blowup alternative: if this path does not extend, then
its positive logarithmic H³-energy growth rate is nonintegrable on every
terminal H³ energy-class tail. -/
theorem not_integrablePositiveLogEnergyGrowthRateOnEveryTail_of_noH3PathExtension
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
          (h3PathPositiveLogEnergyGrowthRate u)
          (Set.Ioo a T) := by

  intro a hClass hLog

  exact
    hNoExtension
      (h3PathExtension_of_integrablePositiveLogEnergyGrowthRateOnTail
        hH3 hClass hLog)

end

end Euclidean
end Bridge
end PrimeTensor
