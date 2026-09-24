import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathLandauAbsorptionLoop
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathAnalyticOnly
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathDirectRestart

/-!
# Transport-dissipation absorption implies H³-path continuation

The exact dissipative balance has reduced the remaining global H³-path problem
to one genuinely nonlinear estimate:

    -T_H3(t) ≤ D_H3(t) + c(t) E_H3(t),

with `c ∈ L¹(a,T)` on every terminal H³ energy-class tail.

Once this estimate is available, the rest is scalar and continuation-theoretic:

    E'(t) + D(t) ≤ c(t) E(t)
    E'(t) ≤ c(t) E(t),

and the existing scalar Grönwall/Osgood infrastructure gives a uniform H³
bound on the terminal tail.  The already-closed H³ restart theorem then
extends the solution smoothly through `T`.

No vorticity hypothesis is used in this file.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The transport/dissipation absorption frontier produces uniform terminal
H³ control directly, with no vorticity-control premise. -/
theorem terminalTailH3Control_of_transportDissipationAbsorption
    (hAbsorption :
      H3PathEnergyClassProducesTransportDissipationAbsorption)
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

  obtain
    ⟨c, hcIntegrable, hAbsorb⟩ :=
    hAbsorption
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

  have hLinearGrowth :
      ∀ s : ℝ,
        s ∈ Set.Ioo a T →
          deriv (velocityH3EnergyAt u) s
            ≤
          c s * velocityH3EnergyAt u s := by

    intro s hs

    exact
      deriv_velocityH3EnergyAt_le_of_transportAbsorption
        hH3
        hClass
        hs
        (hAbsorb s hs)

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
        hLinearGrowth s hs

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

/-- The mixed coercive transport frontier is sufficient for smooth
continuation of every admissible H³ path. -/
theorem everyH3PathPreterminalNavierStokesSolutionExtends_of_transportDissipationAbsorption
    (hAbsorption :
      H3PathEnergyClassProducesTransportDissipationAbsorption) :
    EveryH3PathPreterminalNavierStokesSolutionExtends := by

  intro u T hH3

  have hTail :
      TerminalTailH3Control u T :=
    terminalTailH3Control_of_transportDissipationAbsorption
      hAbsorption
      hH3

  exact
    h3PathH3ControlProducesExtension
      u T
      hH3
      hTail

/-- Contrapositive: any non-extendible admissible H³ path witnesses failure of
the mixed transport/dissipation absorption frontier on some energy-class
tail. -/
theorem not_transportDissipationAbsorption_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T) :
    ¬ H3PathEnergyClassProducesTransportDissipationAbsorption := by

  intro hAbsorption

  exact
    hNoExtension
      (
        everyH3PathPreterminalNavierStokesSolutionExtends_of_transportDissipationAbsorption
          hAbsorption
          u T hH3
      )

end

end Euclidean
end Bridge
end PrimeTensor
