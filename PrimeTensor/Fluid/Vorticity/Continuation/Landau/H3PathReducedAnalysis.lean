import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathCanonicalSelected
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathCanonicalDataReduction
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathDirectRestart

/-!
# H³-path BKM continuation from the reduced canonical-analysis frontier

The H³-path route has now removed the old global
`EnergyClassProducesCanonicalH3Data` interface from the continuation half:

* `LoggedPreterminalH3PathAdmissible` supplies scalar H³-energy continuity;
* terminal-tail H³ control therefore gives the pressure-free real restart
  directly.

`H3PathCanonicalDataReduction` also showed that, on the corrected strong
solution class, the canonical data consumed by the BKM growth argument are
equivalent to only

* local `C¹` regularity of `velocityH3EnergyAt`;
* `H3EnergyEstimateAnalyticOnTail`.

This file rethreads the canonical selected BKM proof through exactly that
reduced path-specific interface.

Consequently the resulting continuation criterion has one remaining named
analytic frontier:

    H3PathEnergyClassProducesCanonicalAnalysis.

There is no global canonical-data hypothesis and no continuation-side analytic
hypothesis.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory

noncomputable section

/--
The canonical selected BKM estimate closes terminal-tail H³ control from the
reduced H³-path canonical-analysis frontier.

The proof is the existing canonical-selected endpoint argument, with the
complete canonical data at the selected old energy-class tail reconstructed
from the path-specific analysis theorem.
-/
theorem h3PathVorticityL1LinfProducesH3Control_of_reducedCanonicalAnalysis
    (hAnalysis :
      H3PathEnergyClassProducesCanonicalAnalysis) :
    H3PathVorticityL1LinfProducesH3Control := by

  intro u T hH3 hControl

  rcases hControl with
    ⟨
      g,
      hgIntegrable,
      hgEnvelope
    ⟩

  obtain
    ⟨
      a,
      hClass
    ⟩ :=
    h3Preterminal_energyClass_of_h3PathAdmissible
      hH3

  have ha :
      a ∈ Set.Ioo (0 : ℝ) T :=
    hClass.terminal_start

  have hPathData :
      H3PathProducesCanonicalH3Data :=
    h3PathProducesCanonicalH3Data_of_analysis
      hAnalysis

  have hData :
      CanonicalH3EnergyDataOnTail
        u a T :=
    hPathData
      u T hH3 a hClass

  let b : ℝ :=
    h3BKMKineticTailMidpoint a T

  have hbOld :
      b ∈ Set.Ioo a T := by
    dsimp only [b]

    exact
      h3BKMKineticTailMidpoint_mem_Ioo
        ha.2

  have hb :
      b ∈ Set.Ioo (0 : ℝ) T := by
    dsimp only [b]

    exact
      h3BKMKineticTailMidpoint_mem_Ioo_zero
        ha

  have hClassB :
      PreterminalH3EnergyClass
        u b T :=
    preterminalH3EnergyClass_restrict_left
      hClass
      (le_of_lt hbOld.1)
      hbOld.2

  have hDataB :
      CanonicalH3EnergyDataOnTail
        u b T :=
    canonicalH3EnergyDataOnTail_restrict_left
      hData
      (le_of_lt hbOld.1)

  have hgTail :
      ∀ t : ℝ,
        t ∈ Set.Ioo a T →
          VorticityEnvelope u g t := by

    intro t ht

    exact
      hgEnvelope
        t
        ⟨
          lt_trans ha.1 ht.1,
          ht.2
        ⟩

  have hActual0 :=
    actualVelocityGradientLogBoundFrom_canonicalSelectedBKM_of_energyClass
      hClass
      hData
      hgTail

  let B : ℝ :=
    h3BKMCanonicalSelectedLogGradientConstant
      (Real.sqrt
        (velocityH3Energy0At u b))

  have hB :
      0 ≤ B := by
    dsimp only [B]

    exact
      h3BKMCanonicalSelectedLogGradientConstant_nonneg
        (Real.sqrt_nonneg _)

  have hActual :
      ActualVelocityGradientLogBoundFrom
        u b T g
        (velocityH3EnergyAt u)
        B := by

    dsimp only [b, B]

    exact hActual0

  have hProfile :
      H3EnergyProfileFrom
        u b T
        (velocityH3EnergyAt u) :=
    h3EnergyProfileFrom_canonical
      hDataB

  have hC1 :
      EnergyLocallyC1OnTail
        b T
        (velocityH3EnergyAt u) :=
    hDataB.2.1

  let h : ℝ → ℝ :=
    h3BKMLogarithmicGradientEnvelope
      g
      (velocityH3EnergyAt u)
      B

  have hGradient :
      ∀ t : ℝ,
        t ∈ Set.Ioo b T →
          VelocityGradientEnvelope
            u h t := by

    intro t ht

    dsimp only [h]

    exact
      velocityGradientEnvelope_h3BKMLogarithmicGradientEnvelope
        hActual
        ht

  have hEndpointBound :
      ∀ t : ℝ,
        t ∈ Set.Ioo b T →
          1 + |h t|
            ≤
          (B + 1)
            * (1 + |g t|)
            * (1 + Real.log (velocityH3EnergyAt u t)) := by

    intro t ht

    have hEt :
        1 ≤ velocityH3EnergyAt u t :=
      (hProfile
        t
        ⟨
          le_of_lt ht.1,
          ht.2
        ⟩).1

    dsimp only [h]

    exact
      one_add_abs_h3BKMLogarithmicGradientEnvelope_le
        hB
        hEt

  have hLandau :
      H3LandauTransportAnalyticOnTail
        u b T h :=
    h3LandauTransportAnalyticOnTail_of_gradientEnvelope
      hClassB
      hDataB
      hGradient

  have hEnergyGrowth :
      H3GradientGrowthInequalityFrom
        b T h
        (velocityH3EnergyAt u)
        4422 :=
    h3GradientGrowthInequalityFrom_canonical_of_landauAnalytic_cutoff
      hClassB
      hDataB
      hLandau

  let C : ℝ :=
    4422 * (B + 1)

  have hC :
      0 ≤ C := by
    dsimp only [C]

    have hBOne :
        0 ≤ B + 1 := by
      linarith

    exact
      mul_nonneg
        (by norm_num)
        hBOne

  have hGrowth :
      BKMLogGrowthInequalityFrom
        b T g
        (velocityH3EnergyAt u)
        C := by

    intro t ht

    have hEtOne :
        1 ≤ velocityH3EnergyAt u t :=
      (hProfile
        t
        ⟨
          le_of_lt ht.1,
          ht.2
        ⟩).1

    have hEtNonneg :
        0 ≤ velocityH3EnergyAt u t :=
      le_trans
        (by norm_num)
        hEtOne

    have hEndpointAt :
        1 + |h t|
          ≤
        (B + 1)
          * (1 + |g t|)
          * (1 + Real.log (velocityH3EnergyAt u t)) :=
      hEndpointBound
        t ht

    calc
      deriv (velocityH3EnergyAt u) t
          ≤
        4422
          * (1 + |h t|)
          * velocityH3EnergyAt u t :=
        hEnergyGrowth
          t ht

      _ ≤
        4422
          *
        (
          (B + 1)
            * (1 + |g t|)
            * (1 + Real.log (velocityH3EnergyAt u t))
        )
          * velocityH3EnergyAt u t := by

        exact
          mul_le_mul_of_nonneg_right
            (
              mul_le_mul_of_nonneg_left
                hEndpointAt
                (by norm_num)
            )
            hEtNonneg

      _ =
        C
          * (1 + |g t|)
          * velocityH3EnergyAt u t
          * (1 + Real.log (velocityH3EnergyAt u t)) := by

        dsimp only [C]
        ring

  have hgTailIntegrable :
      MeasureTheory.IntegrableOn
        g
        (Set.Ioo b T) := by

    apply
      hgIntegrable.mono_set

    intro t ht

    exact
      ⟨
        lt_trans hb.1 ht.1,
        ht.2
      ⟩

  have hEOne :
      ∀ t : ℝ,
        t ∈ Set.Ico b T →
          1 ≤ velocityH3EnergyAt u t := by

    intro t ht

    exact
      (hProfile t ht).1

  obtain
    ⟨
      M,
      hM,
      hEM
    ⟩ :=
    logarithmicGronwallClosesEnergy
      b
      T
      g
      (velocityH3EnergyAt u)
      C
      hb.2
      hgTailIntegrable
      hC
      hEOne
      hC1
      hGrowth

  refine
    ⟨
      b,
      M,
      hb,
      hM,
      ?_
    ⟩

  intro t ht

  exact
    velocityH3BoundAt_mono
      (hProfile t ht).2
      (hEM t ht)

/--
Final H³-path BKM continuation criterion at the current analytic frontier.

The growth half uses only `H3PathEnergyClassProducesCanonicalAnalysis`.
After Osgood produces `TerminalTailH3Control`, the continuation half is
discharged unconditionally by `h3PathH3ControlProducesExtension`.
-/
theorem h3PathVorticityL1LinfProducesExtension_of_reducedCanonicalAnalysis
    (hAnalysis :
      H3PathEnergyClassProducesCanonicalAnalysis) :
    H3PathVorticityL1LinfProducesExtension := by

  intro u T hH3 hControl

  have hTail :
      TerminalTailH3Control u T :=
    h3PathVorticityL1LinfProducesH3Control_of_reducedCanonicalAnalysis
      hAnalysis
      u T
      hH3
      hControl

  exact
    h3PathH3ControlProducesExtension
      u T
      hH3
      hTail

end

end Euclidean
end Bridge
end PrimeTensor
