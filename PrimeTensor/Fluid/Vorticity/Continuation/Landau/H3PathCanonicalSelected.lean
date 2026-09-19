import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathClosedRestart
import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.CanonicalActualGradientClosure

/-!
# Close the H³-path BKM endpoint canonically

`H3PathClosedRestart` reduced H³-path Landau continuation to

* `EnergyClassProducesCanonicalH3Data`;
* an external logarithmic vorticity-to-gradient endpoint.

The endpoint tree has already closed that second item in the exact form needed
for a canonical energy-class tail.

`BKM.Endpoint.KineticEnergyMonotonicity` proves zeroth-order kinetic-energy
monotonicity from canonical H³ energy data.  Restarting at the midpoint then
closes the low-frequency term in the selected BKM decomposition and yields an
actual-velocity logarithmic gradient bound for the canonical H³ profile.

This file repeats the already-closed canonical endpoint assembly with only one
change at the entrance:

    H3SeedProducesEnergyClass

is replaced by the theorem

    h3Preterminal_energyClass_of_h3PathAdmissible.

Consequently the H³-path BKM continuation theorem now has exactly one named
analytic input:

    EnergyClassProducesCanonicalH3Data.

No separate smoothing hypothesis, logarithmic endpoint hypothesis,
old-pressure frontier, abstract continuation theorem, or local-well-posedness
hypothesis remains.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory

noncomputable section

/--
Canonical selected BKM harmonic analysis closes terminal-tail H³ control for
every preterminal H³ path.

The high-order old energy class is constructed internally from the H³ path,
while kinetic-energy monotonicity closes the low-frequency part of the
logarithmic gradient estimate.
-/
theorem h3PathVorticityL1LinfProducesH3Control_of_canonical_selected_endpoint
    (hCanonical :
      EnergyClassProducesCanonicalH3Data) :
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

  have hData :
      CanonicalH3EnergyDataOnTail
        u a T :=
    hCanonical
      u a T hClass

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
The H³-path BKM continuation criterion is therefore closed from canonical H³
energy data alone.

This composes:

    H³ path
      -> high-order old energy class
      -> canonical selected BKM endpoint
      -> scalar Osgood
      -> terminal H³ control
      -> pressure-free late restart
      -> continuation.
-/
theorem h3PathVorticityL1LinfProducesExtension_of_canonical_selected_endpoint_closed
    (hCanonical :
      EnergyClassProducesCanonicalH3Data) :
    H3PathVorticityL1LinfProducesExtension := by

  exact
    h3PathVorticityL1LinfProducesExtension_of_H3Factorization
      (h3PathVorticityL1LinfProducesH3Control_of_canonical_selected_endpoint
        hCanonical)
      (h3ControlProducesExtension_of_unitViscosityCanonicalEnergy
        hCanonical)

end

end Euclidean
end Bridge
end PrimeTensor
