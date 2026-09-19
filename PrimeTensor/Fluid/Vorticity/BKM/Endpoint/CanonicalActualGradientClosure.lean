import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.KineticEnergyMonotonicity
import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.ActualGradientClosure

/-!
# BKM endpoint: close the canonical actual-gradient route

The harmonic-analysis endpoint, kinetic-energy low-frequency control, and
canonical H³ energy machinery are now all available on an energy-class tail.

The older proposition `VorticityControlsActualGradientLogarithmically` is more
general than the continuation proof needs: it quantifies over arbitrary H³
profiles without carrying the energy-class data that supplies kinetic-energy
monotonicity.  The continuation theorem itself only needs one terminal tail and
one concrete H³ profile.

This file therefore closes the continuation route directly with the canonical
profile.

Starting from the smoothing tail `[a,T)`:

1. restart at the kinetic midpoint `b = (a+T)/2`;
2. restrict the high-order energy class and canonical analytic data to `[b,T)`;
3. use the proved selected BKM endpoint to control the actual velocity gradient;
4. package that estimate as the canonical logarithmic gradient envelope;
5. reconstruct the Landau transport tail package;
6. apply the canonical H³ growth estimate with coefficient `4422`;
7. obtain the exact `BKMLogGrowthInequalityFrom` required by the scalar Osgood
   theorem.

Thus the canonical branch no longer assumes an external logarithmic-gradient
endpoint proposition.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory

noncomputable section

/-! ## Tail restriction helpers -/

/--
A preterminal H³ energy class restricts to any later strict tail start.
-/
theorem preterminalH3EnergyClass_restrict_left
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a b T : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (hab : a ≤ b)
    (hbT : b < T) :
    PreterminalH3EnergyClass u b T := by

  refine
    {
      terminal_start := ?_
      velocity_spatial_five := ?_
      pressure_witness := ?_
    }

  · exact
      ⟨
        lt_of_lt_of_le hClass.terminal_start.1 hab,
        hbT
      ⟩

  · intro t ht j i k

    exact
      hClass.velocity_spatial_five
        t
        ⟨
          le_trans hab ht.1,
          ht.2
        ⟩
        j i k

  · rcases hClass.pressure_witness with
      ⟨p, hPDE, hp4⟩

    refine
      ⟨
        p,
        hPDE,
        ?_
      ⟩

    intro t ht i

    exact
      hp4
        t
        ⟨
          le_trans hab ht.1,
          ht.2
        ⟩
        i

/--
Canonical H³ energy data restrict to any later tail start.
-/
theorem canonicalH3EnergyDataOnTail_restrict_left
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a b T : ℝ}
    (hData : CanonicalH3EnergyDataOnTail u a T)
    (hab : a ≤ b) :
    CanonicalH3EnergyDataOnTail u b T := by

  refine
    ⟨
      ?_,
      ?_,
      ?_
    ⟩

  · intro t ht

    exact
      hData.1
        t
        ⟨
          le_trans hab ht.1,
          ht.2
        ⟩

  · intro c hc

    have hcOld :
        c ∈ Set.Ico a T :=
      ⟨
        le_trans hab hc.1,
        hc.2
      ⟩

    have hOld :=
      hData.2.1 c hcOld

    exact
      hOld.mono
        (by
          intro s hs

          exact
            ⟨
              le_trans hab hs.1,
              hs.2
            ⟩)

  · rcases hData.2.2 with
      ⟨p, hPDE, hAnalytic⟩

    refine
      ⟨
        p,
        hPDE,
        ?_
      ⟩

    intro t ht

    exact
      hAnalytic
        t
        ⟨
          lt_of_le_of_lt hab ht.1,
          ht.2
        ⟩

/-! ## Canonical BKM growth closure -/

/--
The selected actual-gradient endpoint and kinetic-energy monotonicity close the
full BKM logarithmic H³ growth proposition on a midpoint-restarted canonical
tail.

No independent `VorticityControlsActualGradientLogarithmically` hypothesis is
needed.
-/
theorem vorticityEnvelopeProducesBKMH3Growth_of_canonical_selected_endpoint
    (hSmooth : H3SeedProducesEnergyClass)
    (hCanonical : EnergyClassProducesCanonicalH3Data) :
    VorticityEnvelopeProducesBKMH3Growth := by

  intro
    u T g
    hNS
    hSeed
    hgIntegrable
    hgEnvelope

  obtain
    ⟨a, hClass⟩ :=
    hSmooth
      u T
      hNS
      hSeed

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

  refine
    ⟨
      b,
      velocityH3EnergyAt u,
      C,
      hb,
      ?_,
      hProfile,
      hC1,
      ?_
    ⟩

  · dsimp only [C]

    have hBOne :
        0 ≤ B + 1 := by
      linarith

    exact
      mul_nonneg
        (by norm_num)
        hBOne

  · intro t ht

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

/-! ## Downstream consequences -/

/--
The canonical selected endpoint plus the proved scalar logarithmic Grönwall
theorem give uniform terminal-tail H³ control.
-/
theorem vorticityL1LinfProducesH3Control_of_canonical_selected_endpoint
    (hSmooth : H3SeedProducesEnergyClass)
    (hCanonical : EnergyClassProducesCanonicalH3Data) :
    VorticityL1LinfProducesH3Control := by

  apply
    vorticityL1LinfProducesH3Control_of_BKMGrowth_closedScalar

  exact
    vorticityEnvelopeProducesBKMH3Growth_of_canonical_selected_endpoint
      hSmooth
      hCanonical

/--
Adding the existing H³ restart/extension theorem yields the seeded vorticity
continuation criterion without an external logarithmic-gradient endpoint
hypothesis.
-/
theorem seededVorticityL1LinfProducesExtension_of_canonical_selected_endpoint
    (hSmooth : H3SeedProducesEnergyClass)
    (hCanonical : EnergyClassProducesCanonicalH3Data)
    (hH3ToExtension : H3ControlProducesExtension) :
    SeededVorticityL1LinfProducesExtension := by

  apply
    seededVorticityL1LinfProducesExtension_of_BKMGrowth_closedScalar
      (
        vorticityEnvelopeProducesBKMH3Growth_of_canonical_selected_endpoint
          hSmooth
          hCanonical
      )
      hH3ToExtension

end

end Euclidean
end Bridge
end PrimeTensor
