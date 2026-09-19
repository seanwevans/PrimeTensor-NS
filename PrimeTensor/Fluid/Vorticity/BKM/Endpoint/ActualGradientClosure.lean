import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.LogarithmicGradientInterface
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.TopFlux.TailClosure

/-!
# BKM endpoint: closing the corrected actual-gradient interface

The corrected endpoint estimate controls the actual first derivatives rather
than an arbitrary scalar envelope.  This file reconnects that statement to the
existing H³/Landau continuation chain.

Starting from

* a seeded preterminal Navier--Stokes solution;
* the existing H³ energy-class smoothing bridge;
* canonical H³ tail data;
* the corrected actual-gradient logarithmic endpoint estimate,

we proceed as follows.

1. Use the endpoint estimate to construct the canonical logarithmic scalar
   gradient envelope.
2. Reconstruct the full Landau transport tail package from that envelope using
   the already-proved continuation-layer top-flux closure.
3. Apply the canonical Landau H³ growth estimate with coefficient `4422`.
4. Insert the logarithmic envelope bound to obtain the exact
   `BKMLogGrowthInequalityFrom` required by the scalar Osgood theorem.

Thus the false quantification over every possible gradient envelope is no
longer needed on this route.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory

/--
Canonical H³ closure plus the corrected actual-gradient endpoint estimate imply
the BKM logarithmic H³ growth frontier.
-/
theorem vorticityEnvelopeProducesBKMH3Growth_of_canonical_and_actual_endpoint
    (
      hSmooth :
        H3SeedProducesEnergyClass
    )
    (
      hCanonical :
        EnergyClassProducesCanonicalH3Data
    )
    (
      hEndpoint :
        VorticityControlsActualGradientLogarithmically
    ) :
    VorticityEnvelopeProducesBKMH3Growth := by

  intro
    u T g
    hNS
    hSeed
    hgIntegrable
    hgEnvelope

  obtain
    ⟨
      a,
      hClass
    ⟩ :=
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
      u a T
      hClass

  let E : ℝ → ℝ :=
    velocityH3EnergyAt u

  have hProfile :
      H3EnergyProfileFrom
        u a T E := by
    dsimp only [E]
    exact
      h3EnergyProfileFrom_canonical
        hData

  have hC1 :
      EnergyLocallyC1OnTail
        a T E := by
    dsimp only [E]
    exact
      hData.2.1

  have hgTail :
      ∀ t : ℝ,
        t ∈ Set.Ioo a T →
          VorticityEnvelope
            u g t := by

    intro t ht

    apply
      hgEnvelope
        t

    exact
      ⟨
        lt_trans ha.1 ht.1,
        ht.2
      ⟩

  obtain
    ⟨
      h,
      B,
      hB,
      hGradient,
      hEndpointBound
    ⟩ :=
    vorticityControlsActualGradientLogarithmically_produces_envelope
      hEndpoint
      u a T g E
      hNS
      ha
      hgTail
      hProfile

  have hLandau :
      H3LandauTransportAnalyticOnTail
        u a T h :=
    h3LandauTransportAnalyticOnTail_of_gradientEnvelope
      hClass
      hData
      hGradient

  have hEnergyGrowth :
      H3GradientGrowthInequalityFrom
        a T h E 4422 := by
    dsimp only [E]
    exact
      h3GradientGrowthInequalityFrom_canonical_of_landauAnalytic_cutoff
        hClass
        hData
        hLandau

  let C : ℝ :=
    4422 * B

  refine
    ⟨
      a,
      E,
      C,
      ha,
      ?_,
      hProfile,
      hC1,
      ?_
    ⟩

  · dsimp only [C]

    exact
      mul_nonneg
        (by norm_num)
        hB

  · intro t ht

    have hEtOne :
        1 ≤ E t :=
      (hProfile
        t
        ⟨
          le_of_lt ht.1,
          ht.2
        ⟩).1

    have hEtNonnegative :
        0 ≤ E t :=
      le_trans
        (by norm_num)
        hEtOne

    have hEndpointAt :
        1 + |h t|
          ≤
        B
          * (1 + |g t|)
          * (1 + Real.log (E t)) :=
      hEndpointBound
        t ht

    calc
      deriv E t
          ≤
        4422
          * (1 + |h t|)
          * E t :=
        hEnergyGrowth
          t ht

      _ ≤
        4422
          *
        (
          B
            * (1 + |g t|)
            * (1 + Real.log (E t))
        )
          * E t := by

        exact
          mul_le_mul_of_nonneg_right
            (
              mul_le_mul_of_nonneg_left
                hEndpointAt
                (by norm_num)
            )
            hEtNonnegative

      _ =
        C
          * (1 + |g t|)
          * E t
          * (1 + Real.log (E t)) := by

        dsimp only [C]
        ring

/--
After the scalar logarithmic Grönwall theorem, the corrected endpoint route
produces uniform terminal-tail H³ control.
-/
theorem vorticityL1LinfProducesH3Control_of_canonical_and_actual_endpoint
    (
      hSmooth :
        H3SeedProducesEnergyClass
    )
    (
      hCanonical :
        EnergyClassProducesCanonicalH3Data
    )
    (
      hEndpoint :
        VorticityControlsActualGradientLogarithmically
    ) :
    VorticityL1LinfProducesH3Control := by

  apply
    vorticityL1LinfProducesH3Control_of_BKMGrowth_closedScalar

  exact
    vorticityEnvelopeProducesBKMH3Growth_of_canonical_and_actual_endpoint
      hSmooth
      hCanonical
      hEndpoint

/--
Adding the standard H³ restart/extension theorem gives the honest seeded
vorticity continuation criterion through the corrected endpoint route.
-/
theorem seededVorticityL1LinfProducesExtension_of_canonical_and_actual_endpoint
    (
      hSmooth :
        H3SeedProducesEnergyClass
    )
    (
      hCanonical :
        EnergyClassProducesCanonicalH3Data
    )
    (
      hEndpoint :
        VorticityControlsActualGradientLogarithmically
    )
    (
      hH3ToExtension :
        H3ControlProducesExtension
    ) :
    SeededVorticityL1LinfProducesExtension := by

  apply
    seededVorticityL1LinfProducesExtension_of_BKMGrowth_closedScalar
      (
        vorticityEnvelopeProducesBKMH3Growth_of_canonical_and_actual_endpoint
          hSmooth
          hCanonical
          hEndpoint
      )
      hH3ToExtension

end Euclidean
end Bridge
end PrimeTensor
