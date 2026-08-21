import PrimeTensor.Fluid.Vorticity.H3.Energy.Closure
import PrimeTensor.Fluid.Vorticity.H3.Energy.Estimate.Landau.Tail

/-!
# Landau specialization of the canonical H³ closure

The older closure route requires two independent nonlinear hypotheses:

* existence of a velocity-gradient envelope;
* a universal abstract commutator estimate.

The explicit Landau transport package is stronger than both at once.  Its
pointwise analytic data already contains the velocity-gradient envelope, and
the order-by-order transport proof supplies the concrete coefficient `4422`.

This file therefore replaces those two abstract obligations by one tail-level
Landau closure proposition.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set

/--
Energy-class closure obligation for the explicit Landau transport package.

This closure obligation now factors into two standard whole-space analytic
theorems, `WholeSpaceC1FDerivL2ToL6` and
`WholeSpaceQuarticDerivativeIntegrationByParts`, plus the genuinely
NS-specific statement that every preterminal H³ energy-class state admits
one tail envelope `h` with the transport integration-by-parts data at
orders zero through three.
-/
def EnergyClassProducesLandauTransportAnalytic : Prop :=
  WholeSpaceC1FDerivL2ToL6
    ∧
  WholeSpaceQuarticDerivativeIntegrationByParts
    ∧
  ∀
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (a T : ℝ),
      PreterminalH3EnergyClass
          u a T
        →
      ∃ h : ℝ → ℝ,
        H3LandauTransportAnalyticOnTail
          u a T h

/--
The canonical H³ data closure together with the explicit Landau transport
closure discharges the existing `EnergyClassProducesH3GradientGrowth`
interface.

No separate gradient-envelope hypothesis is needed: the Landau analytic tail
package itself contains `VelocityGradientEnvelope u h t` at every strict tail
time.
-/
theorem energyClassProducesH3GradientGrowth_of_landauClosure
    (
      hCanonical :
        EnergyClassProducesCanonicalH3Data
    )
    (
      hLandau :
        EnergyClassProducesLandauTransportAnalytic
    ) :
    EnergyClassProducesH3GradientGrowth := by

  intro
    u a T g
    hClass
    hgIntegrable
    hgEnvelope

  have hData :
      CanonicalH3EnergyDataOnTail
        u a T :=
    hCanonical
      u a T hClass

  have hSobolevFDeriv6 :
      WholeSpaceC1FDerivL2ToL6 :=
    hLandau.1

  have hQuarticIBP :
      WholeSpaceQuarticDerivativeIntegrationByParts :=
    hLandau.2.1

  rcases
      hLandau.2.2
        u a T hClass
    with
      ⟨h, hLandauTail⟩

  have hGradient :
      ∀ t : ℝ,
        t ∈ Set.Ioo a T →
          VelocityGradientEnvelope
            u h t := by

    intro t ht

    rcases hLandauTail t ht with
      ⟨
        hIBP0,
        hIBP1,
        hIBP2,
        hIBP3,
        hAnalyticCore3
      ⟩

    simpa [H3OrderThreeInterpolationLandauCoreAnalyticDataAt] using
      hAnalyticCore3

  refine
    ⟨
      velocityH3EnergyAt u,
      h,
      4422,
      ?_,
      h3EnergyProfileFrom_canonical
        hData,
      hData.2.1,
      hGradient,
      ?_
    ⟩

  · norm_num

  · exact
      h3GradientGrowthInequalityFrom_canonical_of_landauAnalytic
        hSobolevFDeriv6
        hQuarticIBP
        hClass
        hData
        hLandauTail

/--
With the pre-existing smoothing bridge, canonical H³ data plus the explicit
Landau transport closure imply the BKM energy-side proposition.

This removes the old `GradientEnvelopeControlsH3Transport` obligation from the
Landau branch entirely.
-/
theorem vorticityEnvelopeProducesH3GradientGrowth_of_landauClosure
    (
      hSmooth :
        H3SeedProducesEnergyClass
    )
    (
      hCanonical :
        EnergyClassProducesCanonicalH3Data
    )
    (
      hLandau :
        EnergyClassProducesLandauTransportAnalytic
    ) :
    VorticityEnvelopeProducesH3GradientGrowth := by

  apply
    vorticityEnvelopeProducesH3GradientGrowth_of_energyClass
      hSmooth

  exact
    energyClassProducesH3GradientGrowth_of_landauClosure
      hCanonical
      hLandau

end Euclidean
end Bridge
end PrimeTensor
