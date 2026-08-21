import PrimeTensor.Fluid.Vorticity.H3.Energy.Estimate

/-!
# Closing the canonical H³ energy interface

`VorticityH3EnergyEstimate` proves the actual scalar growth inequality for the
canonical H³ energy once its analytic tail data and transport control are
available.

The older BKM-facing interface, `EnergyClassProducesH3GradientGrowth`, asks for
slightly more bookkeeping:

* an actual normalized H³ energy profile;
* local C¹ regularity of that profile;
* a finite velocity-gradient envelope on the tail;
* one nonnegative constant controlling the differentiated energy.

This file isolates the two remaining closure obligations needed to bridge the
canonical energy calculation to that interface:

1. canonical H³ integrability / local-C¹ / analytic-tail data;
2. existence of a finite gradient envelope.

The nonlinear transport estimate remains the separately named
`GradientEnvelopeControlsH3Transport` obligation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory

/--
All non-transport data needed to use the canonical H³ energy on a terminal
tail.

The first conjunct makes the finite-sum canonical energy an actual
`H3EnergyProfileFrom`; the second supplies the scalar local-C¹ hypothesis used
downstream; the third is the exact PDE/IBP analytic package introduced by the
energy recombination module.
-/
def CanonicalH3EnergyDataOnTail
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (a T : ℝ) : Prop :=
  (
    ∀ t : ℝ,
      t ∈ Set.Ico a T →
        VelocityH3IntegrableAt
          u t
  )
    ∧
  EnergyLocallyC1OnTail
      a T
      (velocityH3EnergyAt u)
    ∧
  H3EnergyEstimateAnalyticOnTail
      u a T

/--
The canonical finite-sum energy is a normalized H³ energy profile whenever all
of its squared derivative fields are integrable on the tail.
-/
theorem h3EnergyProfileFrom_canonical
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {a T : ℝ}
    (
      hData :
        CanonicalH3EnergyDataOnTail
          u a T
    ) :
    H3EnergyProfileFrom
      u a T
      (velocityH3EnergyAt u) := by

  intro t ht

  refine
    ⟨
      one_le_velocityH3EnergyAt
        u t,
      ?_
    ⟩

  exact
    velocityH3BoundAt_canonical
      u t
      (hData.1 t ht)

/--
Existence of one finite common envelope for all first spatial derivatives of
the logged velocity at each strict tail time.

For classical H³ functions in three dimensions this is the Sobolev-embedding
side of the argument; it is kept explicit here rather than inferred from the
pointwise `SpatialC5` justification class.
-/
def H3GradientEnvelopeExistsOnTail
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (a T : ℝ) : Prop :=
  ∃ h : ℝ → ℝ,
    ∀ t : ℝ,
      t ∈ Set.Ioo a T →
        VelocityGradientEnvelope
          u h t

/--
Energy-class closure obligation for the canonical H³ data.
-/
def EnergyClassProducesCanonicalH3Data : Prop :=
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
      CanonicalH3EnergyDataOnTail
        u a T

/--
Energy-class closure obligation for the finite velocity-gradient envelope.
-/
def EnergyClassProducesGradientEnvelope : Prop :=
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
      H3GradientEnvelopeExistsOnTail
        u a T

/--
The canonical-data closure, gradient-envelope closure, and nonlinear transport
commutator estimate together discharge the existing
`EnergyClassProducesH3GradientGrowth` interface.

The vorticity envelope arguments of that interface are intentionally unused:
as documented when the interface was introduced, the differentiated H³ energy
estimate itself depends on the velocity-gradient envelope, not yet on the
vorticity envelope.
-/
theorem energyClassProducesH3GradientGrowth_of_canonicalClosure
    (
      hCanonical :
        EnergyClassProducesCanonicalH3Data
    )
    (
      hGradientExists :
        EnergyClassProducesGradientEnvelope
    )
    (
      hTransportControl :
        GradientEnvelopeControlsH3Transport
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

  rcases
      hGradientExists
        u a T hClass
    with
      ⟨h, hGradient⟩

  rcases hTransportControl with
    ⟨
      A,
      hA,
      hTransport
    ⟩

  refine
    ⟨
      velocityH3EnergyAt u,
      h,
      A,
      hA,
      h3EnergyProfileFrom_canonical
        hData,
      hData.2.1,
      hGradient,
      ?_
    ⟩

  apply
    h3GradientGrowthInequalityFrom_canonical
      hClass
      hData.2.2

  intro t ht

  have hGradientAt :
      VelocityGradientEnvelope
        u h t :=
    hGradient t ht

  exact
    ⟨
      hGradientAt,
      hTransport
        u a T h t
        hClass
        ht
        hGradientAt
    ⟩

/--
With the pre-existing smoothing bridge, the three canonical energy obligations
already imply the BKM energy-side proposition.
-/
theorem vorticityEnvelopeProducesH3GradientGrowth_of_canonicalClosure
    (
      hSmooth :
        H3SeedProducesEnergyClass
    )
    (
      hCanonical :
        EnergyClassProducesCanonicalH3Data
    )
    (
      hGradientExists :
        EnergyClassProducesGradientEnvelope
    )
    (
      hTransportControl :
        GradientEnvelopeControlsH3Transport
    ) :
    VorticityEnvelopeProducesH3GradientGrowth := by

  apply
    vorticityEnvelopeProducesH3GradientGrowth_of_energyClass
      hSmooth

  exact
    energyClassProducesH3GradientGrowth_of_canonicalClosure
      hCanonical
      hGradientExists
      hTransportControl

end Euclidean
end Bridge
end PrimeTensor
