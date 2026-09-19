import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.HighOrder.Old.H3PathAdmissible
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.TopFlux.TailClosure
import PrimeTensor.Fluid.Vorticity.H3.Energy.Closure.Landau.Endpoint
import PrimeTensor.Fluid.Vorticity.Logarithmic.Gronwall

/-!
# Landau/BKM continuation on the preterminal H³ path class

The original public continuation interface starts from

    LoggedPreterminalNavierStokesAdmissible u T
      + PreterminalH3Seed u T.

That pointwise-classical solution class is intentionally weak: it does not say
that the old solution remains an H³ path between the seed time and `T`.
Consequently the older Landau factorization required the separate global
smoothing hypothesis

    H3SeedProducesEnergyClass.

`Selected.HighOrder.Old.H3PathAdmissible` now supplies the correct strong
solution class:

    LoggedPreterminalH3PathAdmissible u T.

For this class, the high-order energy class is already a theorem:

    h3Preterminal_energyClass_of_h3PathAdmissible.

This file rethreads the Landau/BKM argument through that theorem.  No
`H3SeedProducesEnergyClass` hypothesis appears.

The proof is otherwise the existing BKM route:

1. obtain an old high-order energy class from the H³ path;
2. use canonical H³ data plus the explicit Landau transport estimate to get
   the differentiated H³ energy inequality;
3. insert the logarithmic vorticity-to-gradient endpoint estimate;
4. apply the proved scalar logarithmic Grönwall/Osgood theorem;
5. convert the bounded energy profile to `TerminalTailH3Control`;
6. invoke the existing tail-H³ continuation interface.

This gives a continuation criterion at the standard maximal-strong-solution
level without asserting that one isolated H³ slice propagates through an
otherwise unconstrained pointwise-classical branch.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set MeasureTheory

noncomputable section

/--
BKM H³-control criterion on the preterminal H³ path class.

Unlike `VorticityL1LinfProducesH3Control`, no separate seed is needed: every
strict slice of `LoggedPreterminalH3PathAdmissible` is already H³.
-/
def H3PathVorticityL1LinfProducesH3Control : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalH3PathAdmissible u T →
      VorticityL1LinfControl u T →
      TerminalTailH3Control u T

/--
Seed-free continuation criterion for a preterminal H³ strong path.
-/
def H3PathVorticityL1LinfProducesExtension : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalH3PathAdmissible u T →
      VorticityL1LinfControl u T →
      ∃
        v :
          SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

/--
The differentiated energy estimate plus the logarithmic endpoint close the
BKM terminal H³ bound on the H³ path class.

The high-order energy class is obtained internally from
`h3Preterminal_energyClass_of_h3PathAdmissible`; there is no smoothing axiom.
-/
theorem h3PathVorticityL1LinfProducesH3Control_of_energy_and_endpoint
    (hEnergy : EnergyClassProducesH3GradientGrowth)
    (hEndpoint : VorticityControlsGradientLogarithmically) :
    H3PathVorticityL1LinfProducesH3Control := by

  intro u T hH3 hControl

  rcases hControl with
    ⟨g, hgIntegrable, hgEnvelope⟩

  rcases
    h3Preterminal_energyClass_of_h3PathAdmissible
      hH3
  with
    ⟨a, hClass⟩

  rcases
    hEnergy
      u a T g
      hClass
      hgIntegrable
      hgEnvelope
  with
    ⟨
      E,
      h,
      A,
      hA,
      hProfile,
      hC1,
      hGradient,
      hEnergyGrowth
    ⟩

  have ha :
      a ∈ Set.Ioo (0 : ℝ) T :=
    hClass.terminal_start

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

  rcases
    hEndpoint
      u a T g E h
      ha
      hgTail
      hProfile
      hGradient
  with
    ⟨
      B,
      hB,
      hEndpointBound
    ⟩

  let C : ℝ :=
    A * B

  have hC :
      0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg hA hB

  have hGrowth :
      BKMLogGrowthInequalityFrom
        a T g E C := by
    intro t ht

    have hEtOne :
        1 ≤ E t :=
      (hProfile t
        ⟨le_of_lt ht.1, ht.2⟩).1

    have hEtNonneg :
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
      hEndpointBound t ht

    calc
      deriv E t
          ≤
        A * (1 + |h t|) * E t :=
        hEnergyGrowth t ht

      _ ≤
        A
          *
        (
          B
            * (1 + |g t|)
            * (1 + Real.log (E t))
        )
          * E t := by
        exact
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              hEndpointAt
              hA)
            hEtNonneg

      _ =
        C
          * (1 + |g t|)
          * E t
          * (1 + Real.log (E t)) := by
        dsimp only [C]
        ring

  have hgTailIntegrable :
      IntegrableOn
        g
        (Set.Ioo a T) := by
    apply hgIntegrable.mono_set
    intro t ht
    exact
      ⟨
        lt_trans ha.1 ht.1,
        ht.2
      ⟩

  have hEOne :
      ∀ t : ℝ,
        t ∈ Set.Ico a T →
          1 ≤ E t := by
    intro t ht
    exact
      (hProfile t ht).1

  rcases
    logarithmicGronwallClosesEnergy
      a T g E C
      ha.2
      hgTailIntegrable
      hC
      hEOne
      hC1
      hGrowth
  with
    ⟨
      M,
      hM,
      hEM
    ⟩

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

/--
Canonical H³ closure plus the explicit Landau transport package and the
logarithmic endpoint give BKM terminal-tail H³ control for every admissible H³
path.

No `H3SeedProducesEnergyClass` input remains.
-/
theorem h3PathVorticityL1LinfProducesH3Control_of_landauClosure
    (hCanonical : EnergyClassProducesCanonicalH3Data)
    (hEndpoint : VorticityControlsGradientLogarithmically) :
    H3PathVorticityL1LinfProducesH3Control := by

  have hLandau :
      EnergyClassProducesLandauTransportAnalytic :=
    energyClassProducesLandauTransportAnalytic_of_canonical
      hCanonical

  have hEnergy :
      EnergyClassProducesH3GradientGrowth :=
    energyClassProducesH3GradientGrowth_of_landauClosure
      hCanonical
      hLandau

  exact
    h3PathVorticityL1LinfProducesH3Control_of_energy_and_endpoint
      hEnergy
      hEndpoint

/--
The H³-path BKM control criterion composed with any valid terminal-tail restart
theorem gives continuation through `T`.
-/
theorem h3PathVorticityL1LinfProducesExtension_of_H3Factorization
    (hVorticityToH3 : H3PathVorticityL1LinfProducesH3Control)
    (hH3ToExtension : H3ControlProducesExtension) :
    H3PathVorticityL1LinfProducesExtension := by

  intro u T hH3 hControl

  have hTail :
      TerminalTailH3Control u T :=
    hVorticityToH3
      u T
      hH3
      hControl

  exact
    hH3ToExtension
      u T
      hH3.navier_stokes
      hTail

/--
Landau/BKM continuation theorem on the corrected preterminal H³ strong-solution
class.

The former smoothing hypothesis has disappeared entirely from this route.
-/
theorem h3PathVorticityL1LinfProducesExtension_of_landauClosure
    (hCanonical : EnergyClassProducesCanonicalH3Data)
    (hEndpoint : VorticityControlsGradientLogarithmically)
    (hH3ToExtension : H3ControlProducesExtension) :
    H3PathVorticityL1LinfProducesExtension := by

  exact
    h3PathVorticityL1LinfProducesExtension_of_H3Factorization
      (h3PathVorticityL1LinfProducesH3Control_of_landauClosure
        hCanonical
        hEndpoint)
      hH3ToExtension

/--
Concrete local-well-posedness form of the H³-path Landau criterion.
-/
theorem h3PathVorticityL1LinfProducesExtension_of_landauClosure_localWellPosedness
    (hCanonical : EnergyClassProducesCanonicalH3Data)
    (hEndpoint : VorticityControlsGradientLogarithmically)
    (hLocal : CanonicalH3RealLocalWellPosedness) :
    H3PathVorticityL1LinfProducesExtension := by

  exact
    h3PathVorticityL1LinfProducesExtension_of_landauClosure
      hCanonical
      hEndpoint
      (h3ControlProducesExtension_of_uniformLifespan
        (uniformH3RealRestartLifespan_of_canonicalEnergy
          (uniformCanonicalH3RealRestartLifespan_of_localWellPosedness
            hLocal)))

end

end Euclidean
end Bridge
end PrimeTensor
