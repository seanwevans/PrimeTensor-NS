import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Selected.Old.Pressure
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Selected.Old.Velocity
import PrimeTensor.Fluid.Vorticity.H3.Energy.Regularity

/-!
# Package selected high-order regularity into a late old energy class

The selected restart now supplies the two high-order spatial ingredients used
by `PreterminalH3EnergyClass`:

* spatial `C⁵` for the old velocity, after selected/old physical agreement;
* spatial `C⁴` for the old pressure witness, after pressure-gradient transfer.

This file performs the next local packaging step.

First, the pressure-free curl weak-FTC closure removes the explicit physical
agreement hypothesis from the old-velocity transfer at one strict overlap
time.  Thus a retained canonical H³ tail alone gives the old velocity `C⁵`
shape at every strict overlap point still before the old terminal time.

Second, if one canonical restart radius covers the whole remaining old tail,
we restart at its midpoint and assemble an actual `PreterminalH3EnergyClass`
on `[a,T)`.  The pressure witness is the original witness carried by
`LoggedPreterminalNavierStokesAdmissible`.

This does **not** prove the global `H3SeedProducesEnergyClass` frontier: the
hypothesis here is already a canonical H³ tail whose remaining lifetime fits
inside one restart radius.  The global propagation from one isolated H³ seed
remains a separate step.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldLateEnergyClass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Canonical-tail old velocity transfer -/

/--
At one strict selected/old overlap time, the retained canonical H³ tail alone
supplies the old velocity's `VelocitySpatialC5OnTail` local shape.

The only extra endpoint hypothesis is the unavoidable one saying that the
elapsed time still lies before the old terminal time.
-/
theorem h3Preterminal_oldVelocity_secondPartial_spatialC3_of_canonicalTail
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hq0 : 0 < q)
    (hqR :
      q ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hEnd : t + q < T)
    (j i k : PrimeTensor.Axis Depth.three) :
    SpatialC3
      (spatial3.d i
        (spatial3.d k
          (loggedVelocityComponent
            u (t + q) j))) := by

  have hWeakFTC :
      H3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontierOnRestartRadius
        E u T t hNS ht hE hTail :=
    H3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontier_tailH3_curl
      E hE u T t hNS ht hTail

  have hPhysical :
      H3PreterminalSelectedPhysicalAgreementOnRestartRadius
        (1 : ℝ)
        E
        (one_pos : (0 : ℝ) < 1)
        u T t hNS ht hE hTail :=
    h3PreterminalSelectedPhysicalAgreementOnRestartRadius_of_projectedRHSWeakFTC
      hNS ht hE hTail hWeakFTC

  let qClosed :
      Set.Ioc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
    ⟨q, hq0, hqR⟩

  have hAgreement :
      H3PreterminalSelectedPhysicalAgreementAt
        (one_pos : (0 : ℝ) < 1)
        q
        hNS ht hE hTail := by
    have hAt :=
      hPhysical
        qClosed
        (by simpa only [qClosed] using hEnd)

    simpa only [qClosed] using hAt

  exact
    h3PreterminalSelectedPhysicalAgreementAt_oldVelocity_secondPartial_spatialC3
      hNS
      ht
      hE
      hTail
      hq0
      hqR
      hAgreement
      j i k

/-! ## Late canonical tail -> actual old energy class -/

/--
If the unit-viscosity canonical restart radius launched at `t` reaches at least
the old terminal time `T`, then the original old velocity/pressure pair enters
`PreterminalH3EnergyClass` on the midpoint tail `[(t+T)/2,T)`.

This is the exact local high-order packaging needed before attacking propagation
from a single H³ seed.
-/
theorem h3Preterminal_energyClass_of_canonicalTail_radiusCoversTail
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hCover :
      T - t ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E) :
    ∃ a : ℝ,
      PreterminalH3EnergyClass u a T := by

  let a : ℝ :=
    (t + T) / 2

  have hta :
      t < a := by
    dsimp only [a]
    linarith [ht.2]

  have haT :
      a < T := by
    dsimp only [a]
    linarith [ht.2]

  have ha0 :
      0 < a :=
    lt_trans ht.1 hta

  let pOld :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  have hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        pOld
        T := by
    dsimp only [pOld]
    exact Classical.choose_spec hNS

  refine
    ⟨
      a,
      {
        terminal_start := ⟨ha0, haT⟩
        velocity_spatial_five := ?_
        pressure_witness := ?_
      }
    ⟩

  · intro s hs j i k

    change
      SpatialC3
        (spatial3.d i
          (spatial3.d k
            (loggedVelocityComponent u s j)))

    have hq0 :
        0 < s - t := by
      linarith [hta, hs.1]

    have hqBeforeTerminal :
        s - t < T - t := by
      linarith [hs.2]

    have hqRStrict :
        s - t < h3FinHeatLerayRestartRadius (1 : ℝ) E :=
      lt_of_lt_of_le hqBeforeTerminal hCover

    have hqR :
        s - t ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E :=
      le_of_lt hqRStrict

    have hts :
        t + (s - t) = s := by
      ring

    have hEnd :
        t + (s - t) < T := by
      simpa only [hts] using hs.2

    have hOld :=
      h3Preterminal_oldVelocity_secondPartial_spatialC3_of_canonicalTail
        (q := s - t)
        hNS
        ht
        hE
        hTail
        hq0
        hqR
        hEnd
        j i k

    simpa only [hts] using hOld

  · refine
      ⟨
        pOld,
        hPDE,
        ?_
      ⟩

    intro s hs i

    dsimp only [pOld]

    have hq0 :
        0 < s - t := by
      linarith [hta, hs.1]

    have hqBeforeTerminal :
        s - t < T - t := by
      linarith [hs.2]

    have hqR :
        s - t < h3FinHeatLerayRestartRadius (1 : ℝ) E :=
      lt_of_lt_of_le hqBeforeTerminal hCover

    have hts :
        t + (s - t) = s := by
      ring

    have hEnd :
        t + (s - t) < T := by
      simpa only [hts] using hs.2

    have hOld :=
      h3Preterminal_oldPressure_spatialDerivative_spatialC3_of_canonicalTail
        (q := s - t)
        hNS
        ht
        hE
        hTail
        hq0
        hqR
        hEnd
        i

    simpa only [hts] using hOld

end

end Euclidean
end Bridge
end PrimeTensor
