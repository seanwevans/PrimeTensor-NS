import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.EnergyC1

/-!
# Ordered-third endpoint continuity: restrict canonical H³ energy data to later tails

The canonical H³ energy package is monotone in the terminal-tail start.

If all of the following hold on `[a,T)`:

* H³ integrability at every retained slice;
* local `C¹` regularity of the canonical scalar H³ energy;
* the analytic differentiated-energy package;

then they continue to hold on every later tail `[t,T)` with `a ≤ t < T`.

This is the exact structural fact needed to connect the endpoint restart time to
the pre-existing high-order energy development.  A high-order energy class does
not have to begin at the exact restart time; it is enough that it begins no
later than that restart time.

The file therefore introduces a minimal "energy class before restart" frontier
and proves that, together with the existing
`EnergyClassProducesCanonicalH3Data`, it closes the canonical-energy-data
frontier used by `EnergyC1`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityThirdEnergyTailRestriction
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Local `C¹` regularity of a scalar profile restricts to every later
terminal-tail start. -/
theorem energyLocallyC1OnTail_mono_start
    {a t T : ℝ}
    {F : ℝ → ℝ}
    (hat : a ≤ t)
    (htT : t < T)
    (hC1 : EnergyLocallyC1OnTail a T F) :
    EnergyLocallyC1OnTail t T F := by
  intro b hb

  have hbOld :
      b ∈ Set.Ico a T := by
    exact
      ⟨
        le_trans hat hb.1,
        hb.2
      ⟩

  have hOld :
      ContDiffOn ℝ 1 F (Set.Icc a b) :=
    hC1 b hbOld

  exact
    hOld.mono
      (by
        intro s hs
        exact
          ⟨
            le_trans hat hs.1,
            hs.2
          ⟩)

/-- The differentiated-energy analytic package restricts to every later open
terminal tail. -/
theorem h3EnergyEstimateAnalyticOnTail_mono_start
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a t T : ℝ}
    (hat : a ≤ t)
    (hAnalytic :
      H3EnergyEstimateAnalyticOnTail
        u a T) :
    H3EnergyEstimateAnalyticOnTail
      u t T := by
  rcases hAnalytic with
    ⟨p, hNS, hTail⟩

  refine
    ⟨
      p,
      hNS,
      ?_
    ⟩

  intro s hs

  exact
    hTail s
      ⟨
        lt_of_le_of_lt hat hs.1,
        hs.2
      ⟩

/-- The complete canonical H³ energy-data package is monotone under moving the
tail start forward. -/
theorem canonicalH3EnergyDataOnTail_mono_start
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a t T : ℝ}
    (hat : a ≤ t)
    (htT : t < T)
    (hData :
      CanonicalH3EnergyDataOnTail
        u a T) :
    CanonicalH3EnergyDataOnTail
      u t T := by
  refine
    ⟨
      ?_,
      energyLocallyC1OnTail_mono_start
        hat htT hData.2.1,
      h3EnergyEstimateAnalyticOnTail_mono_start
        hat hData.2.2
    ⟩

  intro s hs

  exact
    hData.1 s
      ⟨
        le_trans hat hs.1,
        hs.2
      ⟩

/-- If an energy class begins no later than `t`, the existing canonical-energy
closure theorem supplies canonical energy data on the restart tail `[t,T)`. -/
theorem canonicalH3EnergyDataOnTail_of_energyClass_before
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a t T : ℝ}
    (hCanonical :
      EnergyClassProducesCanonicalH3Data)
    (hat : a ≤ t)
    (htT : t < T)
    (hClass :
      PreterminalH3EnergyClass
        u a T) :
    CanonicalH3EnergyDataOnTail
      u t T := by
  exact
    canonicalH3EnergyDataOnTail_mono_start
      hat
      htT
      (hCanonical u a T hClass)

/-- Restart-context frontier saying that some existing high-order energy class
starts no later than the selected restart time. -/
def H3PreterminalTailUnitViscosityEnergyClassBeforeRestartFrontier : Prop :=
  ∀
    (E : ℝ)
    (hE : 1 ≤ E)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hTail : CanonicalH3TailDataFrom u t T E),
      ∃ a : ℝ,
        a ≤ t
          ∧
        PreterminalH3EnergyClass
          u a T

/-- The existing canonical-energy closure obligation plus an energy class
starting before the restart time gives the exact canonical energy-data frontier
used by the endpoint proof. -/
theorem h3PreterminalTailUnitViscosityCanonicalH3EnergyDataFrontier_of_energyClassBefore
    (hCanonical :
      EnergyClassProducesCanonicalH3Data)
    (hClassBefore :
      H3PreterminalTailUnitViscosityEnergyClassBeforeRestartFrontier) :
    H3PreterminalTailUnitViscosityCanonicalH3EnergyDataFrontier := by
  intro E hE u T t hNS ht hTail

  rcases
      hClassBefore
        E hE u T t hNS ht hTail
    with
      ⟨a, hat, hClass⟩

  exact
    canonicalH3EnergyDataOnTail_of_energyClass_before
      hCanonical
      hat
      ht.2
      hClass

/-- Consequently the existing canonical-energy closure theorem plus a
high-order energy class already present before each restart time closes the
third-order scalar energy regularity frontier. -/
theorem h3PreterminalTailUnitViscosityPhysicalH3EnergyC1Frontier_of_energyClassBefore
    (hCanonical :
      EnergyClassProducesCanonicalH3Data)
    (hClassBefore :
      H3PreterminalTailUnitViscosityEnergyClassBeforeRestartFrontier) :
    H3PreterminalTailUnitViscosityPhysicalH3EnergyC1Frontier := by
  exact
    h3PreterminalTailUnitViscosityPhysicalH3EnergyC1Frontier_of_canonicalData
      (h3PreterminalTailUnitViscosityCanonicalH3EnergyDataFrontier_of_energyClassBefore
        hCanonical
        hClassBefore)

/-- Current continuation theorem aligned with the project's existing high-order
energy interfaces.

The remaining hypotheses are now:

* the old-pressure mass frontier for zeroth-order time regularity;
* `EnergyClassProducesCanonicalH3Data`, already defined by the H³ energy
  development;
* existence of a high-order energy class whose start lies no later than each
  selected restart time.
-/
theorem h3ControlProducesExtension_of_unitViscosityZeroOldPressureEnergyClassBeforeClosed
    (hOld :
      H3PreterminalTailUnitViscosityZeroOldPressureFrontier)
    (hCanonical :
      EnergyClassProducesCanonicalH3Data)
    (hClassBefore :
      H3PreterminalTailUnitViscosityEnergyClassBeforeRestartFrontier) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_unitViscosityZeroOldPressureCanonicalH3EnergyDataClosed
      hOld
      (h3PreterminalTailUnitViscosityCanonicalH3EnergyDataFrontier_of_energyClassBefore
        hCanonical
        hClassBefore)

end

end Euclidean
end Bridge
end PrimeTensor
