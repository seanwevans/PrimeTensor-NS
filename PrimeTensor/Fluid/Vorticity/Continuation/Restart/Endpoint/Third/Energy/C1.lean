import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Energy.Continuity
import PrimeTensor.Fluid.Vorticity.H3.Energy.Closure

/-!
# Ordered-third endpoint continuity: bridge existing local-C¹ energy regularity

`EnergyContinuity` reduced the remaining ordered-third topology to continuity of
the scalar canonical physical H³ energy profile

    q ↦ velocityH3EnergyAt u (t + q)

on each closed elapsed interval `[0, τ]`.

The project already has the stronger and analytically appropriate notion

    EnergyLocallyC1OnTail t T (velocityH3EnergyAt u),

introduced on the BKM energy side precisely so that the canonical H³ energy can
be manipulated honestly on compact terminal subintervals.

This file connects those interfaces without adding a new analytic assumption.

For `0 < τ` and `t + τ < T`, local C¹ regularity supplies

    ContDiffOn ℝ 1 (velocityH3EnergyAt u) [t, t+τ].

Its continuous restriction to `[t,t+τ]`, composed with the continuous elapsed
translation

    q ↦ t + q : [0,τ] → [t,t+τ],

is exactly the scalar continuity target from `EnergyContinuity`.

Thus the third-order overlap topology is discharged by the already-existing
canonical H³ energy local-C¹ obligation.  The retained `CanonicalH3TailDataFrom`
continues to supply all H³ integrability and uniform-energy information; this
file does not infer local C¹ from that bound alone.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityThirdEnergyC1
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Translation from the elapsed interval `[0,τ]` into the corresponding
physical-time interval `[t,t+τ]`. -/
noncomputable def h3ElapsedToPhysicalClosedInterval
    (t tau : ℝ)
    (htau : 0 ≤ tau) :
    Set.Icc (0 : ℝ) tau →
      Set.Icc t (t + tau) :=
  fun q =>
    ⟨
      t + (q : ℝ),
      by
        constructor
        · linarith [q.2.1]
        · linarith [q.2.2]
    ⟩

/-- The elapsed-to-physical closed-interval translation is continuous. -/
theorem continuous_h3ElapsedToPhysicalClosedInterval
    (t tau : ℝ)
    (htau : 0 ≤ tau) :
    Continuous
      (h3ElapsedToPhysicalClosedInterval
        t tau htau) := by
  unfold h3ElapsedToPhysicalClosedInterval

  exact
    (continuous_const.add continuous_subtype_val).subtype_mk
      _

/-- Existing local C¹ regularity of the canonical H³ energy on the physical
tail gives the exact elapsed scalar-energy continuity target used by the
endpoint-overlap proof. -/
theorem h3PreterminalCanonicalPhysicalH3EnergyContinuousOnElapsed_of_energyLocallyC1OnTail
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hC1 :
      EnergyLocallyC1OnTail
        t T
        (velocityH3EnergyAt u)) :
    H3PreterminalCanonicalPhysicalH3EnergyContinuousOnElapsed
      hNS ht hEnd hTail := by
  unfold H3PreterminalCanonicalPhysicalH3EnergyContinuousOnElapsed

  have htauNonneg :
      0 ≤ tau :=
    le_of_lt htau

  have hRight :
      t + tau ∈ Set.Ico t T := by
    constructor
    · linarith
    · exact hEnd

  have hContDiff :
      ContDiffOn
        ℝ 1
        (velocityH3EnergyAt u)
        (Set.Icc t (t + tau)) :=
    hC1 (t + tau) hRight

  have hRestricted :
      Continuous
        ((Set.Icc t (t + tau)).domRestrict
          (velocityH3EnergyAt u)) :=
    hContDiff.continuousOn.domRestrict

  have hShift :
      Continuous
        (h3ElapsedToPhysicalClosedInterval
          t tau htauNonneg) :=
    continuous_h3ElapsedToPhysicalClosedInterval
      t tau htauNonneg

  have hComp :
      Continuous
        (fun q : Set.Icc (0 : ℝ) tau =>
          ((Set.Icc t (t + tau)).domRestrict
            (velocityH3EnergyAt u))
            (h3ElapsedToPhysicalClosedInterval
              t tau htauNonneg q)) :=
    hRestricted.comp hShift

  simpa only [
    h3ElapsedToPhysicalClosedInterval,
    Set.domRestrict_apply
  ] using hComp

/-- The local-C¹ field already contained in `CanonicalH3EnergyDataOnTail`
therefore gives the endpoint scalar-energy continuity target directly. -/
theorem h3PreterminalCanonicalPhysicalH3EnergyContinuousOnElapsed_of_canonicalH3EnergyData
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hData :
      CanonicalH3EnergyDataOnTail
        u t T) :
    H3PreterminalCanonicalPhysicalH3EnergyContinuousOnElapsed
      hNS ht hEnd hTail := by
  exact
    h3PreterminalCanonicalPhysicalH3EnergyContinuousOnElapsed_of_energyLocallyC1OnTail
      hNS ht htau hEnd hTail
      hData.2.1

/-- Radius-wide canonical-H³-energy local-C¹ frontier.  This uses the project's
pre-existing scalar energy regularity notion rather than a new continuity
predicate. -/
def H3PreterminalTailUnitViscosityPhysicalH3EnergyC1FrontierOnRestartRadius
    (E : ℝ)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  EnergyLocallyC1OnTail
    t T
    (velocityH3EnergyAt u)

/-- Global canonical-H³-energy local-C¹ frontier. -/
def H3PreterminalTailUnitViscosityPhysicalH3EnergyC1Frontier : Prop :=
  ∀
    (E : ℝ)
    (hE : 1 ≤ E)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hTail : CanonicalH3TailDataFrom u t T E),
      H3PreterminalTailUnitViscosityPhysicalH3EnergyC1FrontierOnRestartRadius
        E u T t hNS ht hE hTail

/-- Existing local-C¹ energy regularity closes the scalar physical-H³-energy
continuity frontier introduced in `EnergyContinuity`. -/
theorem h3PreterminalTailUnitViscosityPhysicalH3EnergyContinuityFrontier_of_c1
    (hC1 :
      H3PreterminalTailUnitViscosityPhysicalH3EnergyC1Frontier) :
    H3PreterminalTailUnitViscosityPhysicalH3EnergyContinuityFrontier := by
  intro E hE u T t hNS ht hTail
  intro q hqPos hEnd

  exact
    h3PreterminalCanonicalPhysicalH3EnergyContinuousOnElapsed_of_energyLocallyC1OnTail
      hNS ht hqPos hEnd hTail
      (hC1 E hE u T t hNS ht hTail)

/-- Radius-wide canonical energy-data frontier.  This is a direct reuse of the
energy-side package already defined in `H3.Energy.Closure`. -/
def H3PreterminalTailUnitViscosityCanonicalH3EnergyDataFrontierOnRestartRadius
    (E : ℝ)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  CanonicalH3EnergyDataOnTail
    u t T

/-- Global canonical H³ energy-data frontier. -/
def H3PreterminalTailUnitViscosityCanonicalH3EnergyDataFrontier : Prop :=
  ∀
    (E : ℝ)
    (hE : 1 ≤ E)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hTail : CanonicalH3TailDataFrom u t T E),
      H3PreterminalTailUnitViscosityCanonicalH3EnergyDataFrontierOnRestartRadius
        E u T t hNS ht hE hTail

/-- The canonical energy-data package implies the local-C¹ frontier by
projection to its existing second conjunct. -/
theorem h3PreterminalTailUnitViscosityPhysicalH3EnergyC1Frontier_of_canonicalData
    (hData :
      H3PreterminalTailUnitViscosityCanonicalH3EnergyDataFrontier) :
    H3PreterminalTailUnitViscosityPhysicalH3EnergyC1Frontier := by
  intro E hE u T t hNS ht hTail

  exact
    (hData E hE u T t hNS ht hTail).2.1

/-- Old-pressure control plus the existing canonical H³ energy local-C¹
regularity closes the continuation theorem. -/
theorem h3ControlProducesExtension_of_unitViscosityZeroOldPressurePhysicalH3EnergyC1Closed
    (hOld :
      H3PreterminalTailUnitViscosityZeroOldPressureFrontier)
    (hC1 :
      H3PreterminalTailUnitViscosityPhysicalH3EnergyC1Frontier) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_unitViscosityZeroOldPressurePhysicalH3EnergyClosed
      hOld
      (h3PreterminalTailUnitViscosityPhysicalH3EnergyContinuityFrontier_of_c1
        hC1)

/-- Equivalent closure phrased using the already-existing canonical H³ energy
data package from the BKM energy development. -/
theorem h3ControlProducesExtension_of_unitViscosityZeroOldPressureCanonicalH3EnergyDataClosed
    (hOld :
      H3PreterminalTailUnitViscosityZeroOldPressureFrontier)
    (hData :
      H3PreterminalTailUnitViscosityCanonicalH3EnergyDataFrontier) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_unitViscosityZeroOldPressurePhysicalH3EnergyC1Closed
      hOld
      (h3PreterminalTailUnitViscosityPhysicalH3EnergyC1Frontier_of_canonicalData
        hData)

end

end Euclidean
end Bridge
end PrimeTensor
