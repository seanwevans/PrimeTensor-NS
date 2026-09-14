import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Vorticity

/-!
# Unit-viscosity endpoint-continuity frontier split

The vorticity closure reduced radius-wide physical-tail evolution to the
reduced endpoint physical `L²` continuity predicate.  That predicate still
bundles two analytically different time-topology statements:

* strong `L²` continuity of the zeroth-order velocity coordinates; and
* strong `L²` continuity of the ordered third-order spatial coordinates.

This file separates those two obligations without strengthening either one.
It provides local elapsed-interval predicates, radius-wide frontiers, and
global unit-viscosity frontiers, then recombines them into the already-proved
endpoint-continuity continuation theorem.

The purpose is to let the two time-regularity mechanisms be attacked
independently in subsequent increments while keeping the continuation target
unchanged.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology BigOperators

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityEndpointContinuitySplit
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Strong continuity of the physical zeroth-order `L²` velocity coordinates
on one closed elapsed overlap interval. -/
def H3PreterminalCanonicalL2ZeroContinuousOnElapsed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau E : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  ∀ j : Fin 3,
    Continuous
      (h3PreterminalCanonicalL2JetOnElapsed
        hNS ht hEnd hTail (h3JetSlot0 j))

/-- Strong continuity of the physical ordered third-order `L²` spatial
coordinates on one closed elapsed overlap interval. -/
def H3PreterminalCanonicalL2ThirdContinuousOnElapsed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau E : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  ∀ j i k l : Fin 3,
    Continuous
      (h3PreterminalCanonicalL2JetOnElapsed
        hNS ht hEnd hTail (h3JetSlot3 j i k l))

/-- Zeroth- and third-order continuity together are exactly the existing
reduced endpoint continuity requirement. -/
theorem h3PreterminalCanonicalL2EndpointContinuousOnElapsed_of_zero_third
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau E : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hZero :
      H3PreterminalCanonicalL2ZeroContinuousOnElapsed
        hNS ht hEnd hTail)
    (hThird :
      H3PreterminalCanonicalL2ThirdContinuousOnElapsed
        hNS ht hEnd hTail) :
    H3PreterminalCanonicalL2EndpointContinuousOnElapsed
      hNS ht hEnd hTail := by
  intro j
  constructor
  · exact hZero j
  · intro i k l
    exact hThird j i k l

/-- The zeroth-order half can be projected from the existing endpoint
continuity predicate. -/
theorem h3PreterminalCanonicalL2ZeroContinuousOnElapsed_of_endpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau E : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail) :
    H3PreterminalCanonicalL2ZeroContinuousOnElapsed
      hNS ht hEnd hTail := by
  intro j
  exact (hEndpoint j).1

/-- The ordered-third-order half can be projected from the existing endpoint
continuity predicate. -/
theorem h3PreterminalCanonicalL2ThirdContinuousOnElapsed_of_endpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau E : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail) :
    H3PreterminalCanonicalL2ThirdContinuousOnElapsed
      hNS ht hEnd hTail := by
  intro j i k l
  exact (hEndpoint j).2 i k l

/-- Radius-wide unit-viscosity zeroth-order physical `L²` continuity frontier. -/
def H3PreterminalTailUnitViscosityZeroContinuityFrontierOnRestartRadius
    (E : ℝ)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  ∀ q : Set.Icc
      (0 : ℝ)
      (h3FinHeatLerayRestartRadius (1 : ℝ) E),
    ∀ hqPos : 0 < (q : ℝ),
      ∀ hEnd : t + (q : ℝ) < T,
        H3PreterminalCanonicalL2ZeroContinuousOnElapsed
          hNS ht hEnd hTail

/-- Radius-wide unit-viscosity ordered-third-order physical `L²` continuity
frontier. -/
def H3PreterminalTailUnitViscosityThirdContinuityFrontierOnRestartRadius
    (E : ℝ)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  ∀ q : Set.Icc
      (0 : ℝ)
      (h3FinHeatLerayRestartRadius (1 : ℝ) E),
    ∀ hqPos : 0 < (q : ℝ),
      ∀ hEnd : t + (q : ℝ) < T,
        H3PreterminalCanonicalL2ThirdContinuousOnElapsed
          hNS ht hEnd hTail

/-- The two radius-wide continuity halves reconstruct the existing endpoint
continuity frontier on the restart radius. -/
theorem h3PreterminalTailUnitViscosityEndpointContinuityFrontierOnRestartRadius_of_zero_third
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hZero :
      H3PreterminalTailUnitViscosityZeroContinuityFrontierOnRestartRadius
        E u T t hNS ht hE hTail)
    (hThird :
      H3PreterminalTailUnitViscosityThirdContinuityFrontierOnRestartRadius
        E u T t hNS ht hE hTail) :
    H3PreterminalTailUnitViscosityEndpointContinuityFrontierOnRestartRadius
      E u T t hNS ht hE hTail := by
  intro q hqPos hEnd
  exact
    h3PreterminalCanonicalL2EndpointContinuousOnElapsed_of_zero_third
      hNS ht hEnd hTail
      (hZero q hqPos hEnd)
      (hThird q hqPos hEnd)

/-- Global zeroth-order endpoint-continuity frontier for every retained
canonical H³ tail. -/
def H3PreterminalTailUnitViscosityZeroContinuityFrontier : Prop :=
  ∀
    (E : ℝ)
    (hE : 1 ≤ E)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hTail : CanonicalH3TailDataFrom u t T E),
      H3PreterminalTailUnitViscosityZeroContinuityFrontierOnRestartRadius
        E u T t hNS ht hE hTail

/-- Global ordered-third-order endpoint-continuity frontier for every retained
canonical H³ tail. -/
def H3PreterminalTailUnitViscosityThirdContinuityFrontier : Prop :=
  ∀
    (E : ℝ)
    (hE : 1 ≤ E)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hTail : CanonicalH3TailDataFrom u t T E),
      H3PreterminalTailUnitViscosityThirdContinuityFrontierOnRestartRadius
        E u T t hNS ht hE hTail

/-- The two global time-topology frontiers reconstruct the single global
endpoint-continuity frontier used by the vorticity continuation bridge. -/
theorem h3PreterminalTailUnitViscosityEndpointContinuityFrontier_of_zero_third
    (hZero : H3PreterminalTailUnitViscosityZeroContinuityFrontier)
    (hThird : H3PreterminalTailUnitViscosityThirdContinuityFrontier) :
    H3PreterminalTailUnitViscosityEndpointContinuityFrontier := by
  intro E hE u T t hNS ht hTail
  exact
    h3PreterminalTailUnitViscosityEndpointContinuityFrontierOnRestartRadius_of_zero_third
      hNS ht hE hTail
      (hZero E hE u T t hNS ht hTail)
      (hThird E hE u T t hNS ht hTail)

/-- Split-frontier form of the complete real restart theorem. -/
theorem h3ControlProducesRealRestart_of_unitViscosityZeroThirdContinuityFrontiers
    (hZero : H3PreterminalTailUnitViscosityZeroContinuityFrontier)
    (hThird : H3PreterminalTailUnitViscosityThirdContinuityFrontier)
    (hLocalPDE : H3PreterminalTailUnitViscosityLocalPDEFrontier) :
    H3ControlProducesRealRestart := by
  exact
    h3ControlProducesRealRestart_of_unitViscosityEndpointContinuityFrontier
      (h3PreterminalTailUnitViscosityEndpointContinuityFrontier_of_zero_third
        hZero hThird)
      hLocalPDE

/-- Split-frontier form of the original H³ continuation target. -/
theorem h3ControlProducesExtension_of_unitViscosityZeroThirdContinuityFrontiers
    (hZero : H3PreterminalTailUnitViscosityZeroContinuityFrontier)
    (hThird : H3PreterminalTailUnitViscosityThirdContinuityFrontier)
    (hLocalPDE : H3PreterminalTailUnitViscosityLocalPDEFrontier) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_unitViscosityEndpointContinuityFrontier
      (h3PreterminalTailUnitViscosityEndpointContinuityFrontier_of_zero_third
        hZero hThird)
      hLocalPDE

end

end Euclidean
end Bridge
end PrimeTensor
