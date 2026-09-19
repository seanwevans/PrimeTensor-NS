import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.HighOrder.Absolute
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Joint
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongCurlWeakFTCGlobalClosure
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Evolution.Vorticity

/-!
# Transfer selected spatial C⁴ regularity to the old preterminal pressure

The selected restart now has a canonical pressure with spatial `C⁴`
regularity at every strict positive restart time.

The remaining issue is that `PreterminalH3EnergyClass` carries the *old*
preterminal pressure witness.  Pressure values themselves need not agree, but
their gradients are the invariant object.

The repository already proves the exact overlap identity

    pressureForce_selected = pressureForce_old

on every strict selected/old overlap slab, provided physical tail evolution is
available.  The pressure-free curl weak-FTC closure now supplies that evolution
from any retained canonical H³ tail.

This file composes those facts:

1. curl weak FTC -> radius-wide endpoint continuity;
2. endpoint continuity -> physical tail evolution;
3. physical evolution -> selected/old pressure-force equality;
4. `pressureForceComponent = -∂p`;
5. selected pressure `C⁴` -> old pressure first derivative is `C³`.

No new PDE estimate or uniqueness argument is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldPressureC4Transfer
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Canonical tail -> physical evolution -/

/--
The pressure-free curl weak-FTC closure supplies the physical selected/old
evolution on the whole canonical unit-viscosity restart radius.
-/
theorem h3PreterminalTailPhysicalEvolutionOnRestartRadius_tailH3_curl
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) :
    H3PreterminalTailPhysicalEvolutionOnRestartRadius
      (1 : ℝ)
      E
      (one_pos : (0 : ℝ) < 1)
      u T t hNS ht hE hTail := by

  have hWeakFTC :
      H3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontierOnRestartRadius
        E u T t hNS ht hE hTail :=
    H3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontier_tailH3_curl
      E hE u T t hNS ht hTail

  have hContinuity :
      H3PreterminalTailUnitViscosityEndpointContinuityFrontierOnRestartRadius
        E u T t hNS ht hE hTail := by

    intro q hqPos hEnd

    exact
      h3PreterminalCanonicalL2EndpointContinuousOnElapsed_of_projectedRHSWeakFTC
        (tau := (q : ℝ))
        hNS
        ht
        hqPos
        hEnd
        hE
        hTail
        q.property.2
        hWeakFTC

  exact
    h3PreterminalTailPhysicalEvolutionOnRestartRadius_of_unitViscosity_endpointContinuity
      hNS ht hE hTail hContinuity

/-! ## Pressure-gradient equality on a strict overlap slice -/

/--
On a strict positive overlap slice, the old pressure witness and the selected
canonical pressure have exactly the same spatial gradient.
-/
theorem h3PreterminalTailCanonicalSelectedPressureGradient_eq_old_on_strictOverlap
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hq0 : 0 < q)
    (hqR :
      q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hEnd : t + q < T)
    (x : Point3)
    (i : PrimeTensor.Axis Depth.three) :
    spatial3.d
        i
        ((Classical.choose hNS :
          SpaceTimeScalarField ℝ ℝ ℝ Depth.three) (t + q))
        x
      =
    spatial3.d
        i
        (h3PreterminalTailCanonicalSelectedPressureAbsolute
          hNS ht hE hTail (t + q))
        x := by

  let R : ℝ :=
    h3FinHeatLerayRestartRadius (1 : ℝ) E

  let upper : ℝ :=
    min R (T - t)

  have hqUpper :
      q < upper := by
    dsimp only [upper]
    rw [lt_min_iff]
    exact
      ⟨
        by simpa only [R] using hqR,
        by linarith [hEnd]
      ⟩

  let tau : ℝ :=
    (q + upper) / 2

  have hqTau :
      q < tau := by
    dsimp only [tau]
    linarith [hqUpper]

  have htauUpper :
      tau < upper := by
    dsimp only [tau]
    linarith [hqUpper]

  have htau0 :
      0 < tau := by
    exact lt_trans hq0 hqTau

  have htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E := by
    have hUpperR :
        upper ≤ R := by
      dsimp only [upper]
      exact min_le_left _ _
    exact
      le_trans
        (le_of_lt htauUpper)
        (by simpa only [R] using hUpperR)

  have hEndTau :
      t + tau < T := by
    have hUpperT :
        upper ≤ T - t := by
      dsimp only [upper]
      exact min_le_right _ _
    linarith [htauUpper, hUpperT]

  have hs :
      t + q ∈ Set.Ioo t (t + tau) := by
    constructor <;> linarith [hq0, hqTau]

  have hEvolution :
      H3PreterminalTailPhysicalEvolutionOnRestartRadius
        (1 : ℝ)
        E
        (one_pos : (0 : ℝ) < 1)
        u T t hNS ht hE hTail :=
    h3PreterminalTailPhysicalEvolutionOnRestartRadius_tailH3_curl
      hNS ht hE hTail

  have hForce :=
    h3PreterminalTailCanonicalSelectedPressureForce_eq_old_on_absoluteSlab
      hNS
      ht
      htau0
      hEndTau
      hE
      hTail
      hEvolution
      htauR
      hs
      x
      i

  unfold
    PrimeTensor.Bridge.RealFluid.pressureForceComponent
    at hForce

  linarith

/-! ## Old pressure C4 transfer -/

/--
At every strict selected/old overlap time, the original preterminal pressure
witness has the exact `PressureSpatialC4OnTail` local shape:
each first spatial derivative is spatially `C³`.
-/
theorem h3Preterminal_oldPressure_spatialDerivative_spatialC3_of_canonicalTail
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hq0 : 0 < q)
    (hqR :
      q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hEnd : t + q < T)
    (i : PrimeTensor.Axis Depth.three) :
    SpatialC3
      (spatial3.d
        i
        ((Classical.choose hNS :
          SpaceTimeScalarField ℝ ℝ ℝ Depth.three) (t + q))) := by

  have hsSelected :
      t + q ∈
        Set.Ioo
          t
          (t + h3FinHeatLerayRestartRadius (1 : ℝ) E) := by
    constructor <;> linarith [hq0, hqR]

  have hSelected :
      SpatialC3
        (spatial3.d
          i
          (h3PreterminalTailCanonicalSelectedPressureAbsolute
            hNS ht hE hTail (t + q))) :=
    h3PreterminalTailCanonicalSelectedPressureAbsolute_spatialDerivative_spatialC3
      hNS ht hE hTail hsSelected i

  have hDerivativeEq :
      spatial3.d
          i
          ((Classical.choose hNS :
            SpaceTimeScalarField ℝ ℝ ℝ Depth.three) (t + q))
        =
      spatial3.d
          i
          (h3PreterminalTailCanonicalSelectedPressureAbsolute
            hNS ht hE hTail (t + q)) := by

    funext x

    exact
      h3PreterminalTailCanonicalSelectedPressureGradient_eq_old_on_strictOverlap
        hNS
        ht
        hE
        hTail
        hq0
        hqR
        hEnd
        x
        i

  rw [hDerivativeEq]

  exact hSelected

end

end Euclidean
end Bridge
end PrimeTensor
