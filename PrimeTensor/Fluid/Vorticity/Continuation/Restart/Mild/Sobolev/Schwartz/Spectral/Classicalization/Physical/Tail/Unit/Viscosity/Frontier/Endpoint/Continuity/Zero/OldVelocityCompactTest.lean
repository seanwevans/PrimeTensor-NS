import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.Snapshot
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.RHSBound
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.Curl.Vorticity.Envelope

/-!
# Zeroth endpoint continuity: endpoint-independent old velocity compact-test data

The pressure branch arose because the old weak-FTC argument needed time
integrability of the temporal derivative.  There is another route.

For every old retained H³ snapshot, the canonical real C¹ representative is
already known to agree pointwise with the logged preterminal velocity, with no
endpoint-continuity hypothesis.  The canonical spectral state also has the
uniform bound `‖U(q)‖ ≤ 2E`.  Hence the existing H³ point-evaluation estimate
gives a uniform pointwise envelope for the old velocity itself.

Separately, `PreterminalNavierStokes3` already gives C¹ time regularity at each
fixed spatial point.  Restricting that scalar path to the closed elapsed
interval `[0,τ]` therefore gives ordinary pointwise-in-space time continuity.

These two facts are the exact dominated-convergence inputs needed to prove
continuity of old velocity pairings against fixed compact smooth tests, without
using pressure or endpoint continuity.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3ZeroOldVelocityCompactTest
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Endpoint-independent uniform pointwise envelope for one old logged velocity
component on a closed elapsed interval. -/
theorem norm_loggedVelocityComponent_le_oldCanonicalSnapshotEnvelope
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3)
    (x : Point3) :
    ‖loggedVelocityComponent
        u
        (t + (q : ℝ))
        (h3AxisOfFin3 i)
        x‖
      ≤
    h3RawFourierL1DeweightingCoefficient * (2 * E) := by
  let U : H3SpectralVelocityState :=
    h3PreterminalTailCanonicalSpectralStateOnElapsed
      hNS ht hEnd hTail q

  have hOld :
      h3SpectralVelocityRealC1RepresentativeOnPoint3 U i
        =
      loggedVelocityComponent
        u
        (t + (q : ℝ))
        (h3AxisOfFin3 i) := by
    dsimp only [U]
    exact
      h3PreterminalTailCanonicalSpectralStateOnElapsed_component_eq_old
        hNS ht hEnd hTail q i

  have hRep :
      ‖h3SpectralScalarRealC1RepresentativeOnPoint3
          (U i) x‖
        ≤
      h3RawFourierL1DeweightingCoefficient * ‖U i‖ :=
    norm_h3SpectralScalarRealC1RepresentativeOnPoint3_apply_le
      (U i) x

  have hCoord :
      ‖U i‖ ≤ 2 * E := by
    exact
      (h3SpectralFinVector_coordinate_norm_le U i).trans
        (by
          dsimp only [U]
          exact
            norm_h3PreterminalTailCanonicalSpectralStateOnElapsed_le_twoE
              hNS ht hEnd hE hTail q)

  have hx :=
    congrFun hOld x

  rw [← hx]

  exact
    hRep.trans
      (mul_le_mul_of_nonneg_left
        hCoord
        h3RawFourierL1DeweightingCoefficient_nonneg)

/-- At each fixed physical point, one old logged velocity component is
continuous in elapsed time on the full closed interval. -/
theorem continuous_loggedVelocityComponent_onElapsed_at_point
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (i : Fin 3)
    (x : Point3) :
    Continuous
      (fun q : Set.Icc (0 : ℝ) tau =>
        loggedVelocityComponent
          u
          (t + (q : ℝ))
          (h3AxisOfFin3 i)
          x) := by
  let p :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        p T :=
    Classical.choose_spec hNS

  have hTime :
      ContinuousOn
        (fun s : ℝ =>
          loggedVelocityComponent
            u s (h3AxisOfFin3 i) x)
        (Set.Ioo (0 : ℝ) T) := by
    unfold loggedVelocityComponent

    exact
      (hPDE.regularity.velocity_temporal_one
        x
        (h3AxisOfFin3 i)).continuousOn

  have hShift :
      Continuous
        (fun q : Set.Icc (0 : ℝ) tau =>
          t + (q : ℝ)) :=
    continuous_const.add continuous_subtype_val

  have hMaps :
      MapsTo
        (fun q : Set.Icc (0 : ℝ) tau =>
          t + (q : ℝ))
        Set.univ
        (Set.Ioo (0 : ℝ) T) := by
    intro q hq
    exact
      h3PreterminalElapsedTime_mem_Ioo
        ht hEnd q

  rw [continuous_iff_continuousAt]
  intro q

  have hAbs :
      t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) T :=
    h3PreterminalElapsedTime_mem_Ioo
      ht hEnd q

  have hTimeAt :
      ContinuousAt
        (fun s : ℝ =>
          loggedVelocityComponent
            u s (h3AxisOfFin3 i) x)
        (t + (q : ℝ)) :=
    hTime.continuousAt
      (isOpen_Ioo.mem_nhds hAbs)

  have hShiftAmbient :
      ContinuousAt
        (fun r : ℝ => t + r)
        (q : ℝ) :=
    continuousAt_const.add continuousAt_id

  have hAmbient :
      ContinuousAt
        (fun r : ℝ =>
          loggedVelocityComponent
            u
            (t + r)
            (h3AxisOfFin3 i)
            x)
        (q : ℝ) := by
    change
      ContinuousAt
        ((fun s : ℝ =>
            loggedVelocityComponent
              u s (h3AxisOfFin3 i) x) ∘
          (fun r : ℝ => t + r))
        (q : ℝ)

    exact
      hTimeAt.comp
        hShiftAmbient

  change
    ContinuousAt
      ((fun r : ℝ =>
          loggedVelocityComponent
            u
            (t + r)
            (h3AxisOfFin3 i)
            x) ∘
        (fun r : Set.Icc (0 : ℝ) tau =>
          (r : ℝ)))
      q

  exact
    hAmbient.comp
      continuous_subtype_val.continuousAt

end

end Euclidean
end Bridge
end PrimeTensor
