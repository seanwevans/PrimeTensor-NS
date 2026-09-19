import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.HighOrder.Absolute
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedPhysicalUniquenessFrontier

/-!
# Transfer selected spatial C⁵ regularity to the old preterminal velocity

The selected restart has arbitrary positive-time spatial regularity; in
particular its intrinsic velocity slices satisfy the `C⁵` shape used by
`PreterminalH3EnergyClass`.

The selected/old uniqueness layer already uses the proposition

    H3PreterminalSelectedPhysicalAgreementAt

which is pointwise equality of the selected smooth physical velocity with the
old logged preterminal velocity at one positive elapsed time.

At a fixed elapsed time, that equality is equality of the entire spatial
scalar field.  Therefore no derivative-comparison theorem is needed:
rewriting the old spatial slice by the selected slice transfers every spatial
derivative at once.

This file packages exactly that transfer for the second-partial `SpatialC3`
shape constituting `VelocitySpatialC5OnTail`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldVelocityC5Transfer
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/--
At one strict positive selected/old overlap time, pointwise physical agreement
transfers selected spatial `C⁵` regularity to the old logged velocity.
-/
theorem h3PreterminalSelectedPhysicalAgreementAt_oldVelocity_secondPartial_spatialC3
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
    (hAgreement :
      H3PreterminalSelectedPhysicalAgreementAt
        (one_pos : (0 : ℝ) < 1)
        q
        hNS ht hE hTail)
    (j i k : PrimeTensor.Axis Depth.three) :
    SpatialC3
      (spatial3.d i
        (spatial3.d k
          (loggedVelocityComponent
            u (t + q) j))) := by

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState
      hNS ht hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht hE hTail

  let selectedSlice : ScalarField3 :=
    fun y =>
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
        (one_pos : (0 : ℝ) < 1)
        U₀
        hA
        hU₀
        q
        y).component j

  have hSelected :
      SpatialC3
        (spatial3.d i
          (spatial3.d k
            selectedSlice)) := by

    dsimp only [selectedSlice, U₀, hA, hU₀]

    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_secondPartial_spatialC3At
        (one_pos : (0 : ℝ) < 1)
        (h3PreterminalSelectedDecoderAnchorState hNS ht hTail)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalSelectedDecoderAnchorState_le
          hNS ht hE hTail)
        hq0
        hqR
        j i k

  have hSliceEq :
      selectedSlice
        =
      loggedVelocityComponent
        u (t + q) j := by

    funext y

    let jj : Fin 3 :=
      h3ClassicalizationFinOfAxis j

    have hPoint :=
      hAgreement jj y

    dsimp only [selectedSlice, U₀, hA, hU₀]

    dsimp only [jj] at hPoint

    rw [
      h3AxisOfFin3_h3ClassicalizationFinOfAxis j
    ] at hPoint

    simpa only [loggedVelocityComponent] using hPoint

  rw [← hSliceEq]

  exact hSelected

/--
Radius-wide form: if selected/old physical agreement is known at every strict
positive elapsed time, then the old velocity has the exact spatial `C⁵` local
shape at every such overlap time.
-/
theorem h3PreterminalSelectedPhysicalAgreementOnRestartRadius_oldVelocity_spatialFive
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hAgreement :
      ∀ q : ℝ,
        q ∈ Set.Ioc
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius (1 : ℝ) E) →
        H3PreterminalSelectedPhysicalAgreementAt
          (one_pos : (0 : ℝ) < 1)
          q
          hNS ht hE hTail) :
    ∀ q : ℝ,
      q ∈ Set.Ioc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E) →
      ∀ j i k : PrimeTensor.Axis Depth.three,
        SpatialC3
          (spatial3.d i
            (spatial3.d k
              (loggedVelocityComponent
                u (t + q) j))) := by

  intro q hq j i k

  exact
    h3PreterminalSelectedPhysicalAgreementAt_oldVelocity_secondPartial_spatialC3
      hNS
      ht
      hE
      hTail
      hq.1
      hq.2
      (hAgreement q hq)
      j i k

end

end Euclidean
end Bridge
end PrimeTensor
