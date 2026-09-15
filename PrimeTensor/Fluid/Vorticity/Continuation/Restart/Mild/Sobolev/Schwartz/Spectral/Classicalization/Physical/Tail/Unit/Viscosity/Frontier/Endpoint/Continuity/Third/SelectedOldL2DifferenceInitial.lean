import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldL2DifferenceGronwall
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Initial.Decoder

/-!
# Zero initial selected/old L² difference

The Grönwall comparison from `SelectedOldL2DifferenceGronwall` still listed
`D 0 = 0` among its free data.  For the actual canonical restart this is not
analytic input.

The selected path starts from the genuine H³ encoding of the old anchor slice.
Its real physical representative at elapsed zero agrees almost everywhere with
the old logged velocity.  The canonical old zeroth `L²` jet is represented by
the same function.  Hence the concrete three-component selected-minus-old
physical `L²` difference is exactly zero at elapsed zero.

This file removes the initial-value condition from the remaining Grönwall
frontier.  What remains is only:

* a real-time lifting of the concrete difference;
* continuity on the fixed strict interval;
* its `L²` derivative;
* the standard linear Grönwall norm bound.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldL2DifferenceInitial
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3SelectedOldL2DifferenceInitial :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The concrete canonical selected-minus-old physical `L²` difference is zero
at elapsed time zero. -/
theorem h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed_zero
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) :
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
        hν hNS ht hEnd hE hTail
        ⟨0, le_rfl, htau.le⟩
      =
    0 := by
  apply sub_eq_zero.mpr
  apply PiLp.ext
  intro j

  change
    h3FromFourierRealL2
        (h3SpectralVelocityDecodeRealL2
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν
            (h3PreterminalSelectedDecoderAnchorState
              hNS ht hTail)
            (lt_of_lt_of_le zero_lt_one hE)
            (norm_h3PreterminalSelectedDecoderAnchorState_le
              hNS ht hE hTail)
            0)
          j)
      =
    h3PreterminalCanonicalL2JetOnElapsed
      hNS ht hEnd hTail
      (h3JetSlot0 j)
      ⟨0, le_rfl, htau.le⟩

  rw [
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_zero
  ]

  unfold h3PreterminalSelectedDecoderAnchorState
  unfold h3PreterminalCanonicalAnchorSpectralState
  dsimp only

  rw [
    h3FromFourierRealL2_h3SpectralVelocityDecodeRealL2_velocityH3SpectralStateAt_eq
  ]

  unfold h3PreterminalCanonicalL2JetOnElapsed
  simp only [add_zero]

/-- Remaining free Grönwall data after removing the automatic zero initial
condition. -/
def H3PreterminalSelectedOldL2DifferenceDerivativeBoundDataOnElapsed
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  ∃
    (D D' : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (K : ℝ),
      (∀ q : Set.Icc (0 : ℝ) tau,
        D (q : ℝ)
          =
        h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          hν hNS ht hEnd hE hTail q)
      ∧
      ContinuousOn D (Set.Icc (0 : ℝ) tau)
      ∧
      (∀ s ∈ Set.Ico (0 : ℝ) tau,
        HasDerivWithinAt
          D (D' s) (Set.Ici s) s)
      ∧
      (∀ s ∈ Set.Ico (0 : ℝ) tau,
        ‖D' s‖ ≤ K * ‖D s‖)

/-- The zero initial value is automatic, so derivative/bound data supplies the
full Grönwall package. -/
theorem h3PreterminalSelectedOldL2DifferenceGronwallDataOnElapsed_of_derivativeBound
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hData :
      H3PreterminalSelectedOldL2DifferenceDerivativeBoundDataOnElapsed
        hν hNS ht hEnd hE hTail) :
    H3PreterminalSelectedOldL2DifferenceGronwallDataOnElapsed
      hν hNS ht hEnd hE hTail := by
  rcases hData with
    ⟨D, D', K, hConcrete, hCont, hDeriv, hBound⟩

  refine
    ⟨D, D', K, hConcrete, hCont, hDeriv, ?_, hBound⟩

  let q0 : Set.Icc (0 : ℝ) tau :=
    ⟨0, le_rfl, htau.le⟩

  calc
    D 0
        =
      h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
        hν hNS ht hEnd hE hTail q0 := by
          simpa only [q0] using hConcrete q0
    _ = 0 :=
      h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed_zero
        hν hNS ht htau hEnd hE hTail

/-- The reduced derivative/bound frontier already closes pointwise physical
agreement on every positive time of the fixed strict interval. -/
theorem h3PreterminalSelectedPhysicalAgreementAt_of_l2DifferenceDerivativeBound
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius ν E)
    (hData :
      H3PreterminalSelectedOldL2DifferenceDerivativeBoundDataOnElapsed
        hν hNS ht hEnd hE hTail)
    (q : Set.Ioc (0 : ℝ) tau) :
    H3PreterminalSelectedPhysicalAgreementAt
      hν (q : ℝ) hNS ht hE hTail := by
  exact
    h3PreterminalSelectedPhysicalAgreementAt_of_l2DifferenceGronwall
      hν
      hNS
      ht
      htau
      hEnd
      hE
      hTail
      htauR
      (h3PreterminalSelectedOldL2DifferenceGronwallDataOnElapsed_of_derivativeBound
        hν hNS ht htau hEnd hE hTail hData)
      q

end

end Euclidean
end Bridge
end PrimeTensor
