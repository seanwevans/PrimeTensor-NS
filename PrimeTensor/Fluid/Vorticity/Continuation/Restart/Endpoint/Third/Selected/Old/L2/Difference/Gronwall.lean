import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Physical.Uniqueness.Frontier
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.OldJetCompactWeak
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Velocity.Increment.Leray.Fixed
import Mathlib.Analysis.ODE.Gronwall

/-!
# Selected/old physical L² difference and Grönwall closure

The remaining endpoint frontier has been reduced to ordinary physical uniqueness
between the smooth selected restart and the old preterminal Navier--Stokes
branch.

This file introduces the concrete three-component physical `L²` difference
state on a fixed strict elapsed interval `[0,τ]`.

It then proves two representation-free closure steps:

* if the physical `L²` difference vanishes at one positive elapsed time, the
  selected smooth representative equals the old classical velocity pointwise;
* any real-time lifting of this difference satisfying the standard
  Hilbert-valued Grönwall hypotheses and zero initial data vanishes identically.

Thus the next analytic task is exactly the usual one: identify an `L²` time
derivative of the velocity difference and prove

    ‖Δ'(q)‖ ≤ K ‖Δ(q)‖

on a strict preterminal interval.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldL2DifferenceGronwall
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3SelectedOldL2DifferenceGronwall :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Three-component physical real `L²` state obtained by decoding the canonical
selected restart at elapsed time `q`. -/
noncomputable def h3PreterminalSelectedVelocityPhysicalL2HilbertAt
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : ℝ) :
    H3PhysicalRealFinVectorL2Hilbert :=
  WithLp.toLp 2
    (fun j : Fin 3 =>
      h3FromFourierRealL2
        (h3SpectralVelocityDecodeRealL2
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν
            (h3PreterminalSelectedDecoderAnchorState
              hNS ht hTail)
            (lt_of_lt_of_le zero_lt_one hE)
            (norm_h3PreterminalSelectedDecoderAnchorState_le
              hNS ht hE hTail)
            q)
          j))

/-- Concrete selected-minus-old three-component physical `L²` difference on a
fixed strict elapsed interval. -/
noncomputable def h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau) :
    H3PhysicalRealFinVectorL2Hilbert :=
  h3PreterminalSelectedVelocityPhysicalL2HilbertAt
      hν hNS ht hE hTail (q : ℝ)
    -
  h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
      hNS ht hEnd hTail q

/-- Vanishing of the concrete physical `L²` difference at a positive elapsed
time upgrades to pointwise equality of the selected smooth physical
representative and the old classical velocity. -/
theorem h3PreterminalSelectedPhysicalAgreementAt_of_l2Difference_eq_zero
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (hq : 0 < (q : ℝ))
    (hqR :
      (q : ℝ) ≤ h3FinHeatLerayRestartRadius ν E)
    (hZero :
      h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
        hν hNS ht hEnd hE hTail q = 0) :
    H3PreterminalSelectedPhysicalAgreementAt
      hν (q : ℝ) hNS ht hE hTail := by
  intro j x

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState
      hNS ht hTail

  let hEpos : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht hE hTail

  let VSelected : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalSelectedVelocityPhysicalL2HilbertAt
      hν hNS ht hE hTail (q : ℝ)

  let VOld : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
      hNS ht hEnd hTail q

  have hVector :
      VSelected - VOld = 0 := by
    simpa only [
      VSelected,
      VOld,
      h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
    ] using hZero

  have hCoord :
      VSelected j = VOld j := by
    have h :=
      congrArg
        (fun V : H3PhysicalRealFinVectorL2Hilbert => V j)
        hVector
    simpa only [
      PiLp.sub_apply,
      PiLp.zero_apply,
      sub_eq_zero
    ] using h

  have hSelectedDecoder :
      (fun y : Point3 =>
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
          hν U₀ hEpos hU₀ (q : ℝ) y).component
            (h3AxisOfFin3 j))
        =ᵐ[(volume : Measure Point3)]
      (fun y : Point3 =>
        (VSelected j : H3ScalarL2) y) := by
    have hRep :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_velocityRealC1RepresentativeOnPoint3_ae_eq_decodeRealL2
        (s := (q : ℝ))
        hν U₀ hEpos hU₀ j

    simpa only [
      VSelected,
      h3PreterminalSelectedVelocityPhysicalL2HilbertAt,
      PiLp.toLp_apply,
      U₀,
      hEpos,
      hU₀,
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity,
      h3SpectralRealVelocityOfPath_component_h3AxisOfFin3
    ] using hRep

  have hOld :
      (fun y : Point3 =>
        (VOld j : H3ScalarL2) y)
        =ᵐ[(volume : Measure Point3)]
      loggedVelocityComponent
        u
        (t + (q : ℝ))
        (h3AxisOfFin3 j) := by
    simpa only [
      VOld,
      h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed,
      PiLp.toLp_apply
    ] using
      h3PreterminalCanonicalL2JetOnElapsed_slot0_ae_eq_old_pressureFree
        hNS ht hEnd hTail q j

  have hSelectedOld :
      (fun y : Point3 =>
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
          hν U₀ hEpos hU₀ (q : ℝ) y).component
            (h3AxisOfFin3 j))
        =ᵐ[(volume : Measure Point3)]
      loggedVelocityComponent
        u
        (t + (q : ℝ))
        (h3AxisOfFin3 j) := by
    have hMiddle :
        (fun y : Point3 =>
          (VSelected j : H3ScalarL2) y)
          =ᵐ[(volume : Measure Point3)]
        (fun y : Point3 =>
          (VOld j : H3ScalarL2) y) := by
      rw [hCoord]

    exact
      hSelectedDecoder.trans
        (hMiddle.trans hOld)

  have hSelectedC3 :
      SpatialC3
        (fun y : Point3 =>
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
            hν U₀ hEpos hU₀ (q : ℝ) y).component
              (h3AxisOfFin3 j)) :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_spatialC3At
      hν U₀ hEpos hU₀
      hq
      hqR
      (h3AxisOfFin3 j)

  let pOld :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  have hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        pOld
        T :=
    Classical.choose_spec hNS

  have hOldTime :
      t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) T := by
    exact
      h3PreterminalElapsedTime_mem_Ioo
        ht hEnd q

  have hOldC3 :
      SpatialC3
        (loggedVelocityComponent
          u
          (t + (q : ℝ))
          (h3AxisOfFin3 j)) := by
    unfold loggedVelocityComponent
    exact
      hPDE.regularity.velocity_spatial_three
        (t + (q : ℝ))
        hOldTime
        (h3AxisOfFin3 j)

  unfold SpatialC3 at hSelectedC3 hOldC3

  have hFunctions :
      (fun y : Point3 =>
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
          hν U₀ hEpos hU₀ (q : ℝ) y).component
            (h3AxisOfFin3 j))
        =
      loggedVelocityComponent
        u
        (t + (q : ℝ))
        (h3AxisOfFin3 j) :=
    MeasureTheory.Measure.eq_of_ae_eq
      hSelectedOld
      hSelectedC3.continuous
      hOldC3.continuous

  have hAt := congrFun hFunctions x

  simpa only [
    U₀,
    hEpos,
    hU₀,
    h3PreterminalSelectedDecoderAnchorState,
    loggedVelocityComponent
  ] using hAt

/-- Mathlib's continuous Grönwall theorem specialized to the physical
three-component `L²` Hilbert state used by the restart comparison. -/
theorem h3PhysicalRealFinVectorL2Difference_eq_zero_of_gronwall
    {D D' : ℝ → H3PhysicalRealFinVectorL2Hilbert}
    {K a b : ℝ}
    (hD : ContinuousOn D (Set.Icc a b))
    (hD' :
      ∀ s ∈ Set.Ico a b,
        HasDerivWithinAt
          D (D' s) (Set.Ici s) s)
    (hZero : D a = 0)
    (hBound :
      ∀ s ∈ Set.Ico a b,
        ‖D' s‖ ≤ K * ‖D s‖)
    (s : ℝ)
    (hs : s ∈ Set.Icc a b) :
    D s = 0 := by
  exact
    eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
      hD hD' hZero hBound s hs

/-- Grönwall data for the actual selected-minus-old physical `L²` difference
on one strict elapsed interval.

The real-time path `D` is allowed to be any lifting of the concrete subtype
difference on `[0,τ]`.  This keeps the analytic derivative statement in the
ordinary real-time calculus used throughout Mathlib. -/
def H3PreterminalSelectedOldL2DifferenceGronwallDataOnElapsed
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
      D 0 = 0
      ∧
      (∀ s ∈ Set.Ico (0 : ℝ) tau,
        ‖D' s‖ ≤ K * ‖D s‖)

/-- Grönwall data closes pointwise selected/old physical agreement at every
strictly positive elapsed time in the fixed interval. -/
theorem h3PreterminalSelectedPhysicalAgreementAt_of_l2DifferenceGronwall
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
    (hGronwall :
      H3PreterminalSelectedOldL2DifferenceGronwallDataOnElapsed
        hν hNS ht hEnd hE hTail)
    (q : Set.Ioc (0 : ℝ) tau) :
    H3PreterminalSelectedPhysicalAgreementAt
      hν (q : ℝ) hNS ht hE hTail := by
  rcases hGronwall with
    ⟨D, D', K, hDConcrete, hDCont, hDDeriv, hDZero, hDBound⟩

  let qClosed : Set.Icc (0 : ℝ) tau :=
    ⟨(q : ℝ), q.property.1.le, q.property.2⟩

  have hZeroAt :
      D (q : ℝ) = 0 :=
    h3PhysicalRealFinVectorL2Difference_eq_zero_of_gronwall
      hDCont
      hDDeriv
      hDZero
      hDBound
      (q : ℝ)
      ⟨q.property.1.le, q.property.2⟩

  have hConcreteZero :
      h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          hν hNS ht hEnd hE hTail qClosed
        =
      0 := by
    rw [← hDConcrete qClosed]
    exact hZeroAt

  exact
    h3PreterminalSelectedPhysicalAgreementAt_of_l2Difference_eq_zero
      hν
      hNS
      ht
      hEnd
      hE
      hTail
      qClosed
      q.property.1
      (le_trans q.property.2 htauR)
      hConcreteZero

end

end Euclidean
end Bridge
end PrimeTensor
