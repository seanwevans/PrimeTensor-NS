import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongSelectedWeakPairingDerivative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongSelectedWeakVelocityPairingContinuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongSelectedWeakProjectedRHSPairingContinuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongSelectedWeakPairingBridge
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Selected weak projected-RHS FTC on elapsed time

All selected branch ingredients are now available:

* the ambient compact-test velocity pairing is differentiable at every strict
  elapsed time, with derivative equal to the physical projected-RHS pairing;
* the selected physical velocity pairing is continuous on the complete closed
  elapsed interval;
* the projected-RHS scalar pairing is interval integrable on every initial
  subinterval `[0,q]`.

This file closes the exact branch-local frontier
`H3PreterminalSelectedUnitWeakProjectedRHSFTCOnElapsed`.

No limiting argument is needed.  For each `q ∈ [0,tau]`, scalar FTC applies
directly on `[0,q]`.  The endpoint values of the ambient compact-test pairing
are then identified with the selected physical Hilbert pairings, and their
difference is exactly the pairing with the selected velocity increment.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongSelectedWeakFTC
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The ambient compact-test pairing introduced for the selected derivative
argument is exactly the physical Hilbert pairing with the selected velocity. -/
theorem h3PreterminalSelectedUnitWeakVelocityPairingReal_eq_inner_selectedVelocity
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t r : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector) :
    h3PreterminalSelectedUnitWeakVelocityPairingReal
        hNS ht hE hTail φ r
      =
    inner ℝ
      (h3WeakTestVectorPhysicalL2Hilbert φ)
      (h3PreterminalSelectedVelocityPhysicalL2HilbertAt
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail r) := by
  have h :=
    inner_h3WeakTestVectorPhysicalL2Hilbert_selectedVelocity_eq_classical
      (q := r)
      hNS ht hE hTail φ

  unfold h3PreterminalSelectedUnitWeakVelocityPairingReal
  unfold h3PreterminalSelectedUnitWeakVelocityCoordinatePairingReal
  dsimp only

  symm

  simpa only [
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity,
    h3PreterminalTailCanonicalSelectedRestart,
    h3SpectralRealVelocityOfPath_component_h3AxisOfFin3,
    h3SpectralVelocityRealC1RepresentativeOnPoint3,
    h3PreterminalSelectedDecoderAnchorState,
    h3PreterminalTailCanonicalAnchorSpectralState
  ] using h

/-- The ambient selected weak velocity pairing is continuous on the complete
closed elapsed interval. -/
theorem continuousOn_h3PreterminalSelectedUnitWeakVelocityPairingReal
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (φ : H3WeakTestVector) :
    ContinuousOn
      (h3PreterminalSelectedUnitWeakVelocityPairingReal
        hNS ht hE hTail φ)
      (Set.Icc (0 : ℝ) tau) := by
  rw [continuousOn_iff_continuous_domRestrict]

  have hEq :
      (Set.Icc (0 : ℝ) tau).domRestrict
          (h3PreterminalSelectedUnitWeakVelocityPairingReal
            hNS ht hE hTail φ)
        =
      (fun q : Set.Icc (0 : ℝ) tau =>
        inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert φ)
          (h3PreterminalSelectedVelocityPhysicalL2HilbertAt
            (one_pos : (0 : ℝ) < 1)
            hNS ht hE hTail (q : ℝ))) := by
    funext q
    exact
      h3PreterminalSelectedUnitWeakVelocityPairingReal_eq_inner_selectedVelocity
        hNS ht hE hTail φ

  rw [hEq]

  exact
    continuous_inner_h3WeakTestVectorPhysicalL2Hilbert_selectedVelocityOnElapsed
      hNS ht htau hE hTail htauR φ

/-- The selected branch satisfies the exact weak projected-RHS FTC frontier on
every initial elapsed interval. -/
theorem h3PreterminalSelectedUnitWeakProjectedRHSFTCOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E) :
    H3PreterminalSelectedUnitWeakProjectedRHSFTCOnElapsed
      hNS ht htau hE hTail htauR := by
  intro φ hφ
  intro q

  let P : ℝ → ℝ :=
    h3PreterminalSelectedUnitWeakVelocityPairingReal
      hNS ht hE hTail φ

  let G : ℝ → ℝ :=
    fun r : ℝ =>
      inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
          hNS ht hE hTail htauR r)

  have hPContinuousTau :
      ContinuousOn P (Set.Icc (0 : ℝ) tau) := by
    dsimp only [P]
    exact
      continuousOn_h3PreterminalSelectedUnitWeakVelocityPairingReal
        hNS ht htau hE hTail htauR φ

  have hSub :
      Set.Icc (0 : ℝ) (q : ℝ)
        ⊆
      Set.Icc (0 : ℝ) tau := by
    intro r hr
    exact ⟨hr.1, hr.2.trans q.property.2⟩

  have hPContinuous :
      ContinuousOn P (Set.Icc (0 : ℝ) (q : ℝ)) :=
    hPContinuousTau.mono hSub

  have hGIntegrable :
      IntervalIntegrable
        G
        volume
        (0 : ℝ)
        (q : ℝ) := by
    dsimp only [G]
    exact
      intervalIntegrable_inner_h3WeakTestVectorPhysicalL2Hilbert_selectedUnitProjectedRHSRealOnElapsed
        hNS ht htau hE hTail htauR φ q.property

  have hPDeriv :
      ∀ r : ℝ,
        r ∈ Set.Ioo (0 : ℝ) (q : ℝ) →
        HasDerivAt P (G r) r := by
    intro r hr

    have hrTau :
        r ∈ Set.Ioo (0 : ℝ) tau :=
      ⟨hr.1, lt_of_lt_of_le hr.2 q.property.2⟩

    dsimp only [P, G]

    exact
      h3PreterminalSelectedUnitWeakVelocityPairingReal_hasDerivAt_projectedRHSRealOnElapsed
        hNS ht htau hE hTail htauR hrTau φ

  have hFTC :
      (∫ r in (0 : ℝ)..(q : ℝ), G r)
        =
      P (q : ℝ) - P 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      q.property.1
      hPContinuous
      hPDeriv
      hGIntegrable

  have hPq :
      P (q : ℝ)
        =
      inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalSelectedVelocityPhysicalL2HilbertAt
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail (q : ℝ)) := by
    dsimp only [P]
    exact
      h3PreterminalSelectedUnitWeakVelocityPairingReal_eq_inner_selectedVelocity
        hNS ht hE hTail φ

  have hP0 :
      P 0
        =
      inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalSelectedVelocityPhysicalL2HilbertAt
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail 0) := by
    dsimp only [P]
    exact
      h3PreterminalSelectedUnitWeakVelocityPairingReal_eq_inner_selectedVelocity
        hNS ht hE hTail φ

  unfold
    h3PreterminalSelectedUnitVelocityIncrementPhysicalL2HilbertOnElapsed

  rw [inner_sub_right]
  rw [← hPq, ← hP0]

  dsimp only [G] at hFTC

  exact hFTC.symm

end

end Euclidean
end Bridge
end PrimeTensor
