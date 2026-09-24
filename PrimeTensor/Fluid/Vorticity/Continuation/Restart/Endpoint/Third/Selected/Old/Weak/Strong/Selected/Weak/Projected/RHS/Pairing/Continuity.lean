import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Selected.Weak.Velocity.Pairing.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Selected.Weak.Forcing.Transfer
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Weak.Forcing.Pairing.Continuity

/-!
# Closed-interval continuity of the selected weak projected-RHS pairing

The selected weak FTC now has closed-interval continuity of its velocity
pairing.  This file closes the matching scalar continuity for the selected
projected RHS pairing.

The two pieces are handled in the weak topology where the existing APIs are
strongest.

* Diffusion is already moved onto twice-differentiated compact tests.  Hence
  its time dependence is only the selected physical velocity pairing, whose
  continuity on `[0,tau]` was proved in the preceding checkpoint.

* The Leray forcing pairing is exactly the existing weak forcing functional
  `h3RawFinLerayOuterProductDivergenceWeakPairing`.  That functional is already
  continuous in the weighted H³ spectral state, and the canonical selected
  restart path is globally continuous.

Subtracting the two gives continuity of the named selected weak projected-RHS
pairing.  The previously closed physical representation theorem then transfers
this to the quotient-safe physical projected-RHS Hilbert pairing, including
the ambient-real elapsed extension used by the weak FTC frontier.

The final theorem packages interval integrability on every `[0,q]` with
`q ∈ [0,tau]`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

attribute [local instance]
  point3MeasureSpaceH3SelectedOldWeakStrongGenericWeakForcingAdvection

noncomputable local instance axisFintypeH3SelectedOldWeakStrongSelectedWeakProjectedRHSPairingContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The selected weak diffusion pairing is continuous on every closed elapsed
subinterval inside the unit restart radius. -/
theorem continuous_h3PreterminalSelectedUnitWeakDiffusionPairingOnElapsed
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
    Continuous
      (fun q : Set.Icc (0 : ℝ) tau =>
        h3PreterminalSelectedUnitWeakDiffusionPairingAt
          hNS ht hE hTail (q : ℝ) φ) := by
  unfold h3PreterminalSelectedUnitWeakDiffusionPairingAt

  apply continuous_finset_sum
  intro i hi

  apply continuous_finset_sum
  intro k hk

  exact
    continuous_inner_h3WeakTestFunctionPhysicalL2_selectedVelocityOnElapsed
      hNS ht htau hE hTail htauR
      (h3WeakTestFunctionSecondSpatialDerivative
        (h3AxisOfFin3 k)
        (φ i))
      i

/-- The selected physical Leray-forcing pairing with a fixed compact test is
continuous on the closed elapsed interval. -/
theorem continuous_inner_h3WeakTestVectorPhysicalL2Hilbert_selectedUnitLerayForcingOnElapsed
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
    Continuous
      (fun q : Set.Icc (0 : ℝ) tau =>
        inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert φ)
          (h3PreterminalSelectedUnitLerayForcingPhysicalL2HilbertOnRadius
            hNS ht hE hTail
            (h3PreterminalElapsedToSelectedUnitRadius htauR q))) := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSelectedRestart
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail

  have hW :
      Continuous W := by
    dsimp only [W]
    unfold h3PreterminalTailCanonicalSelectedRestart
    exact
      continuous_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        (one_pos : (0 : ℝ) < 1)
        (h3PreterminalTailCanonicalAnchorSpectralState
          hNS ht hTail)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
          hNS ht hE hTail)

  have hWeakForcing :
      Continuous
        (fun q : Set.Icc (0 : ℝ) tau =>
          ∑ i : Fin 3,
            h3RawFinLerayOuterProductDivergenceWeakPairing
              (φ i) i (W (q : ℝ))) := by
    apply continuous_finset_sum
    intro i hi

    exact
      (continuous_h3RawFinLerayOuterProductDivergenceWeakPairing
        (φ i) i).comp
        (hW.comp continuous_subtype_val)

  have hEq :
      (fun q : Set.Icc (0 : ℝ) tau =>
        inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert φ)
          (h3PreterminalSelectedUnitLerayForcingPhysicalL2HilbertOnRadius
            hNS ht hE hTail
            (h3PreterminalElapsedToSelectedUnitRadius htauR q)))
        =
      (fun q : Set.Icc (0 : ℝ) tau =>
        ∑ i : Fin 3,
          h3RawFinLerayOuterProductDivergenceWeakPairing
            (φ i) i (W (q : ℝ))) := by
    funext q

    let qR :
        Set.Icc
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
      h3PreterminalElapsedToSelectedUnitRadius
        htauR q

    have h :=
      inner_h3WeakTestVectorPhysicalL2Hilbert_selectedUnitLerayForcing_eq_literalC0
        hNS ht hE hTail qR φ

    dsimp only at h

    simpa only [
      h3RawFinLerayOuterProductDivergenceWeakPairing,
      qR,
      W,
      h3PreterminalElapsedToSelectedUnitRadius_coe
    ] using h

  rw [hEq]
  exact hWeakForcing

/-- The named selected weak projected-RHS pairing is continuous on the complete
closed elapsed interval. -/
theorem continuous_h3PreterminalSelectedUnitWeakProjectedRHSPairingOnElapsed
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
    Continuous
      (fun q : Set.Icc (0 : ℝ) tau =>
        h3PreterminalSelectedUnitWeakProjectedRHSPairingAtRadius
          hNS ht hE hTail
          (h3PreterminalElapsedToSelectedUnitRadius htauR q)
          φ) := by
  unfold h3PreterminalSelectedUnitWeakProjectedRHSPairingAtRadius

  have hDiff :=
    continuous_h3PreterminalSelectedUnitWeakDiffusionPairingOnElapsed
      hNS ht htau hE hTail htauR φ

  have hForce :=
    continuous_inner_h3WeakTestVectorPhysicalL2Hilbert_selectedUnitLerayForcingOnElapsed
      hNS ht htau hE hTail htauR φ

  have hDiff' :
      Continuous
        (fun q : Set.Icc (0 : ℝ) tau =>
          h3PreterminalSelectedUnitWeakDiffusionPairingAt
            hNS ht hE hTail
            ((h3PreterminalElapsedToSelectedUnitRadius htauR q : _) : ℝ)
            φ) := by
    simpa only [
      h3PreterminalElapsedToSelectedUnitRadius_coe
    ] using hDiff

  change
    Continuous
      ((fun q : Set.Icc (0 : ℝ) tau =>
          h3PreterminalSelectedUnitWeakDiffusionPairingAt
            hNS ht hE hTail
            ((h3PreterminalElapsedToSelectedUnitRadius htauR q : _) : ℝ)
            φ)
        -
       (fun q : Set.Icc (0 : ℝ) tau =>
          inner ℝ
            (h3WeakTestVectorPhysicalL2Hilbert φ)
            (h3PreterminalSelectedUnitLerayForcingPhysicalL2HilbertOnRadius
              hNS ht hE hTail
              (h3PreterminalElapsedToSelectedUnitRadius htauR q))))

  exact hDiff'.sub hForce

/-- Pairing with the selected physical projected RHS is continuous on the
closed elapsed subtype. -/
theorem continuous_inner_h3WeakTestVectorPhysicalL2Hilbert_selectedUnitProjectedRHSOnElapsed
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
    Continuous
      (fun q : Set.Icc (0 : ℝ) tau =>
        inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert φ)
          (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius
            hNS ht hE hTail
            (h3PreterminalElapsedToSelectedUnitRadius htauR q))) := by
  have hWeak :=
    continuous_h3PreterminalSelectedUnitWeakProjectedRHSPairingOnElapsed
      hNS ht htau hE hTail htauR φ

  have hEq :
      (fun q : Set.Icc (0 : ℝ) tau =>
        inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert φ)
          (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius
            hNS ht hE hTail
            (h3PreterminalElapsedToSelectedUnitRadius htauR q)))
        =
      (fun q : Set.Icc (0 : ℝ) tau =>
        h3PreterminalSelectedUnitWeakProjectedRHSPairingAtRadius
          hNS ht hE hTail
          (h3PreterminalElapsedToSelectedUnitRadius htauR q)
          φ) := by
    funext q
    symm

    exact
      h3PreterminalSelectedUnitWeakProjectedRHSPairingAtRadius_eq_inner_projectedRHS
        hNS ht hE hTail
        (h3PreterminalElapsedToSelectedUnitRadius htauR q)
        φ

  rw [hEq]
  exact hWeak

/-- The ambient-real elapsed selected projected-RHS pairing is continuous when
restricted to the physical closed elapsed interval. -/
theorem continuousOn_inner_h3WeakTestVectorPhysicalL2Hilbert_selectedUnitProjectedRHSRealOnElapsed
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
      (fun r : ℝ =>
        inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert φ)
          (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
            hNS ht hE hTail htauR r))
      (Set.Icc (0 : ℝ) tau) := by
  rw [continuousOn_iff_continuous_domRestrict]

  have hEq :
      (Set.Icc (0 : ℝ) tau).domRestrict
        (fun r : ℝ =>
          inner ℝ
            (h3WeakTestVectorPhysicalL2Hilbert φ)
            (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
              hNS ht hE hTail htauR r))
        =
      (fun q : Set.Icc (0 : ℝ) tau =>
        inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert φ)
          (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius
            hNS ht hE hTail
            (h3PreterminalElapsedToSelectedUnitRadius htauR q))) := by
    funext q

    change
      inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert φ)
          (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
            hNS ht hE hTail htauR (q : ℝ))
        =
      inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert φ)
          (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius
            hNS ht hE hTail
            (h3PreterminalElapsedToSelectedUnitRadius htauR q))

    rw [
      h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed_apply_of_mem
        hNS ht hE hTail htauR q.property
    ]

  rw [hEq]

  exact
    continuous_inner_h3WeakTestVectorPhysicalL2Hilbert_selectedUnitProjectedRHSOnElapsed
      hNS ht htau hE hTail htauR φ

/-- The ambient-real selected projected-RHS pairing is interval integrable on
every initial subinterval `[0,q]` of `[0,tau]`. -/
theorem intervalIntegrable_inner_h3WeakTestVectorPhysicalL2Hilbert_selectedUnitProjectedRHSRealOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (φ : H3WeakTestVector)
    (hq : q ∈ Set.Icc (0 : ℝ) tau) :
    IntervalIntegrable
      (fun r : ℝ =>
        inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert φ)
          (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
            hNS ht hE hTail htauR r))
      volume
      (0 : ℝ)
      q := by
  have hContinuousTau :=
    continuousOn_inner_h3WeakTestVectorPhysicalL2Hilbert_selectedUnitProjectedRHSRealOnElapsed
      hNS ht htau hE hTail htauR φ

  have hSub :
      Set.Icc (0 : ℝ) q ⊆ Set.Icc (0 : ℝ) tau := by
    intro r hr
    exact ⟨hr.1, hr.2.trans hq.2⟩

  have hContinuous :
      ContinuousOn
        (fun r : ℝ =>
          inner ℝ
            (h3WeakTestVectorPhysicalL2Hilbert φ)
            (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
              hNS ht hE hTail htauR r))
        (Set.Icc (0 : ℝ) q) :=
    hContinuousTau.mono hSub

  apply ContinuousOn.intervalIntegrable
  simpa only [uIcc_of_le hq.1] using hContinuous

end

end Euclidean
end Bridge
end PrimeTensor
