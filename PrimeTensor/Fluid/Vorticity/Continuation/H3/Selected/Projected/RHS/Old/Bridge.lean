import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Spectral.State.Old.Bridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.RHS.Difference.Leray.Fixed
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Dual.Curl.Fourier.Reduction

/-!
# Selected projected RHS: exact equality with the old overlap RHS

At a positive selected/old overlap slice the complete weighted H³ spectral
states are now known to agree exactly.

Both projected RHS constructions are the same algebraic Fourier operator of
that state,

    R̂(U) = Δ̂U - P div(U ⊗ U).

Therefore the selected and old quotient-safe Fourier RHS vectors agree
definitionally after rewriting the state equality.

The genuine real physical `L²` RHS vectors have those Fourier vectors as their
exact canonical Plancherel transforms.  Injectivity of the physical Fourier
transform then transports the equality back to the native three-component
Hilbert space.

This removes the selected/old RHS representation seam at order zero.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace ComplexConjugate

noncomputable section

noncomputable local instance axisFintypeH3PathSelectedProjectedRHSOldBridge
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Exact equality of the quotient-safe selected and old projected RHS Fourier
vectors at one positive physical-agreement overlap point. -/
theorem h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius_eq_tailCanonical_of_physicalAgreement
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (q : Set.Icc (0 : ℝ) tau)
    (hq : 0 < (q : ℝ))
    (hAgreement :
      H3PreterminalSelectedPhysicalAgreementAt
        (one_pos : (0 : ℝ) < 1)
        (q : ℝ)
        hNS ht hE hTail) :
    h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
        hNS ht hE hTail
        (h3PreterminalElapsedToSelectedUnitRadius htauR q)
      =
    h3PreterminalTailCanonicalZeroProjectedRHSFourierL2HilbertOnElapsed
        hNS ht hEnd hTail q := by
  have hState :
      h3PreterminalSelectedUnitSpectralStateOnRadius
          hNS ht hE hTail
          (h3PreterminalElapsedToSelectedUnitRadius htauR q)
        =
      h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail q :=
    h3PreterminalSelectedUnitSpectralStateOnRadius_eq_tailCanonical_of_physicalAgreement
      hNS ht hEnd hE hTail htauR q hq hAgreement

  funext i

  unfold
    h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
    h3PreterminalSelectedUnitLaplacianFourierL2OnRadius
    h3PreterminalSelectedUnitLerayForcingFourierL2OnRadius
    h3PreterminalTailCanonicalZeroProjectedRHSFourierL2HilbertOnElapsed
    h3PreterminalTailCanonicalZeroProjectedRHSFourierL2OnElapsed

  dsimp only

  rw [hState]

/-- Exact equality of the genuine real physical selected and old projected RHS
Hilbert vectors at one positive physical-agreement overlap point. -/
theorem h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius_eq_tailCanonical_of_physicalAgreement
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (q : Set.Icc (0 : ℝ) tau)
    (hq : 0 < (q : ℝ))
    (hAgreement :
      H3PreterminalSelectedPhysicalAgreementAt
        (one_pos : (0 : ℝ) < 1)
        (q : ℝ)
        hNS ht hE hTail) :
    h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius
        hNS ht hE hTail
        (h3PreterminalElapsedToSelectedUnitRadius htauR q)
      =
    h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed
        hNS ht hEnd hTail q := by
  let S : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius
      hNS ht hE hTail
      (h3PreterminalElapsedToSelectedUnitRadius htauR q)

  let O : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed
      hNS ht hEnd hTail q

  have hFourier :
      h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
          hNS ht hE hTail
          (h3PreterminalElapsedToSelectedUnitRadius htauR q)
        =
      h3PreterminalTailCanonicalZeroProjectedRHSFourierL2HilbertOnElapsed
          hNS ht hEnd hTail q :=
    h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius_eq_tailCanonical_of_physicalAgreement
      hNS ht hEnd hE hTail htauR q hq hAgreement

  have hRaw :
      h3PhysicalRealFinVectorL2HilbertRawFourier S
        =
      h3PhysicalRealFinVectorL2HilbertRawFourier O := by
    dsimp only [S, O]

    rw [
      h3PhysicalRealFinVectorL2HilbertRawFourier_selectedUnitProjectedRHSPhysicalL2HilbertOnRadius_eq
        hNS ht hE hTail
        (h3PreterminalElapsedToSelectedUnitRadius htauR q),
      h3PhysicalRealFinVectorL2HilbertRawFourier_zeroProjectedRHSPhysicalL2HilbertOnElapsed_eq
        hNS ht hEnd hTail q
    ]

    exact hFourier

  have hZeroRaw :
      h3PhysicalRealFinVectorL2HilbertRawFourier (S - O)
        =
      0 := by
    change
      h3PhysicalRealFinVectorL2HilbertRawFourierRealLinearMap (S - O)
        =
      0

    rw [map_sub]

    change
      h3PhysicalRealFinVectorL2HilbertRawFourier S
        -
      h3PhysicalRealFinVectorL2HilbertRawFourier O
        =
      0

    exact sub_eq_zero.mpr hRaw

  have hZero :
      S - O = 0 :=
    h3PhysicalRealFinVectorL2Hilbert_eq_zero_of_rawFourier_eq_zero
      (S - O) hZeroRaw

  have hSO : S = O :=
    sub_eq_zero.mp hZero

  simpa only [S, O] using hSO

/-- Radius-wide selected/old physical agreement yields exact selected/old
projected-RHS equality at every positive closed elapsed point. -/
theorem h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius_eq_tailCanonical_of_restartRadiusAgreement
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hPhysical :
      H3PreterminalSelectedPhysicalAgreementOnRestartRadius
        (1 : ℝ) E (one_pos : (0 : ℝ) < 1)
        u T t hNS ht hE hTail)
    (q : Set.Icc (0 : ℝ) tau)
    (hq : 0 < (q : ℝ)) :
    h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius
        hNS ht hE hTail
        (h3PreterminalElapsedToSelectedUnitRadius htauR q)
      =
    h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed
        hNS ht hEnd hTail q := by
  let qR :
      Set.Ioc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
    ⟨
      (q : ℝ),
      hq,
      q.property.2.trans htauR
    ⟩

  have hEndq :
      t + (qR : ℝ) < T := by
    dsimp only [qR]
    linarith [q.property.2, hEnd]

  have hAgreement :
      H3PreterminalSelectedPhysicalAgreementAt
        (one_pos : (0 : ℝ) < 1)
        (q : ℝ)
        hNS ht hE hTail := by
    simpa only [qR] using
      hPhysical qR hEndq

  exact
    h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius_eq_tailCanonical_of_physicalAgreement
      hNS ht hEnd hE hTail htauR q hq hAgreement

end

end Euclidean
end Bridge
end PrimeTensor
