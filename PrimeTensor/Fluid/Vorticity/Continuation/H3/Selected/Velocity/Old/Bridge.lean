import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Projected.RHS.Old.Bridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Difference.Leray.Fixed
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Dual.Curl.Fourier.Reduction

/-!
# Selected physical velocity: exact equality with the old overlap velocity

The positive-overlap weighted H³ states have already been identified exactly.

Both physical velocity Hilbert vectors have canonical raw Fourier transforms
obtained by applying the same H³ deweighting map coordinatewise to those
weighted states. Rewriting by the spectral-state equality therefore identifies
their raw Fourier vectors exactly. Plancherel injectivity then returns the
equality to the native physical `PiLp 2` Hilbert space.

This strengthens the previous equality of kinetic energies to equality of the
actual three-component physical velocity vectors.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace ComplexConjugate

noncomputable section

noncomputable local instance axisFintypeH3PathSelectedVelocityOldBridge
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The selected and old physical velocity Hilbert vectors coincide at every
positive physical-agreement overlap point. -/
theorem h3PreterminalSelectedVelocityPhysicalL2HilbertAt_eq_canonicalVelocityPhysicalL2HilbertOnElapsed_of_physicalAgreement
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
    h3PreterminalSelectedVelocityPhysicalL2HilbertAt
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail (q : ℝ)
      =
    h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
        hNS ht hEnd hTail q := by
  let qR :
      Set.Icc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
    h3PreterminalElapsedToSelectedUnitRadius htauR q

  let S : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalSelectedVelocityPhysicalL2HilbertAt
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail (q : ℝ)

  let O : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
      hNS ht hEnd hTail q

  have hState :
      h3PreterminalSelectedUnitSpectralStateOnRadius
          hNS ht hE hTail qR
        =
      h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail q := by
    dsimp only [qR]
    exact
      h3PreterminalSelectedUnitSpectralStateOnRadius_eq_tailCanonical_of_physicalAgreement
        hNS ht hEnd hE hTail htauR q hq hAgreement

  have hRaw :
      h3PhysicalRealFinVectorL2HilbertRawFourier S
        =
      h3PhysicalRealFinVectorL2HilbertRawFourier O := by
    rw [show
      h3PhysicalRealFinVectorL2HilbertRawFourier S
        =
      h3PreterminalSelectedUnitRawFourierVectorOnRadius
        hNS ht hE hTail qR by
          dsimp only [S, qR]
          simpa only [h3PreterminalElapsedToSelectedUnitRadius_coe] using
            h3PhysicalRealFinVectorL2HilbertRawFourier_selectedUnitVelocityOnRadius_eq
              hNS ht hE hTail
              (h3PreterminalElapsedToSelectedUnitRadius htauR q)]

    rw [show
      h3PhysicalRealFinVectorL2HilbertRawFourier O
        =
      fun i : Fin 3 =>
        h3SpectralScalarRawFourierL2
          ((h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNS ht hEnd hTail q) i) by
          dsimp only [O]
          exact
            h3PhysicalRealFinVectorL2HilbertRawFourier_velocityOnElapsed_eq_deweightedSpectral
              hNS ht hEnd hTail q]

    unfold h3PreterminalSelectedUnitRawFourierVectorOnRadius
    rw [hState]

  have hZeroRaw :
      h3PhysicalRealFinVectorL2HilbertRawFourier (S - O)
        =
      0 := by
    rw [
      h3PhysicalRealFinVectorL2HilbertRawFourier_sub,
      hRaw,
      sub_self
    ]

  have hZero :
      S - O = 0 :=
    h3PhysicalRealFinVectorL2Hilbert_eq_zero_of_rawFourier_eq_zero
      (S - O) hZeroRaw

  have hSO : S = O :=
    sub_eq_zero.mp hZero

  simpa only [S, O] using hSO

/-- Radius-wide physical agreement gives equality of the actual selected and
old physical velocity Hilbert vectors at every positive closed elapsed point. -/
theorem h3PreterminalSelectedVelocityPhysicalL2HilbertAt_eq_canonicalVelocityPhysicalL2HilbertOnElapsed_of_restartRadiusAgreement
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
    h3PreterminalSelectedVelocityPhysicalL2HilbertAt
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail (q : ℝ)
      =
    h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
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
    h3PreterminalSelectedVelocityPhysicalL2HilbertAt_eq_canonicalVelocityPhysicalL2HilbertOnElapsed_of_physicalAgreement
      hNS ht hEnd hE hTail htauR q hq hAgreement

end

end Euclidean
end Bridge
end PrimeTensor
