import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialActualPhysicalSourceMeasurability
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Old.RHS.Decomposition
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.RHS.Reality

/-!
# Actual-time initial sources equal the old physical Navier--Stokes sources

The corrected source constructors are inverse-Fourier reconstructions of the
actual old H³ spectral velocity.  This module proves that, on *any* strictly
positive canonical restart window, they equal the existing physical old
Laplacian and the existing physical Leray transport, respectively.

For diffusion the equality is not definitional: we use the genuine physical
second-jet Fourier identity, Hermitian reality of its Fourier Laplacian,
and injectivity of scalar Plancherel.  For Leray transport, the two inverse-
Fourier packages agree directly once both use the same actual old spectral
snapshot.  The old physical RHS decomposition then gives the full physical
Navier--Stokes projected source, exactly and without a new identification
assumption.

Finally the previously proved old weak temporal Navier--Stokes PDE, tested
against divergence-free compact vectors, is rewritten against *these exact
actual-time reconstructed sources*.  This is NOT the scalar `HasDerivAt`
identity against every (possibly non-solenoidal) Schwartz vector used by the
initial weak FTC contract.  Initial H³-energy integrability and the vanishing
relative-energy residual also remain independent obligations.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3AuditInitialActualPhysicalSourceIdentification
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 800000

/-- On any strict positive restart window, the corrected actual-time physical
Laplacian equals the old physical L² Laplacian (the genuine second spatial
jet), not merely an equinormed Fourier candidate. -/
theorem h3Audit_initialActualSpectralLaplacian_eq_oldPhysicalOnElapsed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T S t τ E : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hShort : LoggedPreterminalH3PathAdmissible u S)
    (hST : S ≤ T)
    (ht : t ∈ Set.Ioo (0 : ℝ) S)
    (hEnd : t + τ < S)
    (hTail : CanonicalH3TailDataFrom u t S E)
    (q : Set.Icc (0 : ℝ) τ) :
    h3AuditInitialActualSpectralLaplacianTotal hH3 (t + (q : ℝ)) =
      h3PreterminalTailCanonicalOldLaplacianPhysicalL2HilbertOnElapsed
        hShort.navier_stokes ht hEnd hTail q := by
  have hs : t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) S :=
    h3PreterminalElapsedTime_mem_Ioo ht hEnd q
  have hsT : t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) T :=
    ⟨hs.1, lt_of_lt_of_le hs.2 hST⟩
  have hU :
      h3AuditActualSpectralVelocityTotal hH3 (t + (q : ℝ)) =
        h3PreterminalTailCanonicalSpectralStateOnElapsed
          hShort.navier_stokes ht hEnd hTail q :=
    h3Audit_actualSpectralVelocityTotal_eq_canonicalElapsed
      hH3 hShort hST ht hEnd hTail q
  unfold h3AuditInitialActualSpectralLaplacianTotal
  rw [dif_pos hsT, hU]
  apply PiLp.ext
  intro i
  change
    h3FromFourierRealL2
      (h3RealPartFourierL2
        ((MeasureTheory.Lp.fourierTransformₗᵢ
            H3FourierPoint3 ℂ).symm
          (h3SpectralScalarLaplacianRawFourierL2
            ((h3PreterminalTailCanonicalSpectralStateOnElapsed
                hShort.navier_stokes ht hEnd hTail q) i)))) =
    h3PreterminalTailCanonicalVelocityLaplacianPhysicalL2OnElapsed
      hShort.navier_stokes ht hEnd hTail q i
  apply h3ScalarFourierL2_injective_zeroWeak
  rw [h3ScalarFourierL2_realPhysicalReconstruction_eq_of_hermitian
    (h3SpectralScalarLaplacianRawFourierL2
      ((h3PreterminalTailCanonicalSpectralStateOnElapsed
          hShort.navier_stokes ht hEnd hTail q) i))
    (h3PreterminalTailCanonicalSnapshotLaplacianFourierL2_hermitian
      hShort.navier_stokes ht hEnd hTail q i)]
  rw [h3ScalarFourierL2_h3PreterminalTailCanonicalVelocityLaplacianPhysicalL2OnElapsed
    hShort.navier_stokes ht hEnd hTail q i]
  exact (h3PreterminalTailCanonicalVelocityLaplacianFourierL2OnElapsed_eq_snapshotLaplacian
    hShort.navier_stokes ht hEnd hTail q i).symm

/-- The corrected actual-time nonlinear source is exactly the old physical
Leray forcing, reconstructed from the same old spectral velocity snapshot. -/
theorem h3Audit_initialActualSpectralLeray_eq_oldPhysicalOnElapsed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T S t τ E : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hShort : LoggedPreterminalH3PathAdmissible u S)
    (hST : S ≤ T)
    (ht : t ∈ Set.Ioo (0 : ℝ) S)
    (hEnd : t + τ < S)
    (hTail : CanonicalH3TailDataFrom u t S E)
    (q : Set.Icc (0 : ℝ) τ) :
    h3AuditInitialActualSpectralLerayTotal hH3 (t + (q : ℝ)) =
      h3PreterminalTailCanonicalOldLerayForcingPhysicalL2HilbertOnElapsed
        hShort.navier_stokes ht hEnd hTail q := by
  have hs : t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) S :=
    h3PreterminalElapsedTime_mem_Ioo ht hEnd q
  have hsT : t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) T :=
    ⟨hs.1, lt_of_lt_of_le hs.2 hST⟩
  have hU :
      h3AuditActualSpectralVelocityTotal hH3 (t + (q : ℝ)) =
        h3PreterminalTailCanonicalSpectralStateOnElapsed
          hShort.navier_stokes ht hEnd hTail q :=
    h3Audit_actualSpectralVelocityTotal_eq_canonicalElapsed
      hH3 hShort hST ht hEnd hTail q
  unfold h3AuditInitialActualSpectralLerayTotal
  rw [dif_pos hsT, hU]
  apply PiLp.ext
  intro i
  rfl

/-- The actual-time diffusion-minus-Leray source is the genuine old physical
projected Navier--Stokes RHS on every strict positive restart window. -/
theorem h3Audit_initialActualSpectralProjectedRHS_eq_oldPhysicalOnElapsed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T S t τ E : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hShort : LoggedPreterminalH3PathAdmissible u S)
    (hST : S ≤ T)
    (ht : t ∈ Set.Ioo (0 : ℝ) S)
    (hEnd : t + τ < S)
    (hTail : CanonicalH3TailDataFrom u t S E)
    (q : Set.Icc (0 : ℝ) τ) :
    h3AuditInitialActualSpectralLaplacianTotal hH3 (t + (q : ℝ)) -
      h3AuditInitialActualSpectralLerayTotal hH3 (t + (q : ℝ)) =
      h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed
        hShort.navier_stokes ht hEnd hTail q := by
  calc
    h3AuditInitialActualSpectralLaplacianTotal hH3 (t + (q : ℝ)) -
        h3AuditInitialActualSpectralLerayTotal hH3 (t + (q : ℝ)) =
      h3PreterminalTailCanonicalOldLaplacianPhysicalL2HilbertOnElapsed
          hShort.navier_stokes ht hEnd hTail q -
        h3PreterminalTailCanonicalOldLerayForcingPhysicalL2HilbertOnElapsed
          hShort.navier_stokes ht hEnd hTail q := by
      rw [h3Audit_initialActualSpectralLaplacian_eq_oldPhysicalOnElapsed
        hH3 hShort hST ht hEnd hTail q,
        h3Audit_initialActualSpectralLeray_eq_oldPhysicalOnElapsed
          hH3 hShort hST ht hEnd hTail q]
    _ = h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed
          hShort.navier_stokes ht hEnd hTail q :=
      (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed_eq_laplacian_sub_leray
        hShort.navier_stokes ht hEnd hTail q).symm

/-- The already-proved physical Navier--Stokes temporal PDE on a strict
positive restart window pairs EXACTLY with the corrected reconstructed RHS
for divergence-free compact vector tests.  No additional physical-RHS
identification hypothesis is used. -/
theorem h3Audit_initialActualSpectralProjectedRHS_weakTemporalPairing_onElapsed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T S t τ E : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hShort : LoggedPreterminalH3PathAdmissible u S)
    (hST : S ≤ T)
    (ht : t ∈ Set.Ioo (0 : ℝ) S)
    (hEnd : t + τ < S)
    (hTail : CanonicalH3TailDataFrom u t S E)
    (q : Set.Icc (0 : ℝ) τ)
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ) :
    (∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (temporal.d
            (fun a : ℝ =>
              loggedVelocityComponent u a (h3AxisOfFin3 i) x)
            (t + (q : ℝ)))
        ∂volume) =
    inner ℝ
      (h3WeakTestVectorPhysicalL2Hilbert φ)
      (h3AuditInitialActualSpectralLaplacianTotal hH3 (t + (q : ℝ)) -
        h3AuditInitialActualSpectralLerayTotal hH3 (t + (q : ℝ))) := by
  have hOld :=
    h3PreterminalLoggedVelocity_weakTemporalPairing_eq_zeroProjectedRHSPhysicalL2HilbertOnElapsed
      hShort.navier_stokes ht hEnd hTail q φ hφ
  have hIdent :=
    h3Audit_initialActualSpectralProjectedRHS_eq_oldPhysicalOnElapsed
      hH3 hShort hST ht hEnd hTail q
  rw [hIdent]
  exact hOld

/-- The local canonical restart windows cover every strictly positive time.
Consequently the actual old physical Navier--Stokes weak momentum equation
holds at *every* positive preterminal time with the now-identified, corrected
inverse-Fourier diffusion-minus-Leray physical source.  The test is still
required to be divergence-free and compactly supported. -/
theorem h3Audit_initialActualSpectralProjectedRHS_weakTemporalPairing_at_positiveTime
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ) :
    (∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (temporal.d
            (fun a : ℝ =>
              loggedVelocityComponent u a (h3AxisOfFin3 i) x)
            s)
        ∂volume) =
    inner ℝ
      (h3WeakTestVectorPhysicalL2Hilbert φ)
      (h3AuditInitialActualSpectralLaplacianTotal hH3 s -
        h3AuditInitialActualSpectralLerayTotal hH3 s) := by
  obtain ⟨t, S, E, ht, hST, _hE, hTail,
    hElapsed, _hRadius, _hMatch, hsS⟩ :=
    hH3.exists_localCanonicalRestartWindowAt hs
  let τ : ℝ := s - t
  have hτ : 0 < τ := by
    dsimp only [τ]
    exact hElapsed
  have hEnd : t + τ < S := by
    dsimp only [τ]
    linarith only [hsS]
  have hSpos : 0 < S := lt_trans ht.1 ht.2
  let hShort : LoggedPreterminalH3PathAdmissible u S :=
    h3Audit_h3PathAdmissible_restrict_terminal hH3 hSpos
      (le_of_lt hST)
  let q : Set.Icc (0 : ℝ) τ := ⟨τ, hτ.le, le_rfl⟩
  have hTime : t + (q : ℝ) = s := by
    dsimp only [q, τ]
    ring
  have hLocal :=
    h3Audit_initialActualSpectralProjectedRHS_weakTemporalPairing_onElapsed
      hH3 hShort (le_of_lt hST) ht hEnd hTail q φ hφ
  simpa only [hTime] using hLocal

end
end Euclidean
end Bridge
end PrimeTensor
