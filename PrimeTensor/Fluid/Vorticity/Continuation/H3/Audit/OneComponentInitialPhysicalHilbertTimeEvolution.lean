import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialCanonicalWeakFTCAbsoluteTransfer

/-!
# Canonical weak momentum FTC upgrades to physical Hilbert time evolution

This extends the absolute-time transfer from compact solenoidal and Schwartz
scalar pairings to the *actual physical L² Hilbert velocity*.  The source is
the actual physical spectral Laplacian minus the actual physical Leray term.

The key input is the preceding, proved solenoidal weak FTC, together with
the already-proved Leray fixedness/density and source continuity.  We obtain
an exact physical Bochner evolution and strong `HasDerivAt` on an interior
canonical restart window, then a strong derivative and continuity at every
strictly positive preterminal time under the old joint-continuity premise.

No claim is made that this extra old temporal joint-continuity premise follows
from bare H³ admissibility; initial-time integrability, residual closure, and
the terminal endpoint remain independent.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeInitialPhysicalHilbertTimeEvolution
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 800000

/-- The canonical solenoidal weak FTC gives the *whole vector* physical
Bochner identity on an absolute-time old restart interval, not only its
pairings with divergence-free test fields. -/
theorem h3Audit_initialCanonicalWeakFTC_implies_physicalHilbertEvolution_onElapsed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T S t τ E : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hShort : LoggedPreterminalH3PathAdmissible u S)
    (hST : S ≤ T)
    (ht : t ∈ Set.Ioo (0 : ℝ) S)
    (hτ : 0 < τ)
    (hEnd : t + τ < S)
    (hTail : CanonicalH3TailDataFrom u t S E)
    (hWeakFTC :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakFTCOnElapsed
        hShort.navier_stokes ht hτ hEnd hTail)
    (r : ℝ) (hr : r ∈ Set.Icc t (t + τ)) :
    h3AuditInitialOldPhysicalHilbertTotal hH3 r =
      h3AuditInitialOldPhysicalHilbertTotal hH3 t +
        ∫ x in t..r,
          (h3AuditInitialActualSpectralLaplacianTotal hH3 x -
            h3AuditInitialActualSpectralLerayTotal hH3 x) := by
  have htτT : t + τ < T := lt_of_lt_of_le hEnd hST
  have hFfixed : ∀ x : ℝ, x ∈ Set.Icc t (t + τ) →
      H3PhysicalRealFinVectorL2HilbertLerayFixed
        (h3AuditInitialOldPhysicalHilbertTotal hH3 x) := by
    intro x hx
    exact h3Audit_initialOldPhysicalHilbert_lerayFixed_at_positiveTime
      hH3 x ⟨lt_of_lt_of_le ht.1 hx.1,
        lt_of_le_of_lt hx.2 htτT⟩
  exact h3Audit_physicalSolenoidalWeakFTC_implies_HilbertEvolution
    (h3AuditInitialOldPhysicalHilbertTotal hH3)
    (fun x : ℝ =>
      h3AuditInitialActualSpectralLaplacianTotal hH3 x -
        h3AuditInitialActualSpectralLerayTotal hH3 x)
    t (t + τ) (lt_add_of_pos_right t hτ)
    (h3Audit_initialActualProjectedRHS_continuousOn_strictInterval
      hH3 t (t + τ) ht.1 (lt_add_of_pos_right t hτ) htτT)
    hFfixed
    (h3Audit_initialActualProjectedRHS_lerayFixed_allTimes hH3)
    (h3Audit_initialCanonicalWeakFTC_implies_absoluteSolenoidalWeakFTC
      hH3 hShort hST ht hτ hEnd hTail hWeakFTC)
    r hr

/-- On the open canonical interval, physical momentum is differentiable
*strongly in L²*, with precisely the already identified physical projected
Navier--Stokes RHS. -/
theorem h3Audit_initialCanonicalWeakFTC_implies_physicalHilbertHasDerivAt_onElapsed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T S t τ E : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hShort : LoggedPreterminalH3PathAdmissible u S)
    (hST : S ≤ T)
    (ht : t ∈ Set.Ioo (0 : ℝ) S)
    (hτ : 0 < τ)
    (hEnd : t + τ < S)
    (hTail : CanonicalH3TailDataFrom u t S E)
    (hWeakFTC :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakFTCOnElapsed
        hShort.navier_stokes ht hτ hEnd hTail)
    (s : ℝ) (hs : s ∈ Set.Ioo t (t + τ)) :
    HasDerivAt (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3AuditInitialActualSpectralLaplacianTotal hH3 s -
        h3AuditInitialActualSpectralLerayTotal hH3 s) s := by
  have htτT : t + τ < T := lt_of_lt_of_le hEnd hST
  have hFfixed : ∀ x : ℝ, x ∈ Set.Icc t (t + τ) →
      H3PhysicalRealFinVectorL2HilbertLerayFixed
        (h3AuditInitialOldPhysicalHilbertTotal hH3 x) := by
    intro x hx
    exact h3Audit_initialOldPhysicalHilbert_lerayFixed_at_positiveTime
      hH3 x ⟨lt_of_lt_of_le ht.1 hx.1,
        lt_of_le_of_lt hx.2 htτT⟩
  exact h3Audit_physicalSolenoidalWeakFTC_implies_HilbertHasDerivAt
    (h3AuditInitialOldPhysicalHilbertTotal hH3)
    (fun x : ℝ =>
      h3AuditInitialActualSpectralLaplacianTotal hH3 x -
        h3AuditInitialActualSpectralLerayTotal hH3 x)
    t (t + τ) (lt_add_of_pos_right t hτ)
    (h3Audit_initialActualProjectedRHS_continuousOn_strictInterval
      hH3 t (t + τ) ht.1 (lt_add_of_pos_right t hτ) htτT)
    hFfixed
    (h3Audit_initialActualProjectedRHS_lerayFixed_allTimes hH3)
    (h3Audit_initialCanonicalWeakFTC_implies_absoluteSolenoidalWeakFTC
      hH3 hShort hST ht hτ hEnd hTail hWeakFTC)
    s hs

/-- Under the established old joint-continuity *premise*, the physical
Bochner momentum equation holds on each strictly positive canonical window. -/
theorem h3Audit_initialOldJoint_implies_physicalHilbertEvolution_onElapsed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T S t τ E : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hShort : LoggedPreterminalH3PathAdmissible u S)
    (hST : S ≤ T)
    (ht : t ∈ Set.Ioo (0 : ℝ) S)
    (hτ : 0 < τ)
    (hEnd : t + τ < S)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t S E)
    (hOldJoint : H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous u S)
    (r : ℝ) (hr : r ∈ Set.Icc t (t + τ)) :
    h3AuditInitialOldPhysicalHilbertTotal hH3 r =
      h3AuditInitialOldPhysicalHilbertTotal hH3 t +
        ∫ x in t..r,
          (h3AuditInitialActualSpectralLaplacianTotal hH3 x -
            h3AuditInitialActualSpectralLerayTotal hH3 x) := by
  have hWeakFTC :=
    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakFTCOnElapsed_of_oldTemporalDerivativeJointlyContinuous
      hShort.navier_stokes ht hτ hEnd hE hTail hOldJoint
  exact h3Audit_initialCanonicalWeakFTC_implies_physicalHilbertEvolution_onElapsed
    hH3 hShort hST ht hτ hEnd hTail hWeakFTC r hr

/-- Old temporal joint continuity implies the strong physical L² momentum
derivative at every point of an interior canonical restart interval. -/
theorem h3Audit_initialOldJoint_implies_physicalHilbertHasDerivAt_onElapsed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T S t τ E : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hShort : LoggedPreterminalH3PathAdmissible u S)
    (hST : S ≤ T)
    (ht : t ∈ Set.Ioo (0 : ℝ) S)
    (hτ : 0 < τ)
    (hEnd : t + τ < S)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t S E)
    (hOldJoint : H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous u S)
    (s : ℝ) (hs : s ∈ Set.Ioo t (t + τ)) :
    HasDerivAt (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3AuditInitialActualSpectralLaplacianTotal hH3 s -
        h3AuditInitialActualSpectralLerayTotal hH3 s) s := by
  have hWeakFTC :=
    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakFTCOnElapsed_of_oldTemporalDerivativeJointlyContinuous
      hShort.navier_stokes ht hτ hEnd hE hTail hOldJoint
  exact h3Audit_initialCanonicalWeakFTC_implies_physicalHilbertHasDerivAt_onElapsed
    hH3 hShort hST ht hτ hEnd hTail hWeakFTC s hs

/-- Local canonical restart coverage now upgrades the old joint-continuity
premise into strong physical L² momentum differentiability at *every*
strictly positive preterminal time. -/
theorem h3Audit_initialOldJoint_implies_physicalHilbertHasDerivAt_at_positiveTime
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hOldJoint : H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous u T)
    (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3AuditInitialActualSpectralLaplacianTotal hH3 s -
        h3AuditInitialActualSpectralLerayTotal hH3 s) s := by
  obtain ⟨t, S, E, ht, hST, hE, hTail,
    hElapsed, _hRadius, _hMatch, hsS⟩ :=
    hH3.exists_localCanonicalRestartWindowAt hs
  let τ : ℝ := (s + S) / 2 - t
  have hτ : 0 < τ := by
    dsimp only [τ]
    linarith only [hElapsed, hsS]
  have hEnd : t + τ < S := by
    dsimp only [τ]
    linarith only [hsS]
  have hsInterior : s ∈ Set.Ioo t (t + τ) := by
    constructor
    · exact sub_pos.mp hElapsed
    · dsimp only [τ]
      linarith only [hsS]
  have hSpos : 0 < S := lt_trans ht.1 ht.2
  let hShort : LoggedPreterminalH3PathAdmissible u S :=
    h3Audit_h3PathAdmissible_restrict_terminal hH3 hSpos
      (le_of_lt hST)
  have hOldJointShort :
      H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous u S := by
    intro i
    exact (hOldJoint i).mono (by
      intro z hz
      exact ⟨⟨hz.1.1, lt_of_lt_of_le hz.1.2 (le_of_lt hST)⟩, hz.2⟩)
  exact h3Audit_initialOldJoint_implies_physicalHilbertHasDerivAt_onElapsed
    hH3 hShort (le_of_lt hST) ht hτ hEnd hE hTail
    hOldJointShort s hsInterior

/-- In particular the entire physical L² old velocity (not merely its
Schwartz pairings) is continuous throughout strictly positive preterminal
time. No claim about continuity at time zero is needed or used. -/
theorem h3Audit_initialOldJoint_implies_physicalHilbertContinuousOn_positiveTime
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hOldJoint : H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous u T) :
    ContinuousOn (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (Set.Ioo (0 : ℝ) T) := by
  intro s hs
  exact
    (h3Audit_initialOldJoint_implies_physicalHilbertHasDerivAt_at_positiveTime
      hH3 hOldJoint s hs).continuousAt.continuousWithinAt

end
end Euclidean
end Bridge
end PrimeTensor
