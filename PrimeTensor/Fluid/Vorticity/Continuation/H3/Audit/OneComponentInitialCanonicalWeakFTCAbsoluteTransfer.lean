import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialSolenoidalWeakFTCStrongDerivative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Projected.RHS.Weak.Evolution.Old.Joint

/-!
# Old canonical weak FTC transported to positive absolute physical time

The old endpoint-independent branch supplies the solenoidal scalar weak FTC
in elapsed time on a canonical restart window.  The initial audit requires
that same evolution for the *actual* old physical velocity and the newly
identified actual physical projected RHS, in absolute time.

The first theorem performs this nontrivial representation transfer.  It uses
exact physical velocity/zero-jet compatibility, the already-proved physical
RHS identification and interval-integral translation.  No new temporal
integrability or derivative identity is assumed beyond the old canonical
solenoidal weak FTC itself.

The subsequent theorems combine it with the previously proved Leray-density
weak-to-strong derivative result.  Under the independently stated joint
continuity of the old temporal derivative, the existing old-branch weak FTC
closes that last solenoidal temporal premise, hence the unrestricted Schwartz
momentum derivative holds at every positive preterminal time.

The joint continuity frontier is not proved by the basic H3 admissibility
axioms.  Initial H3 energy integrability, the initial relative-energy defect,
and terminal actual-vorticity endpoint hypotheses remain separate.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3AuditInitialCanonicalWeakFTCAbsoluteTransfer
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 800000

/-- The true physical old velocity at each absolute time in a strict
canonical window is exactly the old physical zero-jet Hilbert state at the
corresponding elapsed coordinate. -/
theorem h3Audit_initialOldPhysicalHilbertTotal_eq_canonicalElapsed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T S t τ E : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hShort : LoggedPreterminalH3PathAdmissible u S)
    (hST : S ≤ T)
    (ht : t ∈ Set.Ioo (0 : ℝ) S)
    (hEnd : t + τ < S)
    (hTail : CanonicalH3TailDataFrom u t S E)
    (q : Set.Icc (0 : ℝ) τ) :
    h3AuditInitialOldPhysicalHilbertTotal hH3 (t + (q : ℝ)) =
      h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
        hShort.navier_stokes ht hEnd hTail q := by
  have hsShort : t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) S :=
    h3PreterminalElapsedTime_mem_Ioo ht hEnd q
  have hsT : t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) T :=
    ⟨hsShort.1, lt_of_lt_of_le hsShort.2 hST⟩
  apply PiLp.ext
  intro j
  change h3AuditActualPhysicalZeroJetL2Total hH3 j (t + (q : ℝ)) =
    h3PreterminalCanonicalL2JetOnElapsed
      hShort.navier_stokes ht hEnd hTail (h3JetSlot0 j) q
  rw [h3AuditActualPhysicalZeroJetL2Total_eq_at hH3 j _ hsT]
  rfl

/-- The endpoint-independent solenoidal scalar weak FTC on a canonical old
restart window gives the *actual* absolute-time weak FTC for the physical old
velocity and the correctly identified projected RHS. -/
theorem h3Audit_initialCanonicalWeakFTC_implies_absoluteSolenoidalWeakFTC
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
        hShort.navier_stokes ht hτ hEnd hTail) :
    H3AuditPhysicalSolenoidalWeakFTCOn
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (fun x : ℝ =>
        h3AuditInitialActualSpectralLaplacianTotal hH3 x -
          h3AuditInitialActualSpectralLerayTotal hH3 x)
      t (t + τ) := by
  intro φ hφ r hr
  let ψ : H3PhysicalRealFinVectorL2Hilbert :=
    h3WeakTestVectorPhysicalL2Hilbert φ
  have hqRange : r - t ∈ Set.Icc (0 : ℝ) τ := by
    constructor <;> linarith only [hr.1, hr.2]
  let q : Set.Icc (0 : ℝ) τ := ⟨r - t, hqRange⟩
  let q0 : Set.Icc (0 : ℝ) τ := ⟨0, le_rfl, hτ.le⟩
  have hTime : t + (q : ℝ) = r := by
    dsimp only [q]
    ring
  have hPhysicalR :=
    h3Audit_initialOldPhysicalHilbertTotal_eq_canonicalElapsed
      hH3 hShort hST ht hEnd hTail q
  have hPhysical0 :=
    h3Audit_initialOldPhysicalHilbertTotal_eq_canonicalElapsed
      hH3 hShort hST ht hEnd hTail q0
  have hIncrement :
      h3AuditInitialOldPhysicalHilbertTotal hH3 r -
        h3AuditInitialOldPhysicalHilbertTotal hH3 t =
      h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
        hShort.navier_stokes ht hτ hEnd hTail q := by
    rw [← hTime]
    simpa only [q0, add_zero,
      h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo]
      using congrArg₂ (· - ·) hPhysicalR hPhysical0
  have hScalarFTC := (hWeakFTC φ hφ q).2
  have hIdentIntegral :
      (∫ x in (0 : ℝ)..(q : ℝ),
        inner ℝ ψ
          (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
            hShort.navier_stokes ht hEnd hTail x)) =
      ∫ x in (0 : ℝ)..(q : ℝ),
        inner ℝ ψ
          (h3AuditInitialActualSpectralLaplacianTotal hH3 (t + x) -
            h3AuditInitialActualSpectralLerayTotal hH3 (t + x)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hxRange : x ∈ Set.Icc (0 : ℝ) τ := by
      rw [Set.uIcc_of_le q.property.1] at hx
      exact ⟨hx.1, hx.2.trans q.property.2⟩
    -- Expose the pointwise integrands before rewriting the elapsed RHS.
    -- `integral_congr` leaves both sides wrapped as `(fun x => ...) x`.
    change inner ℝ ψ
        (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
          hShort.navier_stokes ht hEnd hTail x) =
      inner ℝ ψ
        (h3AuditInitialActualSpectralLaplacianTotal hH3 (t + x) -
          h3AuditInitialActualSpectralLerayTotal hH3 (t + x))
    rw [h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal_apply_of_mem
      hShort.navier_stokes ht hEnd hTail hxRange]
    exact congrArg (inner ℝ ψ)
      ((h3Audit_initialActualSpectralProjectedRHS_eq_oldPhysicalOnElapsed
        hH3 hShort hST ht hEnd hTail ⟨x, hxRange⟩).symm)
  change inner ℝ ψ
      (h3AuditInitialOldPhysicalHilbertTotal hH3 r -
        h3AuditInitialOldPhysicalHilbertTotal hH3 t) =
    ∫ x in t..r,
      inner ℝ ψ
        (h3AuditInitialActualSpectralLaplacianTotal hH3 x -
          h3AuditInitialActualSpectralLerayTotal hH3 x)
  calc
    inner ℝ ψ
        (h3AuditInitialOldPhysicalHilbertTotal hH3 r -
          h3AuditInitialOldPhysicalHilbertTotal hH3 t) =
      inner ℝ ψ
        (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
          hShort.navier_stokes ht hτ hEnd hTail q) := by rw [hIncrement]
    _ = ∫ x in (0 : ℝ)..(q : ℝ),
          inner ℝ ψ
            (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
              hShort.navier_stokes ht hEnd hTail x) := hScalarFTC
    _ = ∫ x in (0 : ℝ)..(q : ℝ),
          inner ℝ ψ
            (h3AuditInitialActualSpectralLaplacianTotal hH3 (t + x) -
              h3AuditInitialActualSpectralLerayTotal hH3 (t + x)) := hIdentIntegral
    _ = ∫ x in t..r,
          inner ℝ ψ
            (h3AuditInitialActualSpectralLaplacianTotal hH3 x -
              h3AuditInitialActualSpectralLerayTotal hH3 x) := by
      let f : ℝ → ℝ := fun x =>
        inner ℝ ψ
          (h3AuditInitialActualSpectralLaplacianTotal hH3 x -
            h3AuditInitialActualSpectralLerayTotal hH3 x)
      have hShift := intervalIntegral.integral_comp_add_left f t
        (a := (0 : ℝ)) (b := (q : ℝ))
      simpa only [f, add_zero, hTime] using hShift

/-- Canonical old scalar weak FTC therefore closes the unrestricted actual
Schwartz pairing derivative at every *interior* physical time of that window. -/
theorem h3Audit_initialCanonicalWeakFTC_implies_SchwartzHasDerivAt_onElapsed
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
    (Φ : H3PhysicalRealFinVectorSchwartz)
    (s : ℝ) (hs : s ∈ Set.Ioo t (t + τ)) :
    HasDerivAt
      (fun x : ℝ =>
        ((innerSL ℝ) (h3AuditInitialOldPhysicalHilbertTotal hH3 x))
          (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ))
      (((innerSL ℝ)
        (h3AuditInitialActualSpectralLaplacianTotal hH3 s -
          h3AuditInitialActualSpectralLerayTotal hH3 s))
        (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ)) s := by
  have htT : 0 < t := ht.1
  have htτT : t + τ < T := lt_of_lt_of_le hEnd hST
  exact h3Audit_initialActualProjectedRHS_schwartzHasDerivAt_of_solenoidalWeakFTC
    hH3 t (t + τ) htT (lt_add_of_pos_right t hτ) htτT
    (h3Audit_initialCanonicalWeakFTC_implies_absoluteSolenoidalWeakFTC
      hH3 hShort hST ht hτ hEnd hTail hWeakFTC)
    Φ s hs

/-- Joint continuity of the actual old temporal derivative on the short
physical cylinder supplies its *previously established* old weak FTC, then
the full Schwartz derivative, without a new strong time derivative input. -/
theorem h3Audit_initialOldJoint_implies_SchwartzHasDerivAt_onElapsed
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
    (Φ : H3PhysicalRealFinVectorSchwartz)
    (s : ℝ) (hs : s ∈ Set.Ioo t (t + τ)) :
    HasDerivAt
      (fun x : ℝ =>
        ((innerSL ℝ) (h3AuditInitialOldPhysicalHilbertTotal hH3 x))
          (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ))
      (((innerSL ℝ)
        (h3AuditInitialActualSpectralLaplacianTotal hH3 s -
          h3AuditInitialActualSpectralLerayTotal hH3 s))
        (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ)) s := by
  have hWeakFTC :=
    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakFTCOnElapsed_of_oldTemporalDerivativeJointlyContinuous
      hShort.navier_stokes ht hτ hEnd hE hTail hOldJoint
  exact h3Audit_initialCanonicalWeakFTC_implies_SchwartzHasDerivAt_onElapsed
    hH3 hShort hST ht hτ hEnd hTail hWeakFTC Φ s hs

/-- The old temporal-derivative joint-continuity frontier on `(0,T)` closes
the full Schwartz momentum derivative at every positive preterminal time.
The joint-continuity frontier itself is **not** discharged here. -/
theorem h3Audit_initialOldJoint_implies_SchwartzHasDerivAt_at_positiveTime
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hOldJoint : H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous u T)
    (Φ : H3PhysicalRealFinVectorSchwartz)
    (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt
      (fun x : ℝ =>
        ((innerSL ℝ) (h3AuditInitialOldPhysicalHilbertTotal hH3 x))
          (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ))
      (((innerSL ℝ)
        (h3AuditInitialActualSpectralLaplacianTotal hH3 s -
          h3AuditInitialActualSpectralLerayTotal hH3 s))
        (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ)) s := by
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
  exact h3Audit_initialOldJoint_implies_SchwartzHasDerivAt_onElapsed
    hH3 hShort (le_of_lt hST) ht hτ hEnd hE hTail
    hOldJointShort Φ s hsInterior


/-- Initial actual physical comparison data with the *old temporal joint
continuity* substituted for a separately postulated Schwartz momentum
`HasDerivAt`. The initial H³ integral and relative-energy residual remain
explicit, independent data. -/
def H3AuditInitialCanonicalOldJointResidualData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) : Prop :=
  H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous u T ∧
  ∃ (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (hFourier0 : VelocityH3FourierCompatibleAt u 0 hInt0 hMeas0)
    (A : ℝ) (hA : 0 < A)
    (hU₀ : ‖velocityH3SpectralStateAt u 0 hInt0 hMeas0 hFourier0‖ ≤ A)
    (b : ℝ),
    0 < b ∧ b < T ∧
    b ≤ h3FinHeatLerayRestartRadius 1 A ∧
    IntervalIntegrable (velocityH3EnergyAt u) volume 0 b ∧
    ∃ K : ℝ,
      ∀ ε : ℝ, 0 < ε →
        ∃ (κ R : ℝ → ℝ),
          ContinuousOn κ (Set.Icc (0 : ℝ) b) ∧
          (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) b → κ s ≤ K) ∧
          IntervalIntegrable (fun s => |R s|) volume 0 b ∧
          (∫ s in (0 : ℝ)..b, |R s|) ≤ ε ∧
          ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) b →
            ‖h3AuditInitialCanonicalPhysicalDifference
              hH3 hFourier0 A hA hU₀ t‖ ^ 2 ≤
              (∫ s in (0 : ℝ)..t,
                κ s * ‖h3AuditInitialCanonicalPhysicalDifference
                  hH3 hFourier0 A hA hU₀ s‖ ^ 2) +
              (∫ s in (0 : ℝ)..t, |R s|)

/-- Joint old temporal continuity supplies the missing unrestricted
Schwartz derivative in the prior actual-spectral-source initial data. -/
theorem h3Audit_initialOldJointResidual_implies_actualSpectralSourcesData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalOldJointResidualData hH3) :
    H3AuditInitialCanonicalActualSpectralSourcesRelativeEnergyData hH3 := by
  obtain ⟨hOldJoint, hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, hE, K, hResidual⟩ := hData
  refine ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, hE, K, ?_, hResidual⟩
  intro Φ t ht
  exact h3Audit_initialOldJoint_implies_SchwartzHasDerivAt_at_positiveTime
    hH3 hOldJoint Φ t ⟨ht.1, lt_of_lt_of_le ht.2 hbT.le⟩

/-- The already-proved relative-energy route now accepts old temporal-joint
continuity in place of an explicit unrestricted physical Schwartz derivative.
The initial energy integral and residual are *not* proved by this implication. -/
theorem h3Audit_initialOldJointResidual_implies_compactWeakComparisonData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalOldJointResidualData hH3) :
    H3AuditInitialCanonicalCompactWeakComparisonData hH3 := by
  exact h3Audit_initialActualSpectralSources_implies_compactWeakComparisonData
    hH3 (h3Audit_initialOldJointResidual_implies_actualSpectralSourcesData hH3 hData)

/-- And the same assumptions produce the concrete physical zero-jet L² trace
and the H³ energy upper trace already obtained by the initial comparison chain. -/
theorem h3Audit_initialOldJointResidual_implies_physicalZeroJetAndEnergyUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalOldJointResidualData hH3) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  exact h3Audit_initialActualSpectralSources_implies_physicalZeroJetAndEnergyUpper
    hH3 (h3Audit_initialOldJointResidual_implies_actualSpectralSourcesData hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
