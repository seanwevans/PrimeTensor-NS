import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopWeakFTCSelectedUniqueness244
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Selected.Old.H3.Path.Admissible
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Spectral.State.Old.Bridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Initial.State
import Mathlib.Tactic

/-!
# Actual physical eighth moments on truncated local restart windows

`LoggedPreterminalH3PathAdmissible.exists_localCanonicalRestartWindowAt` supplies,
for every strict physical time `t`, an earlier anchor `t₀`, a shorter terminal
`S < T`, and a *local* bounded canonical H³ tail on `(t₀,S)`.

This is stronger and more appropriate geometrically than demanding a bound on
`(t₀,T)`: no terminal-uniform energy ceiling is required.  Put `q=t-t₀`.
The time `t` is exactly the positive endpoint of a half-slab with `Q=q`.

If the OLD branch has the scalar projected-RHS weak FTC on `[0,q]`, the existing
L² relative-energy Grönwall argument identifies its physical solution with
the selected mild restart.  The existing spectral overlap theorem then
transfers ALL finite raw Fourier moments from the selected state to the actual
physical slice.  This is an actual truncated-time proof, not an axiom that
some selected state equals the physical state.

We do not assert that the scalar weak FTC follows from bare H³ admissibility.
The old-pressure/global weak-FTC frontiers are explicit sufficient conditions.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval

noncomputable section

noncomputable local instance axisFintypeH3LocalShortRestartEighthMoments244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 2600000

/-- Every strict physical time has an earlier local restart anchor whose
canonical energy bound is needed only up to a shorter endpoint `S < T`.
The chosen elapsed time is positive and strictly within the restart radius. -/
theorem h3Path_exists_localShortRestartGeometry244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    ∃ (t₀ S E : ℝ),
      t₀ ∈ Set.Ioo (0 : ℝ) S ∧
      S < T ∧
      1 ≤ E ∧
      CanonicalH3TailDataFrom u t₀ S E ∧
      0 < t - t₀ ∧
      t - t₀ < h3FinHeatLerayRestartRadius (1 : ℝ) E ∧
      t₀ + (t - t₀) < S := by
  rcases hH3.exists_localCanonicalRestartWindowAt ht with
    ⟨t₀, S, E, ht₀, hST, hE, hTail, hq, hqR, hTime, htS⟩
  refine ⟨t₀, S, E, ht₀, hST, hE, hTail, hq, hqR, ?_⟩
  rw [hTime]
  exact htS

/-- The only additional analytic hypothesis at one physical slice: a
strictly *local* canonical restart window supports scalar projected-RHS
weak FTC on its selected elapsed interval `[0,t-t₀]`. -/
def h3PathVelocityShortWindowWeakFTCAt244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (_hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) : Prop :=
  ∃ (t₀ S E : ℝ)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) S)
    (_hST : S < T)
    (_hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ S E)
    (hq : 0 < t - t₀)
    (_hqR : t - t₀ < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hEnd : t₀ + (t - t₀) < S)
    (hNSShort : LoggedPreterminalNavierStokesAdmissible u S),
    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakFTCOnElapsed
      hNSShort ht₀ hq hEnd hTail

/-- A single scalar weak-FTC interval on the SHORT old physical path
produces the actual order-eight Fourier moment of every physical velocity
coordinate at the target time, using local Grönwall and exact H³ spectral
snapshot identification. -/
theorem h3Path_physicalEighthMoments_of_shortWindowWeakFTC244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t t₀ S E : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hNSShort : LoggedPreterminalNavierStokesAdmissible u S)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) S)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ S E)
    (hq : 0 < t - t₀)
    (hqR : t - t₀ < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hEnd : t₀ + (t - t₀) < S)
    (hWeakFTC :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakFTCOnElapsed
        hNSShort ht₀ hq hEnd hTail) :
    h3PathVelocityRawEightMomentsAt244 hH3 hClass ht := by
  let q : ℝ := t - t₀
  have hqPos : 0 < q := hq
  have hqR' : q < h3FinHeatLerayRestartRadius (1 : ℝ) E := hqR
  let qClosed : Set.Icc (0 : ℝ) q := ⟨q, hqPos.le, le_rfl⟩
  have hAgree :
      H3PreterminalSelectedPhysicalAgreementAt
        (one_pos : (0 : ℝ) < 1) q hNSShort ht₀ hE hTail :=
    h3PreterminalSelectedPhysicalAgreementAt_of_allProjectedRHSWeakFTC
      (tau := q) (q := q)
      hNSShort ht₀ hqPos hEnd hE hTail hqR'.le hWeakFTC
      ⟨hqPos, le_rfl⟩
  have hSelectedOld :=
    h3PreterminalSelectedUnitSpectralStateOnRadius_eq_tailCanonical_of_physicalAgreement
      hNSShort ht₀ hEnd hE hTail hqR'.le qClosed hqPos hAgree
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  have hPhysicalOld :
      h3TerminalVelocitySpectralStateAt hH3 t htAbs =
      h3PreterminalTailCanonicalSpectralStateOnElapsed
        hNSShort ht₀ hEnd hTail qClosed := by
    have hTime : t = t₀ + (qClosed : ℝ) := by
      dsimp only [qClosed, q]
      ring
    unfold h3TerminalVelocitySpectralStateAt
    unfold h3PreterminalTailCanonicalSpectralStateOnElapsed
    exact velocityH3SpectralStateAt_eq_of_time_eq u hTime
      _ _ _ _ _ _
  let s : Set.Icc (q / 2) q :=
    ⟨q, (by linarith only [hqPos]), le_rfl⟩
  have hRadius :
      h3PreterminalElapsedToSelectedUnitRadius hqR'.le qClosed =
      h3SelectedProjectedRHSSlabRadius hE hqPos hqR' s := by
    apply Subtype.ext
    rfl
  have hEq :
      h3TerminalVelocitySpectralStateAt hH3 t htAbs =
      h3PreterminalSelectedUnitSpectralStateOnRadius
        hNSShort ht₀ hE hTail
        (h3SelectedProjectedRHSSlabRadius hE hqPos hqR' s) := by
    calc
      h3TerminalVelocitySpectralStateAt hH3 t htAbs =
          h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNSShort ht₀ hEnd hTail qClosed := hPhysicalOld
      _ = h3PreterminalSelectedUnitSpectralStateOnRadius
            hNSShort ht₀ hE hTail
            (h3PreterminalElapsedToSelectedUnitRadius hqR'.le qClosed) :=
          hSelectedOld.symm
      _ = h3PreterminalSelectedUnitSpectralStateOnRadius
            hNSShort ht₀ hE hTail
            (h3SelectedProjectedRHSSlabRadius hE hqPos hqR' s) := by
          rw [hRadius]
  change ∀ k : Fin 3,
    H3RawFourierMomentIntegrable (8 : ℝ)
      (h3TerminalVelocitySpectralStateAt hH3 t htAbs k)
  intro k
  rw [hEq]
  exact h3PreterminalSelectedUnitSpectralStateOnSlab_natMoment_integrable
    8 hNSShort ht₀ hE hTail hqPos hqR' s k

/-- The actual eighth-moment conclusion needs only the existence of one
suitable local scalar-FTC window, NOT a uniform energy bound up to T. -/
theorem h3Path_physicalEighthMoments_of_localShortWeakFTC244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hLocal : h3PathVelocityShortWindowWeakFTCAt244 hH3 t) :
    h3PathVelocityRawEightMomentsAt244 hH3 hClass ht := by
  rcases hLocal with
    ⟨t₀, S, E, ht₀, _hST, hE, hTail, hq, hqR, hEnd,
      hNSShort, hWeakFTC⟩
  exact h3Path_physicalEighthMoments_of_shortWindowWeakFTC244
    hH3 hClass ht hNSShort ht₀ hE hTail hq hqR hEnd hWeakFTC

/-- The existing GLOBAL weak-FTC frontier supplies the only analytic
condition on the *local* restart interval furnished automatically by H³
path admissibility.  The frontier is applied to the truncated time `S`,
not to an incorrectly assumed uniformly bounded `(t₀,T)` tail. -/
theorem h3Path_localShortWeakFTC_of_globalWeakFTC244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hGlobal : H3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontier) :
    h3PathVelocityShortWindowWeakFTCAt244 hH3 t := by
  rcases h3Path_exists_localShortRestartGeometry244 hH3 ht with
    ⟨t₀, S, E, ht₀, hST, hE, hTail, hq, hqR, hEnd⟩
  have hSPos : 0 < S := lt_trans ht₀.1 ht₀.2
  let hNSShort : LoggedPreterminalNavierStokesAdmissible u S :=
    loggedPreterminalNavierStokesAdmissible_mono_terminal
      hH3.navier_stokes hSPos hST.le
  let qClosed : Set.Icc (0 : ℝ)
      (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
    ⟨t - t₀, hq.le, hqR.le⟩
  have hLocal :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakFTCOnElapsed
        hNSShort ht₀ hq hEnd hTail :=
    (hGlobal E hE u S t₀ hNSShort ht₀ hTail) qClosed hq hEnd
  exact ⟨t₀, S, E, ht₀, hST, hE, hTail, hq, hqR, hEnd,
    hNSShort, hLocal⟩

/-- Global weak FTC gives pointwise raw Fourier eighth moments at EVERY
strict physical time, without any terminal-uniform canonical tail or any
independently postulated selected/old spectral equality. -/
theorem h3Path_physicalEighthMoments_of_globalWeakFTC_noGeometry244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hGlobal : H3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontier) :
    h3PathVelocityRawEightMomentsAt244 hH3 hClass ht := by
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  exact h3Path_physicalEighthMoments_of_localShortWeakFTC244
    hH3 hClass ht
    (h3Path_localShortWeakFTC_of_globalWeakFTC244 hH3 htAbs hGlobal)

/-- The physical terminal alternative under LOCAL shortened-interval scalar
weak-FTC coverage needs no extra restart geometry assumption. -/
theorem h3Path_unboundedPhysicalTop_forces_dissipationOne_or_eightMoment_of_localShortWeakFTC244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (hEscape : ∀ M : ℝ, ∃ t, t ∈ Set.Ioo s T ∧
      M < velocityH3Dissipation3At u t)
    (hLocal : ∀ t (_ht : t ∈ Set.Ioo a T),
      h3PathVelocityShortWindowWeakFTCAt244 hH3 t) :
    (∀ K : ℝ, ∃ r, r ∈ Set.Ioo s T ∧
      K < velocityH3Dissipation1At u r) ∨
    (∀ σ, σ ∈ Set.Ioo s T → ∀ K : ℝ,
      ∃ r, r ∈ Set.Ioo σ T ∧ ∃ j : Fin 3,
        K < h3PathVelocityRawEightMomentComponent244 hH3 hClass j r) := by
  apply h3Path_unboundedPhysicalTop_forces_dissipationOne_or_eightMoment_noRep244
    hH3 hClass hs hEscape
  intro t ht
  exact h3Path_physicalEighthMoments_of_localShortWeakFTC244
    hH3 hClass ht (hLocal t ht)

/-- The global projected-RHS scalar weak FTC now closes the high-moment
premise WITHOUT the former erroneous demand for a canonical H³ tail
uniformly bounded all the way to the terminal time. -/
theorem h3Path_unboundedPhysicalTop_forces_dissipationOne_or_eightMoment_of_globalWeakFTC_noGeometry244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (hEscape : ∀ M : ℝ, ∃ t, t ∈ Set.Ioo s T ∧
      M < velocityH3Dissipation3At u t)
    (hGlobal : H3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontier) :
    (∀ K : ℝ, ∃ r, r ∈ Set.Ioo s T ∧
      K < velocityH3Dissipation1At u r) ∨
    (∀ σ, σ ∈ Set.Ioo s T → ∀ K : ℝ,
      ∃ r, r ∈ Set.Ioo σ T ∧ ∃ j : Fin 3,
        K < h3PathVelocityRawEightMomentComponent244 hH3 hClass j r) := by
  apply h3Path_unboundedPhysicalTop_forces_dissipationOne_or_eightMoment_noRep244
    hH3 hClass hs hEscape
  intro t ht
  exact h3Path_physicalEighthMoments_of_globalWeakFTC_noGeometry244
    hH3 hClass ht hGlobal

end
end PrimeTensor.FirstMonomialTriad
