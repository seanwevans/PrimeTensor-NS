import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfilePrescribedGaugeLateViscousSecondaryHighRadialSlices
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileAnnularPersistence
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessEndpointViscousAnnularPDEPersistence
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessAttainedPhysicalPDEFactorGate
import Mathlib.Tactic

/-!
# A real PDE persistence clock for the selected secondary high-radial H³ spikes

The existing residual two-clock theorem forces high-radial dissipation at one
of two prescribed secondary physical times, but a pointwise spike alone costs
no definite terminal dissipation. Here the exact Fourier partition first
captures a fixed-radius high tail in a FINITE annulus at that SAME time.
The actual source/spectral maxima on a compact future interval then provide
the genuine physical PDE annular variation coefficient. The resulting right
clock has an explicit solution-dependent min-width, persistent annular floor,
and a real terminal viscous integral charge. Its new source/state maximizers
are rate coefficients; the old secondary observations are not reselected.
No terminal-uniform rate, outer cutoff or persistence width is asserted.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- Quantitative ANNULAR persistence at one of the original selected high-radial
observation times. The outer cutoff and compact-window maxima are chosen
only after the original time and lower cutoff are fixed. -/
def ThirdFullSecondaryHighRadialAnnularPDECharge244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (m x σ M : ℝ) : Prop :=
  ∃ (N : ℕ) (qSource qState δ : ℝ),
    qSource ∈ Set.Icc x (x + (T - x) / 2) ∧
    qState ∈ Set.Icc x (x + (T - x) / 2) ∧
    (∀ r : ℝ, r ∈ Set.Icc x (x + (T - x) / 2) →
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤
        ‖h3PathActualProjectedMomentumSource244 hH3 qSource‖ ∧
      ‖h3AuditActualSpectralVelocityTotal hH3 r‖ ≤
        ‖h3AuditActualSpectralVelocityTotal hH3 qState‖) ∧
    0 < δ ∧
    δ = min (((T - x) / 2) / 2)
      ((M / 2) /
        (2 * (h3PathFiniteAnnulusPDEVariationCoefficient244
          σ ((N : ℝ) + 1)
          ‖h3AuditActualSpectralVelocityTotal hH3 qState‖
          ‖h3PathActualProjectedMomentumSource244 hH3 qSource‖ + 1))) ∧
    x + δ < T ∧
    (∀ r : ℝ, r ∈ Set.Icc x (x + δ) →
      M / 2 <
        h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 r) -
        h3PathActualLowRadialDissipation244 σ
          (h3AuditActualSpectralVelocityTotal hH3 r) ∧
      h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 r) -
        h3PathActualLowRadialDissipation244 σ
          (h3AuditActualSpectralVelocityTotal hH3 r) ≤
        velocityH3DissipationAt u r) ∧
    δ * (M / 2) ≤ ∫ r in m..T, velocityH3DissipationAt u r ∂volume

/-- FINITE radial capture + exact physical Navier--Stokes annular variation:
if 2M < D_high,σ(x), a positive, explicitly selected PDE clock retains
at least M/2 of true annular dissipation and charges that same terminal tail.
This is much stronger than merely choosing an unknown continuity radius. -/
theorem thirdFullPhysical_secondaryHighRadialSpike_annularPDECharge244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (m x σ M : ℝ) (hm : m ∈ Set.Ioo a T)
    (hx : x ∈ Set.Ioo m T) (hσ : 0 ≤ σ) (hM : 0 < M)
    (hHigh : 2 * M < h3PathActualHighRadialDissipation244 σ
      (h3AuditActualSpectralVelocityTotal hH3 x)) :
    ThirdFullSecondaryHighRadialAnnularPDECharge244 hH3 m x σ M := by
  let U : ℝ → H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3
  let d : ℝ := (T - x) / 2
  have hxClass : x ∈ Set.Ioo a T := ⟨lt_trans hm.1 hx.1, hx.2⟩
  have hx0 : 0 < x := lt_trans hClass.terminal_start.1 hxClass.1
  have hd : 0 < d := by dsimp only [d]; linarith only [hx.2]
  have hEnd : x + d < T := by dsimp only [d]; linarith only [hx.2]
  have hQuarter : 0 < M / 2 := by linarith only [hM]
  have hTail := h3Path_actualHighRadialDissipation_tendsto_zero_fixedTime244
    hH3 hClass x hxClass
  have hEvent : ∀ᶠ N : ℕ in atTop,
      h3PathActualHighRadialDissipation244 ((N : ℝ) + 1) (U x) < M / 2 :=
    hTail.eventually (eventually_lt_nhds hQuarter)
  rw [Filter.eventually_atTop] at hEvent
  obtain ⟨N0, hN0⟩ := hEvent
  let N : ℕ := N0
  let Q : ℝ := (N : ℝ) + 1
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hOuter : h3PathActualHighRadialDissipation244 Q (U x) < M / 2 := by
    exact hN0 N le_rfl
  have hPartσ := h3Path_actualRadialDissipation_partition244
    hH3 hClass x hxClass σ
  have hPartQ := h3Path_actualRadialDissipation_partition244
    hH3 hClass x hxClass Q
  have hPeak : M <
      h3PathActualLowRadialDissipation244 Q (U x) -
      h3PathActualLowRadialDissipation244 σ (U x) := by
    dsimp only [U] at hHigh hOuter hPartσ hPartQ ⊢
    linarith only [hHigh, hOuter, hPartσ, hPartQ, hM]
  obtain ⟨qSource, qState, hqSource, hqState, hMax⟩ :=
    h3Critical_actualSourceSpectral_attainedCompactMaxima
      hH3 x d hx0 hd hEnd
  let C : ℝ := ‖h3PathActualProjectedMomentumSource244 hH3 qSource‖
  let K : ℝ := ‖U qState‖
  have hK : 0 ≤ K := norm_nonneg _
  have hEnvelope : ∀ r : ℝ, r ∈ Set.Icc x (x + d) →
      ∀ j : Fin 3, ‖(U r) j‖ ≤ K := by
    intro r hr j
    exact (norm_le_pi_norm (U r) j).trans (hMax r hr).2
  have hSource : ∀ r : ℝ, r ∈ Set.Icc x (x + d) →
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤ C := by
    intro r hr
    exact (hMax r hr).1
  have hPeak' : 2 * (M / 2) <
      h3PathActualLowRadialDissipation244 Q (U x) -
      h3PathActualLowRadialDissipation244 σ (U x) := by
    linarith only [hPeak]
  obtain ⟨δ, hδ, _hδHalf, hδEq, hδEnd, hFloor, hCost⟩ :=
    h3Critical_physicalAnnulus_PDEControlledPositiveRightWindow
      hH3 hClass σ Q K C (M / 2) x d hσ hQ hK hQuarter
      hxClass hd hEnd hEnvelope hSource
      (by simpa only [U] using hPeak')
  let D : ℝ → ℝ := velocityH3DissipationAt u
  let Ann : ℝ → ℝ := fun r =>
    h3PathActualLowRadialDissipation244 Q (U r) -
      h3PathActualLowRadialDissipation244 σ (U r)
  have hDtail : IntervalIntegrable D volume m T := by
    apply hDInt.mono_set
    intro r hr
    have hrIcc : r ∈ Set.Icc m T := by
      simpa only [Set.uIcc_of_le hm.2.le] using hr
    have hrAll : r ∈ Set.Icc a T :=
      ⟨hm.1.le.trans hrIcc.1, hrIcc.2⟩
    simpa only [Set.uIcc_of_le hClass.terminal_start.2.le] using hrAll
  have hDwindow : IntervalIntegrable D volume x (x + δ) := by
    apply hDInt.mono_set
    intro r hr
    have hrIcc : r ∈ Set.Icc x (x + δ) := by
      simpa only [Set.uIcc_of_le (le_add_of_nonneg_right hδ.le)] using hr
    have hrAll : r ∈ Set.Icc a T :=
      ⟨hxClass.1.le.trans hrIcc.1, hrIcc.2.trans hδEnd.le⟩
    simpa only [Set.uIcc_of_le hClass.terminal_start.2.le] using hrAll
  have hSub : Set.Icc x (x + δ) ⊆ Set.Ioo a T := by
    intro r hr
    exact ⟨lt_of_lt_of_le hxClass.1 hr.1, lt_of_le_of_lt hr.2 hδEnd⟩
  have hAnnInt : IntervalIntegrable Ann volume x (x + δ) := by
    have hCont : ContinuousOn Ann (Set.Ioo a T) := by
      exact h3Path_finiteAnnularDissipation_continuousOn244
        hH3 hClass σ Q hσ hQ
    exact (hCont.mono hSub).intervalIntegrable_of_Icc
      (by linarith only [hδ])
  have hAnnLeD : (∫ r in x..(x + δ), Ann r ∂volume) ≤
      ∫ r in x..(x + δ), D r ∂volume := by
    apply intervalIntegral.integral_mono_on
      (le_add_of_nonneg_right hδ.le) hAnnInt hDwindow
    intro r hr
    exact (hFloor r hr).2
  have hNonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc m T)] D := by
    filter_upwards [] with r
    exact velocityH3DissipationAt_nonneg u r
  have hWindowTail : (∫ r in x..(x + δ), D r ∂volume) ≤
      ∫ r in m..T, D r ∂volume :=
    intervalIntegral.integral_mono_interval
      hx.1.le (le_add_of_nonneg_right hδ.le) hδEnd.le hNonneg hDtail
  have hTailCost : δ * (M / 2) ≤
      ∫ r in m..T, D r ∂volume := by
    calc
      δ * (M / 2) ≤ ∫ r in x..(x + δ), Ann r ∂volume := by
        simpa only [Ann, U, Q] using hCost
      _ ≤ ∫ r in x..(x + δ), D r ∂volume := hAnnLeD
      _ ≤ ∫ r in m..T, D r ∂volume := hWindowTail
  unfold ThirdFullSecondaryHighRadialAnnularPDECharge244
  refine ⟨N, qSource, qState, δ, ?_, ?_, ?_, hδ, ?_, hδEnd, ?_, ?_⟩
  · simpa only [d] using hqSource
  · simpa only [d] using hqState
  · intro r hr
    have hr' : r ∈ Set.Icc x (x + d) := by
      simpa only [d] using hr
    exact hMax r hr'
  · simpa only [d, Q, K, C, U] using hδEq
  · intro r hr
    simpa only [Ann, Q, U] using hFloor r hr
  · exact hTailCost

/-- On the ORIGINAL two attained secondary state/source times, a large
noncompressed squared-height demand forces an actual, quantitatively
PDE-persistent finite annulus at ONE of those SAME times. A new maximum on
the chosen forward window only supplies the variation RATE, not a new spike. -/
theorem thirdFullPhysical_secondaryTwoSlice_forcesAnnularPDECharge244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (m zState zSource A R B S M s σ : ℝ)
    (hm : m ∈ Set.Ioo b T)
    (hzState : zState ∈ Set.Ioo m T)
    (hzSource : zSource ∈ Set.Ioo m T)
    (hR : 0 ≤ R) (hB : 0 ≤ B) (hS : 0 ≤ S)
    (hσ : 0 ≤ σ) (hM : 0 < M)
    (hWide : 192 * B * Real.sqrt (R * B) < (T - s) * A)
    (hDemand : 576 * R * B ^ 2 *
      (96 * (3 + h3AuditInitialLerayEnergyCoefficient) *
        (1 + 6 * velocityH3Energy0At u b + 3 *
          (σ ^ 2 * (h3TerminalRadialSobolevWeightSquareCeiling σ *
            velocityH3Energy0At u b) + 2 * M)) ^ 2 * S + 4) < A ^ 2)
    (hGate : (T - s) * A ≤ 192 * B * Real.sqrt (R * B) ∨
      A ^ 2 ≤ 576 * R * B ^ 2 *
        (96 * (1 + 6 * velocityH3Energy0At u b +
            3 * velocityH3DissipationAt u zState) *
          ((3 + h3AuditInitialLerayEnergyCoefficient) *
            (1 + 6 * velocityH3Energy0At u b +
              3 * velocityH3DissipationAt u zSource)) * S + 4)) :
    ∃ x : ℝ, (x = zState ∨ x = zSource) ∧
      ThirdFullSecondaryHighRadialAnnularPDECharge244 hH3 m x σ M := by
  have hHigh := thirdFullPhysical_secondaryTwoSlice_forcesHighRadial244
    hH3 hClass b hb zState zSource A R B S (2 * M) s σ
    ⟨lt_trans hm.1 hzState.1, hzState.2⟩
    ⟨lt_trans hm.1 hzSource.1, hzSource.2⟩
    hR hB hS hσ hWide hDemand hGate
  have hmAll : m ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hm.1, hm.2⟩
  rcases hHigh with hState | hSource
  · exact ⟨zState, Or.inl rfl,
      thirdFullPhysical_secondaryHighRadialSpike_annularPDECharge244
        hH3 hClass hDInt m zState σ M hmAll hzState hσ hM hState⟩
  · exact ⟨zSource, Or.inr rfl,
      thirdFullPhysical_secondaryHighRadialSpike_annularPDECharge244
        hH3 hClass hDInt m zSource σ M hmAll hzSource hσ hM hSource⟩

end
end PrimeTensor.FirstMonomialTriad
