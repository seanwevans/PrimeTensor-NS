import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticAnnularDissipationRate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfilePrescribedGaugeLateViscousSecondaryAnnularClockRate
import Mathlib.Tactic

/-!
# Selected secondary high-radial spikes: kinetic annular charge and cutoff escape

The earlier cofinal ledger fixes the two physical source/state observation
slices before an arbitrarily chosen lower frequency and height. A spike
above 2M at natural lower cutoff n+1 can be captured in a finite outer
annulus [n+1,N+1) AT THAT SAME observation time, via fixed-time radial
high-tail decay and the exact physical Fourier dissipation partition.

The compiled kinetic-only finite-annulus PDE persistence theorem then gives
an explicit terminal viscous charge at a rate depending on the actual
kinetic anchor and the two finite frequency cutoffs, not attained full-H3
source/state maxima. The same midpoint geometry yields a clock-compression
or genuine kinetic frequency-rate alternative. A finite-sum rate bound at
any proposed outer cutoff converts the second branch into outer frequency
escape when the actual terminal viscous budget is sufficiently small.

No fresh secondary observation time is selected; no overlapping annular
windows are summed. This is a necessary frequency-growth alternative,
not a terminal-uniform cutoff bound or a global continuation proof.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- A natural annular physical kinetic-rate certificate at an already
selected secondary time. Its outer cutoff and width may depend on n,M;
the previously selected time x does not. -/
def ThirdFullSecondaryNaturalKineticAnnularCharge244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b m s x : ℝ) (n : ℕ) (M : ℝ) : Prop :=
  ∃ (N : ℕ) (δ : ℝ),
    0 < δ ∧
    δ = min ((T - x) / 4)
      ((M / 2) /
        (2 * (thirdFullPhysicalKineticLowBandDissipationRate244 N
                (velocityH3Energy0At u b) +
              thirdFullPhysicalKineticLowBandDissipationRate244 n
                (velocityH3Energy0At u b) + 1))) ∧
    x + δ < T ∧
    (∀ r : ℝ, r ∈ Set.Icc x (x + δ) →
      M / 2 <
        h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 r) -
        h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 r) ∧
      h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 r) -
        h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 r) ≤
        velocityH3DissipationAt u r) ∧
    δ * (M / 2) ≤
      (∫ r in m..T, velocityH3DissipationAt u r ∂volume) ∧
    ((T - s) * M ≤
        16 * (∫ r in m..T, velocityH3DissipationAt u r ∂volume) ∨
     M ^ 2 ≤ 8 *
        (thirdFullPhysicalKineticLowBandDissipationRate244 N
            (velocityH3Energy0At u b) +
         thirdFullPhysicalKineticLowBandDissipationRate244 n
            (velocityH3Energy0At u b) + 1) *
        (∫ r in m..T, velocityH3DissipationAt u r ∂volume))

/-- The true original high-radial spike yields a finite natural annulus
whose persistence coefficient depends ONLY on kinetic energy and finite
frequency cutoffs. The physical terminal integral pays for the width. -/
theorem thirdFullPhysical_secondaryHighRadialSpike_kineticAnnularCharge244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (m s x : ℝ) (n : ℕ) (M : ℝ)
    (hm : m ∈ Set.Ioo b T) (hx : x ∈ Set.Ioo m T)
    (hxMid : x ∈ Set.Icc s (s + (T - s) / 2))
    (hM : 0 < M)
    (hHigh : 2 * M < h3PathActualHighRadialDissipation244
      ((n : ℝ) + 1) (h3AuditActualSpectralVelocityTotal hH3 x)) :
    ThirdFullSecondaryNaturalKineticAnnularCharge244
      hH3 b m s x n M := by
  let U : ℝ → H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3
  have hxClass : x ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 (lt_trans hm.1 hx.1), hx.2⟩
  have hHalf : 0 < M / 2 := by linarith only [hM]
  have hTail := h3Path_actualHighRadialDissipation_tendsto_zero_fixedTime244
    hH3 hClass x hxClass
  have hEvent : ∀ᶠ N : ℕ in atTop,
      h3PathActualHighRadialDissipation244 ((N : ℝ) + 1) (U x) < M / 2 :=
    hTail.eventually (eventually_lt_nhds hHalf)
  rw [Filter.eventually_atTop] at hEvent
  obtain ⟨N, hN⟩ := hEvent
  have hOuter :
      h3PathActualHighRadialDissipation244 ((N : ℝ) + 1) (U x) < M / 2 :=
    hN N le_rfl
  have hPartInner := h3Path_actualRadialDissipation_partition244
    hH3 hClass x hxClass ((n : ℝ) + 1)
  have hPartOuter := h3Path_actualRadialDissipation_partition244
    hH3 hClass x hxClass ((N : ℝ) + 1)
  have hPeak : M <
      h3PathActualLowRadialDissipation244 ((N : ℝ) + 1) (U x) -
      h3PathActualLowRadialDissipation244 ((n : ℝ) + 1) (U x) := by
    dsimp only [U] at hHigh hOuter hPartInner hPartOuter ⊢
    linarith only [hHigh, hOuter, hPartInner, hPartOuter, hM]
  have hPeak' : 2 * (M / 2) <
      h3PathActualLowRadialDissipation244 ((N : ℝ) + 1) (U x) -
      h3PathActualLowRadialDissipation244 ((n : ℝ) + 1) (U x) := by
    linarith only [hPeak]
  obtain ⟨δ, hδ, hδEq, hδEnd, hFloor, hCost⟩ :=
    thirdFullPhysical_kineticNaturalAnnularRightTailCharge244
      hH3 hClass hDInt b hb m x hm hx n N (M / 2) hHalf
      (by simpa only [U] using hPeak')
  let Λ : ℝ :=
    thirdFullPhysicalKineticLowBandDissipationRate244 N
      (velocityH3Energy0At u b) +
    thirdFullPhysicalKineticLowBandDissipationRate244 n
      (velocityH3Energy0At u b)
  have hΛ : 0 ≤ Λ := add_nonneg
    (thirdFullPhysicalKineticLowBandDissipationRate_nonneg244 N _)
    (thirdFullPhysicalKineticLowBandDissipationRate_nonneg244 n _)
  have hQuarter : ((T - x) / 2) / 2 = (T - x) / 4 := by ring
  have hWidth : δ = min (((T - x) / 2) / 2)
      ((M / 2) / (2 * (Λ + 1))) := by
    rw [hQuarter]
    simpa only [Λ] using hδEq
  have hFork := thirdFull_scalar_secondaryAnnularClockOrRate244
    T s x M Λ δ
    (∫ r in m..T, velocityH3DissipationAt u r ∂volume)
    hM hΛ hxMid hWidth hCost
  unfold ThirdFullSecondaryNaturalKineticAnnularCharge244
  refine ⟨N, δ, hδ, ?_, hδEnd, ?_, hCost, ?_⟩
  · simpa only [Λ] using hδEq
  · intro r hr
    simpa only [U] using hFloor r hr
  · simpa only [Λ] using hFork

/-- An ORIGINAL secondary state/source observation (no new observation
selection) inherits the natural finite-annulus kinetic PDE certificate. -/
theorem thirdFullPhysical_secondaryTwoSlice_forcesKineticAnnularCharge244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (m s zState zSource : ℝ) (n : ℕ) (M : ℝ)
    (hm : m ∈ Set.Ioo b T)
    (hzState : zState ∈ Set.Ioo m T)
    (hzSource : zSource ∈ Set.Ioo m T)
    (hzMidState : zState ∈ Set.Icc s (s + (T - s) / 2))
    (hzMidSource : zSource ∈ Set.Icc s (s + (T - s) / 2))
    (hM : 0 < M)
    (hHigh : 2 * M < h3PathActualHighRadialDissipation244
        ((n : ℝ) + 1) (h3AuditActualSpectralVelocityTotal hH3 zState) ∨
      2 * M < h3PathActualHighRadialDissipation244
        ((n : ℝ) + 1) (h3AuditActualSpectralVelocityTotal hH3 zSource)) :
    ∃ x : ℝ, (x = zState ∨ x = zSource) ∧
      ThirdFullSecondaryNaturalKineticAnnularCharge244 hH3 b m s x n M := by
  rcases hHigh with hState | hSource
  · exact ⟨zState, Or.inl rfl,
      thirdFullPhysical_secondaryHighRadialSpike_kineticAnnularCharge244
        hH3 hClass hDInt b hb m s zState n M
        hm hzState hzMidState hM hState⟩
  · exact ⟨zSource, Or.inr rfl,
      thirdFullPhysical_secondaryHighRadialSpike_kineticAnnularCharge244
        hH3 hClass hDInt b hb m s zSource n M
        hm hzSource hzMidSource hM hSource⟩

/-- Every bounded set of finite natural cutoffs has a single explicit
kinetic rate ceiling: the finite sum of their nonnegative PDE rates.
Consequently a genuine rate-branch spike with sufficiently small terminal
viscous budget must have an outer cutoff ABOVE any proposed n0. -/
theorem thirdFull_scalar_kineticAnnularRate_forces_outerCutoffEscape244
    (L : ℕ → ℝ) (n N n0 : ℕ) (M B : ℝ)
    (hL : ∀ j : ℕ, 0 ≤ L j) (hB : 0 ≤ B)
    (hFast : M ^ 2 ≤ 8 * (L N + L n + 1) * B)
    (hSmall : 8 *
      ((∑ j ∈ Finset.range (n0 + 1), L j) + L n + 1) * B < M ^ 2) :
    n0 < N := by
  by_contra hNot
  have hN : N ≤ n0 := Nat.le_of_not_gt hNot
  have hMem : N ∈ Finset.range (n0 + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le hN)
  have hSum : L N ≤ ∑ j ∈ Finset.range (n0 + 1), L j := by
    exact Finset.single_le_sum (fun j _ => hL j) hMem
  have hUpper : 8 * (L N + L n + 1) * B ≤
      8 * ((∑ j ∈ Finset.range (n0 + 1), L j) + L n + 1) * B := by
    apply mul_le_mul_of_nonneg_right _ hB
    have hAux : L N + L n + 1 ≤
        (∑ j ∈ Finset.range (n0 + 1), L j) + L n + 1 := by
      linarith only [hSum]
    exact mul_le_mul_of_nonneg_left hAux (by norm_num)
  have hImpossible : M ^ 2 < M ^ 2 :=
    lt_of_le_of_lt (le_trans hFast hUpper) hSmall
  exact (lt_irrefl _) hImpossible

/-- The physical annulus must escape any fixed outer cutoff whenever its
certified clock cannot compress and its actual terminal dissipation is below
the finite-frequency kinetic-rate cost. There is no full-H3 source ceiling. -/
theorem thirdFullPhysical_secondaryKineticAnnularCharge_outerCutoffEscape244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b m s x : ℝ) (n n0 : ℕ) (M : ℝ) (hM : 0 < M)
    (hCharge : ThirdFullSecondaryNaturalKineticAnnularCharge244
      hH3 b m s x n M)
    (hClock : 16 * (∫ r in m..T, velocityH3DissipationAt u r ∂volume) <
      (T - s) * M)
    (hSmall : 8 *
      ((∑ j ∈ Finset.range (n0 + 1),
          thirdFullPhysicalKineticLowBandDissipationRate244 j
            (velocityH3Energy0At u b)) +
        thirdFullPhysicalKineticLowBandDissipationRate244 n
          (velocityH3Energy0At u b) + 1) *
        (∫ r in m..T, velocityH3DissipationAt u r ∂volume) < M ^ 2) :
    ∃ N : ℕ, n0 < N := by
  obtain ⟨N, δ, hδ, hδEq, hEnd, hFloor, hCost, hFork⟩ := hCharge
  have hB : 0 ≤ (∫ r in m..T, velocityH3DissipationAt u r ∂volume) := by
    have hHalf : 0 ≤ M / 2 := by linarith only [hM]
    exact (mul_nonneg hδ.le hHalf).trans hCost
  rcases hFork with hCompressed | hAmplified
  · have hImpossible : (T - s) * M < (T - s) * M :=
      lt_of_le_of_lt hCompressed hClock
    exact False.elim ((lt_irrefl _) hImpossible)
  · let L : ℕ → ℝ := fun j =>
        thirdFullPhysicalKineticLowBandDissipationRate244 j
          (velocityH3Energy0At u b)
    have hL : ∀ j : ℕ, 0 ≤ L j := fun j =>
      thirdFullPhysicalKineticLowBandDissipationRate_nonneg244 j _
    exact ⟨N, thirdFull_scalar_kineticAnnularRate_forces_outerCutoffEscape244
      L n N n0 M _ hL hB (by simpa only [L] using hAmplified)
      (by simpa only [L] using hSmall)⟩


/-- Preserve all primary/secondary observations and first-window charges from
 the original cofinal high-radial ledger, but replace the second annular
PDE-rate certificate by an actual kinetic-only natural-annulus charge.
The new outer cutoff is selected AFTER the earlier two observations and
lower natural radius n. Nothing is asserted uniform as n grows. -/
def ThirdFullLateRetainedPrimarySecondaryNaturalKineticAnnularCofinalLedger244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b m r P V : ℝ) (J : ℕ)
    (sSource sState eta1 : ℝ) : Prop :=
  ThirdFullLateRetainedPrimarySecondaryHighRadialCofinalLedger244
    hH3 b m r P V J sSource sState eta1 ∧
  let C0 : ℝ := 3 + h3AuditInitialLerayEnergyCoefficient
  let E0 : ℝ := 1 + 6 * velocityH3Energy0At u b
  let R : ℝ := 96 * C0 * (((J : ℝ) + 2) ^ 5)
  let A : ℝ := V / (2 * P)
  let B : ℝ := ∫ t in m..T, velocityH3DissipationAt u t ∂volume
  (A ^ 2 ≤ R *
      (E0 + 3 * velocityH3DissipationAt u sState) *
      (E0 + 3 * velocityH3DissipationAt u sSource) * B →
    4 * R * B * E0 ^ 2 < A ^ 2 →
    48 * Real.sqrt (R * B) ≤ 1 →
    ∃ (s eta2 : ℝ) (J2 : ℕ) (zSource zState : ℝ),
      (s = sState ∨ s = sSource) ∧ r ≤ s ∧
      0 < eta2 ∧ s + eta2 < T ∧
      zSource ∈ Set.Icc s (s + (T - s) / 2) ∧
      zState ∈ Set.Icc s (s + (T - s) / 2) ∧
      (∀ (n : ℕ) (M : ℝ), 0 < M →
        192 * B * Real.sqrt (R * B) < (T - s) * A →
        576 * R * B ^ 2 *
          (96 * C0 *
            (E0 + 3 * (((n : ℝ) + 1) ^ 2 *
              (h3TerminalRadialSobolevWeightSquareCeiling ((n : ℝ) + 1) *
                velocityH3Energy0At u b) + 2 * M)) ^ 2 *
              (((J2 : ℝ) + 2) ^ 5) + 4) < A ^ 2 →
        ∃ x : ℝ, (x = zState ∨ x = zSource) ∧
          ThirdFullSecondaryNaturalKineticAnnularCharge244
            hH3 b m s x n M))

/-- Complete same-witness lift of the old cofinal high-radial ledger. All
quantifiers n,M enter AFTER the old secondary state/source times and J2.
The outer cutoff selected by Fourier tail decay remains free to escape. -/
theorem thirdFullPhysical_secondaryHighRadialLedger_to_naturalKineticAnnular244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (m r P V : ℝ) (J : ℕ) (sSource sState eta1 : ℝ)
    (hm : m ∈ Set.Ioo b T) (hr : r ∈ Set.Ioo m T)
    (hOld : ThirdFullLateRetainedPrimarySecondaryHighRadialCofinalLedger244
      hH3 b m r P V J sSource sState eta1) :
    ThirdFullLateRetainedPrimarySecondaryNaturalKineticAnnularCofinalLedger244
      hH3 b m r P V J sSource sState eta1 := by
  let C0 : ℝ := 3 + h3AuditInitialLerayEnergyCoefficient
  let E0 : ℝ := 1 + 6 * velocityH3Energy0At u b
  let R : ℝ := 96 * C0 * (((J : ℝ) + 2) ^ 5)
  let A : ℝ := V / (2 * P)
  let B : ℝ := ∫ t in m..T, velocityH3DissipationAt u t ∂volume
  change ThirdFullLateRetainedPrimarySecondaryHighRadialCofinalLedger244
      hH3 b m r P V J sSource sState eta1 ∧
    (A ^ 2 ≤ R *
        (E0 + 3 * velocityH3DissipationAt u sState) *
        (E0 + 3 * velocityH3DissipationAt u sSource) * B →
      4 * R * B * E0 ^ 2 < A ^ 2 →
      48 * Real.sqrt (R * B) ≤ 1 →
      ∃ (s eta2 : ℝ) (J2 : ℕ) (zSource zState : ℝ),
        (s = sState ∨ s = sSource) ∧ r ≤ s ∧
        0 < eta2 ∧ s + eta2 < T ∧
        zSource ∈ Set.Icc s (s + (T - s) / 2) ∧
        zState ∈ Set.Icc s (s + (T - s) / 2) ∧
        (∀ (n : ℕ) (M : ℝ), 0 < M →
          192 * B * Real.sqrt (R * B) < (T - s) * A →
          576 * R * B ^ 2 *
            (96 * C0 *
              (E0 + 3 * (((n : ℝ) + 1) ^ 2 *
                (h3TerminalRadialSobolevWeightSquareCeiling ((n : ℝ) + 1) *
                  velocityH3Energy0At u b) + 2 * M)) ^ 2 *
                (((J2 : ℝ) + 2) ^ 5) + 4) < A ^ 2 →
          ∃ x : ℝ, (x = zState ∨ x = zSource) ∧
            ThirdFullSecondaryNaturalKineticAnnularCharge244
              hH3 b m s x n M))
  refine ⟨hOld, ?_⟩
  intro hRate hGap hStrong
  obtain ⟨s, eta2, J2, zSource, zState,
      hChoice, hrs, heta2, hend2, hzSource, hzState, hRadial⟩ :=
    hOld.2 hRate hGap hStrong
  have hsT : s < T := by linarith only [heta2, hend2]
  have hHalfEnd : s + (T - s) / 2 < T := by
    linarith only [hsT]
  have hzSourceTime : zSource ∈ Set.Ioo m T :=
    ⟨lt_of_lt_of_le hr.1 (le_trans hrs hzSource.1),
      lt_of_le_of_lt hzSource.2 hHalfEnd⟩
  have hzStateTime : zState ∈ Set.Ioo m T :=
    ⟨lt_of_lt_of_le hr.1 (le_trans hrs hzState.1),
      lt_of_le_of_lt hzState.2 hHalfEnd⟩
  refine ⟨s, eta2, J2, zSource, zState,
    hChoice, hrs, heta2, hend2, hzSource, hzState, ?_⟩
  intro n M hM hWide hDemand
  have hHigh := hRadial ((n : ℝ) + 1) (2 * M)
    (by positivity) hWide
    (by simpa only [E0, C0] using hDemand)
  exact thirdFullPhysical_secondaryTwoSlice_forcesKineticAnnularCharge244
    hH3 hClass hDInt b hb m s zState zSource n M
    hm hzStateTime hzSourceTime hzState hzSource hM hHigh


/-- The cofinal no-terminal-H³-trace obstruction, with its original
first-crossing minimal windows, frequency escape, disjoint viscous sum and
vanishing terminal integral, now carries the additional annular PDE
clock-or-rate alternative on its retained physical high-radial branch.
No new annular interval is falsely added to the old disjoint charge sum. -/
theorem thirdFullPhysical_noH3Trace_prescribedGauge_secondaryNaturalKineticAnnular244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (H : ℕ → ℝ) (hH : ∀ n : ℕ, 1 ≤ H n) :
    ∃ (U : H3PhysicalRealFinVectorL2Hilbert)
      (tau : ℕ → ℝ) (N : ℕ → ℕ) (K C delta : ℕ → ℝ) (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k => tau (v k)) atTop (𝓝 T) ∧
      (∀ k, ThirdFullProfileMinimalAttainedSourceWindow244 hH3
        (fun n : ℕ => (H n) ^ 8) tau N K C delta (v k)) ∧
      (∀ j : ℕ,
        (∑ k ∈ Finset.range j,
          delta (v k) * ((H (v k)) ^ 8 / 4)) ≤
            ∫ s in a..T, velocityH3DissipationAt u s) ∧
      Tendsto (fun k : ℕ =>
        ((N (v k) : ℝ) + 2) / H (v k)) atTop atTop ∧
      (∀ᶠ k : ℕ in atTop,
        let t := tau (v k)
        let m := (t + T) / 2
        let Q := (N (v k) : ℝ) + 2
        let F := h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap
        let C0 := 3 + h3AuditInitialLerayEnergyCoefficient
        let E0 := 1 + 6 * velocityH3Energy0At u b
        let P := 168 * Q ^ 4 * (‖F‖ * C0) * (T - m)
        let V := (H (v k)) ^ 4
        V < 14 * Q ^ 4 *
          ‖thirdFullSpectralVelocityHighRadialApply244 (v k) (F U)‖ ∨
        (∃ r : ℝ, r ∈ Set.Icc t m ∧
          V < 28 * Q ^ 4 *
            (‖F‖ * ((m - t) *
              ‖h3PathActualProjectedMomentumSource244 hH3 r‖))) ∨
        V < 56 * Q ^ 4 * (‖F‖ * C0 * ((T - m) * E0)) ∨
        (∃ (r : ℝ) (J : ℕ) (sSource sState eta1 : ℝ),
          r ∈ Set.Ioo m T ∧ 0 < P ∧
          sSource ∈ Set.Icc r (r + (T - r) / 2) ∧
          sState ∈ Set.Icc r (r + (T - r) / 2) ∧
          eta1 = min ((T - r) / 4)
            ((V / (2 * P)) /
              (2 * (thirdFullLateViscousLowRadialPDERate244 J
                ‖h3AuditActualSpectralVelocityTotal hH3 sState‖
                ‖h3PathActualProjectedMomentumSource244 hH3 sSource‖ + 1))) ∧
          0 < eta1 ∧ r + eta1 < T ∧
          (∀ s : ℝ, s ∈ Set.Icc r (r + eta1) →
            V / (2 * P) <
              h3PathActualLowRadialDissipation244 ((J : ℝ) + 1)
                (h3AuditActualSpectralVelocityTotal hH3 s) ∧
            V / (2 * P) < velocityH3DissipationAt u s) ∧
          eta1 * (V / (2 * P)) ≤
            ∫ s in m..T, velocityH3DissipationAt u s ∂volume ∧
          ThirdFullLateRetainedPrimarySecondaryNaturalKineticAnnularCofinalLedger244
            hH3 b m r P V J sSource sState eta1)) ∧
      Tendsto (fun k : ℕ =>
        ∫ s in ((tau (v k) + T) / 2)..T,
          velocityH3DissipationAt u s ∂volume)
        atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨U, tau, N, K, C, delta, v, hMono, hLimit,
      hWindows, hCharges, hEscape, hOld, hViscousTail⟩ :=
    thirdFullPhysical_noH3Trace_prescribedGauge_secondaryHighRadial244
      hH3 hClass b hb hNoTrace hDInt H hH
  have hAfter : ∀ᶠ k : ℕ in atTop, b < tau (v k) :=
    hLimit.eventually (isOpen_Ioi.mem_nhds hb.2)
  refine ⟨U, tau, N, K, C, delta, v, hMono, hLimit,
    hWindows, hCharges, hEscape, ?_, hViscousTail⟩
  filter_upwards [hOld, hAfter] with k hkOld hkAfter
  dsimp only at hkOld ⊢
  let t : ℝ := tau (v k)
  let m : ℝ := (t + T) / 2
  let Q : ℝ := (N (v k) : ℝ) + 2
  let F : H3PhysicalRealFinVectorL2Hilbert →L[ℝ] H3SpectralVelocityState :=
    h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap
  let C0 : ℝ := 3 + h3AuditInitialLerayEnergyCoefficient
  let E0 : ℝ := 1 + 6 * velocityH3Energy0At u b
  let P : ℝ := 168 * Q ^ 4 * (‖F‖ * C0) * (T - m)
  let V : ℝ := (H (v k)) ^ 4
  rcases hkOld with hCarrier | hSource | hClock |
      ⟨r, J, sSource, sState, eta1, hr, hP,
        hsSource, hsState, hEtaEq, heta1, hend1, hFloor, hCharge, hLedger⟩
  · exact Or.inl hCarrier
  · exact Or.inr (Or.inl hSource)
  · exact Or.inr (Or.inr (Or.inl hClock))
  · right; right; right
    have hmT : m < T := lt_trans hr.1 hr.2
    have htT : t < T := by
      dsimp only [m] at hmT
      linarith only [hmT]
    have htm : t < m := by
      dsimp only [m]
      linarith only [htT]
    have hmB : m ∈ Set.Ioo b T :=
      ⟨lt_trans hkAfter htm, hmT⟩
    have hPhysical :=
      thirdFullPhysical_secondaryHighRadialLedger_to_naturalKineticAnnular244
        hH3 hClass hDInt b hb m r P V J sSource sState eta1
        hmB hr hLedger
    exact ⟨r, J, sSource, sState, eta1, hr, hP,
      hsSource, hsState, hEtaEq, heta1, hend1,
      hFloor, hCharge, hPhysical⟩


end
end PrimeTensor.FirstMonomialTriad
