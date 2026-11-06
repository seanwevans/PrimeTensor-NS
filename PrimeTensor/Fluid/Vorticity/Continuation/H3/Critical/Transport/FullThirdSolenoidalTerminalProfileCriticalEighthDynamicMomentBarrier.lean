import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileCriticalEighthWindowRawTransport
import Mathlib.Tactic

/-!
# Dynamic eighth-moment barrier on real Navier--Stokes source windows

The physical minimal-first-crossing windows persist at one quarter of the
constructed critical-eighth dissipation height at EVERY time of the window.
On those same times, the physical Hilbert FTC and the Bochner L¹ source
action uniformly control the RAW Fourier mass of the moving annulus.

Combining the genuine annular H⁴ dissipation-to-raw-eighth-moment inequality
with this dynamical raw-mass estimate forces

  η R⁸ < 48 Q⁸ (raw-highpass-at-start + ‖Fourier‖ * source-L¹-action)².

The right-hand parenthesis tends to zero along the original disjoint windows.
This quantifies the frequency amplification needed to sustain the eighth
moment; neither a bound on Q/R nor a Navier--Stokes regularity theorem follows.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

/-- Pure algebra: persistent eighth-moment dissipation and a Fourier mass
controlled by a transport amplitude demand a large eighth-frequency gain. -/
theorem thirdFull_criticalEighth_persistentMoment_transportAmplifier244
    (R Q M D μ B η : ℝ)
    (hHeight : η * R ^ 8 ≤ M)
    (hFloor : M / 4 < D)
    (hDiss : D ≤ 4 * Q ^ 8 * μ)
    (hMass : μ ≤ 3 * B ^ 2) :
    η * R ^ 8 < 48 * Q ^ 8 * B ^ 2 := by
  have hScaled : 16 * Q ^ 8 * μ ≤ 16 * Q ^ 8 * (3 * B ^ 2) :=
    mul_le_mul_of_nonneg_left hMass (by positivity)
  calc
    η * R ^ 8 ≤ M := hHeight
    _ = 4 * (M / 4) := by ring
    _ < 4 * D := mul_lt_mul_of_pos_left hFloor (by norm_num)
    _ ≤ 4 * (4 * Q ^ 8 * μ) :=
      mul_le_mul_of_nonneg_left hDiss (by norm_num)
    _ = 16 * Q ^ 8 * μ := by ring
    _ ≤ 16 * Q ^ 8 * (3 * B ^ 2) := hScaled
    _ = 48 * Q ^ 8 * B ^ 2 := by ring

/-- At EVERY physical time in a genuinely attained minimal-crossing window,
its persistent H³-dissipation height is charged to the initial physical raw
highpass plus the ACTUAL absolute projected-source action on that window.
The source maximum C does not appear, and no radial cutoff is replaced. -/
theorem thirdFullPhysical_criticalEighth_window_persistentMoment_transportBarrier244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (η : ℝ) (τ : ℕ → ℝ) (N : ℕ → ℕ)
    (K C δ : ℕ → ℝ) (n : ℕ)
    (ht : τ n ∈ Set.Ioo a T)
    (hWindow : ThirdFullProfileMinimalAttainedSourceWindow244 hH3
      (thirdFullConstructiveCriticalEighthProfile244 η) τ N K C δ n)
    (s : ℝ) (hs : s ∈ Set.Icc (τ n) (τ n + δ n)) :
    η * (((n : ℝ) + 1) ^ 8) <
      48 * (((N n : ℝ) + 2) ^ 8) *
      (‖thirdFullSpectralVelocityHighRadialApply244 n
          (h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap
            (h3AuditInitialOldPhysicalHilbertTotal hH3 (τ n)))‖ +
        ‖h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap‖ *
          (∫ r in τ n..(τ n + δ n),
            ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume)) ^ 2 := by
  let X : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3
  let G : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3
  let F : H3PhysicalRealFinVectorL2Hilbert →L[ℝ] H3SpectralVelocityState :=
    h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap
  let μ : ℝ := h3PathActualBandRawKineticMass244
    ((n : ℝ) + 1) ((N n : ℝ) + 1)
    (h3AuditActualSpectralVelocityTotal hH3 s)
  let B : ℝ :=
    ‖thirdFullSpectralVelocityHighRadialApply244 n (F (X (τ n)))‖ +
      ‖F‖ * (∫ r in τ n..(τ n + δ n), ‖G r‖ ∂volume)
  let D : ℝ :=
    h3PathActualLowRadialDissipation244 ((N n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 s) -
      h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 s)
  rcases hWindow.1.1 with
    ⟨hnN, _, _, hδ, _, hEnd, _, _, _, _, _, hFloor, _⟩
  have hsClass : s ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le ht.1 hs.1, lt_of_le_of_lt hs.2 hEnd⟩
  have htAbs : τ n ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  have hEndAbs : τ n + δ n ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans htAbs.1 (by linarith only [hδ]), hEnd⟩
  have hsAbs : s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_of_lt_of_le htAbs.1 hs.1, lt_of_le_of_lt hs.2 hEnd⟩
  have hnNReal : (n : ℝ) ≤ (N n : ℝ) := by exact_mod_cast hnN
  have hRQ : ((n : ℝ) + 1) ≤ ((N n : ℝ) + 1) := by
    linarith only [hnNReal]
  have hDissOriginal :=
    h3Path_actualAnnularDissipation_le_shiftedEighthBandMass244
      hH3 hClass s hsClass
      ((n : ℝ) + 1) ((N n : ℝ) + 1) hRQ (by positivity)
  have hDiss : D ≤ 4 * (((N n : ℝ) + 2) ^ 8) * μ := by
    dsimp only [D, μ]
    convert hDissOriginal using 1 <;> ring
  have hRaw : μ ≤ 3 * B ^ 2 := by
    exact thirdFullPhysical_rawBandMass_window_le_sourceL1244
      hH3 n ((N n : ℝ) + 1) (τ n) (τ n + δ n) s
      htAbs hEndAbs hsAbs hs.1 hs.2
  have hCritical : η * (((n : ℝ) + 1) ^ 8) ≤
      thirdFullConstructiveCriticalEighthProfile244 η n :=
    thirdFullConstructiveCriticalEighthProfile_lower244 η n
  have hFloorD : thirdFullConstructiveCriticalEighthProfile244 η n / 4 < D :=
    hFloor s hs
  change η * (((n : ℝ) + 1) ^ 8) <
      48 * (((N n : ℝ) + 2) ^ 8) * B ^ 2
  exact thirdFull_criticalEighth_persistentMoment_transportAmplifier244
    ((n : ℝ) + 1) ((N n : ℝ) + 2)
    (thirdFullConstructiveCriticalEighthProfile244 η n)
    D μ B η hCritical hFloorD hDiss hRaw

/-- SAME-WITNESS physical consequence of failure of the strong terminal H³
trace: disjoint critical-eighth windows simultaneously carry persistent
H³ annular dissipation and vanishing raw kinetic/source amplitudes. The
quantitative eighth-frequency amplifier is compulsory on EVERY late window
time; no new endpoint regularity hypothesis or source bound is imposed. -/
theorem thirdFullPhysical_noH3Trace_criticalEighth_dynamicMomentBarrier244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (η : ℝ) (hη : 0 < η) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ) (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ k, ThirdFullProfileMinimalAttainedSourceWindow244 hH3
        (thirdFullConstructiveCriticalEighthProfile244 η) τ N K C δ (v k)) ∧
      Summable (fun k : ℕ => δ (v k) * (((v k : ℝ) + 1) ^ 8)) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
        ∀ s : ℝ, s ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k)) →
          h3PathActualBandRawKineticMass244
            ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s) < ε) ∧
      Tendsto (fun k : ℕ =>
        ((N (v k) : ℝ) + 2) / ((v k : ℝ) + 1)) atTop atTop ∧
      (∀ᶠ k : ℕ in atTop,
        ∀ s : ℝ, s ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k)) →
          η * (((v k : ℝ) + 1) ^ 8) <
            48 * (((N (v k) : ℝ) + 2) ^ 8) *
            (‖thirdFullSpectralVelocityHighRadialApply244 (v k)
                (h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap
                  (h3AuditInitialOldPhysicalHilbertTotal hH3 (τ (v k))))‖ +
              ‖h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap‖ *
                (∫ r in τ (v k)..(τ (v k) + δ (v k)),
                  ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume)) ^ 2) ∧
      Tendsto (fun k : ℕ =>
        ‖thirdFullSpectralVelocityHighRadialApply244 (v k)
          (h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap
            (h3AuditInitialOldPhysicalHilbertTotal hH3 (τ (v k))))‖ +
        ‖h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap‖ *
          (∫ r in τ (v k)..(τ (v k) + δ (v k)),
            ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume))
        atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨τ, N, K, C, δ, v, hMono, hLimit, hWindows, hClock,
      hUniform, hEscape, hL1⟩ :=
    thirdFullPhysical_noH3Trace_criticalEighth_uniformWindowRawMass244
      hH3 hClass b hb hNoTrace hDInt η hη
  let X : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3
  let F : H3PhysicalRealFinVectorL2Hilbert →L[ℝ] H3SpectralVelocityState :=
    h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap
  let G : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3
  have hPos (k : ℕ) : 0 < δ (v k) ∧ τ (v k) + δ (v k) < T := by
    rcases (hWindows k).1.1 with
      ⟨_, _, _, hδ, _, hEnd, _, _, _, _, _, _, _⟩
    exact ⟨hδ, hEnd⟩
  have hBefore (k : ℕ) : τ (v k) < T := by
    linarith only [(hPos k).1, (hPos k).2]
  have hLimitLeft : Tendsto (fun k : ℕ => τ (v k)) atTop (𝓝[<] T) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hLimit, Filter.Eventually.of_forall (fun k => hBefore k)⟩
  obtain ⟨L, hTrace⟩ :=
    h3Critical_physicalL2_terminal_trace_of_finite_dissipation
      hH3 hClass hDInt
  have hPhysical : Tendsto (fun k : ℕ => X (τ (v k)))
      atTop (𝓝 L) := hTrace.comp hLimitLeft
  have hHigh : Tendsto (fun k : ℕ =>
      ‖thirdFullSpectralVelocityHighRadialApply244 (v k)
        (F (X (τ (v k))))‖) atTop (𝓝 (0 : ℝ)) :=
    thirdFullPhysical_movingRawHighpass_norm_tendsto_zero244
      (fun k : ℕ => X (τ (v k))) L v
      hPhysical hMono.tendsto_atTop
  have hAmplitude : Tendsto (fun k : ℕ =>
      ‖thirdFullSpectralVelocityHighRadialApply244 (v k)
        (F (X (τ (v k))))‖ +
      ‖F‖ * (∫ r in τ (v k)..(τ (v k) + δ (v k)),
        ‖G r‖ ∂volume)) atTop (𝓝 (0 : ℝ)) := by
    have hSum := hHigh.add (hL1.const_mul ‖F‖)
    simpa only [mul_zero, add_zero] using hSum
  have hAfter : ∀ᶠ k : ℕ in atTop, a < τ (v k) := by
    filter_upwards [hLimit.eventually (isOpen_Ioi.mem_nhds hb.2)] with k hk
    exact lt_trans hb.1 hk
  have hBarrier : ∀ᶠ k : ℕ in atTop,
      ∀ s : ℝ, s ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k)) →
        η * (((v k : ℝ) + 1) ^ 8) <
          48 * (((N (v k) : ℝ) + 2) ^ 8) *
          (‖thirdFullSpectralVelocityHighRadialApply244 (v k)
              (F (X (τ (v k))))‖ +
            ‖F‖ * (∫ r in τ (v k)..(τ (v k) + δ (v k)),
              ‖G r‖ ∂volume)) ^ 2 := by
    filter_upwards [hAfter] with k hk
    intro s hs
    have ht : τ (v k) ∈ Set.Ioo a T := ⟨hk, hBefore k⟩
    exact thirdFullPhysical_criticalEighth_window_persistentMoment_transportBarrier244
      hH3 hClass η τ N K C δ (v k) ht (hWindows k) s hs
  exact ⟨τ, N, K, C, δ, v, hMono, hLimit, hWindows, hClock,
    hUniform, hEscape, hBarrier, hAmplitude⟩

end
end PrimeTensor.FirstMonomialTriad
