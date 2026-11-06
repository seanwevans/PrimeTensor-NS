import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileCriticalEighthSourceL1Tail
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileMovingRawFourierTightness
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Dynamic raw Fourier tightness on the actual critical-eighth physical windows

The exact physical Hilbert FTC bounds the motion of the raw Fourier highpass
by the absolute L¹ action of the projected Navier--Stokes momentum source.
This is a *moving* frequency projection: the inner radius may go to infinity
as the positive-time window approaches T. The norm of the real-linear
physical Plancherel map is kept explicitly, rather than assuming an
unproved isometry constant.

Combining this transport estimate with the already proved terminal raw L²
tightness and source L¹ tail shows that the *whole physical persistence
window* has vanishing moving annular raw kinetic mass, uniformly in the
time variable. In contrast, the exact H³-weighted dissipation remains
positive at the prescribed eighth-power level on the same windows.

This is a same-witness dynamical spectral separation. It does not bound the
weighted H³ highpass by its unweighted counterpart and does not by itself
exclude the no-H³-trace branch.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

/-!
The highpass triangle estimate is proved once on the weighted spectral
vector space, without unfolding physical Plancherel or Lp internals.
The first two source transport results are parametric in a real continuous
linear map.  This avoids elaborating a large physical Fourier implementation
in their theorem types and keeps the actual map for the annular mass bridge.
-/

private theorem thirdFullRawHighpass_triangle244
    (n : ℕ) (A B : H3SpectralVelocityState) :
    ‖thirdFullSpectralVelocityHighRadialApply244 n A‖ ≤
      ‖thirdFullSpectralVelocityHighRadialApply244 n B‖ + ‖A - B‖ := by
  calc
    ‖thirdFullSpectralVelocityHighRadialApply244 n A‖ =
        ‖thirdFullSpectralVelocityHighRadialApply244 n ((A - B) + B)‖ := by
          rw [sub_add_cancel]
    _ = ‖thirdFullSpectralVelocityHighRadialApply244 n (A - B) +
        thirdFullSpectralVelocityHighRadialApply244 n B‖ := by
          rw [thirdFullSpectralVelocityHighRadialApply_add244]
    _ ≤ ‖thirdFullSpectralVelocityHighRadialApply244 n (A - B)‖ +
        ‖thirdFullSpectralVelocityHighRadialApply244 n B‖ :=
          norm_add_le _ _
    _ ≤ ‖A - B‖ +
        ‖thirdFullSpectralVelocityHighRadialApply244 n B‖ :=
          add_le_add_left
            (thirdFullSpectralVelocityHighRadialApply_norm_le244 n (A - B)) _
    _ = _ := add_comm _ _

/-- Transport of a genuine highpass under any bounded real-linear observation
of the actual physical momentum equation. The proof uses only the physical
Hilbert FTC, not a reduction of the Fourier transform implementation. -/
theorem thirdFullPhysical_rawHighpass_transport_le_sourceL1244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (F : H3PhysicalRealFinVectorL2Hilbert →L[ℝ] H3SpectralVelocityState)
    (n : ℕ) (t s : ℝ)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (hts : t ≤ s) :
    ‖thirdFullSpectralVelocityHighRadialApply244 n
        (F (h3AuditInitialOldPhysicalHilbertTotal hH3 s))‖ ≤
      ‖thirdFullSpectralVelocityHighRadialApply244 n
        (F (h3AuditInitialOldPhysicalHilbertTotal hH3 t))‖ +
      ‖F‖ *
        (∫ r in t..s, ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume) := by
  let X : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3
  let G : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3
  have hFTC := h3Path_physicalHilbertFTC_betweenPositiveTimes244
    hH3 t s ht hs
  change X s - X t = ∫ r in t..s, G r ∂volume at hFTC
  have hVelocity : ‖X s - X t‖ ≤
      ∫ r in t..s, ‖G r‖ ∂volume := by
    calc
      ‖X s - X t‖ = ‖∫ r in t..s, G r ∂volume‖ :=
        congrArg norm hFTC
      _ ≤ ∫ r in t..s, ‖G r‖ ∂volume :=
        intervalIntegral.norm_integral_le_integral_norm hts
  have hMap : ‖F (X s) - F (X t)‖ ≤
      ‖F‖ * ‖X s - X t‖ := by
    calc
      ‖F (X s) - F (X t)‖ = ‖F (X s - X t)‖ := by
        rw [map_sub]
      _ ≤ ‖F‖ * ‖X s - X t‖ :=
        ContinuousLinearMap.le_opNorm F (X s - X t)
  have hTransport := thirdFullRawHighpass_triangle244
    n (F (X s)) (F (X t))
  change ‖thirdFullSpectralVelocityHighRadialApply244 n (F (X s))‖ ≤
    ‖thirdFullSpectralVelocityHighRadialApply244 n (F (X t))‖ +
      ‖F‖ * ∫ r in t..s, ‖G r‖ ∂volume
  exact hTransport.trans (add_le_add_right
    (hMap.trans (mul_le_mul_of_nonneg_left hVelocity (norm_nonneg F))) _)

/-- The same physical Bochner L1 action bounds the highpass uniformly for
all times inside an ordered physical interval. -/
theorem thirdFullPhysical_rawHighpass_window_le_sourceL1244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (F : H3PhysicalRealFinVectorL2Hilbert →L[ℝ] H3SpectralVelocityState)
    (n : ℕ) (t σ s : ℝ)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hσ : σ ∈ Set.Ioo (0 : ℝ) T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (hts : t ≤ s) (hsσ : s ≤ σ) :
    ‖thirdFullSpectralVelocityHighRadialApply244 n
        (F (h3AuditInitialOldPhysicalHilbertTotal hH3 s))‖ ≤
      ‖thirdFullSpectralVelocityHighRadialApply244 n
        (F (h3AuditInitialOldPhysicalHilbertTotal hH3 t))‖ +
      ‖F‖ *
        (∫ r in t..σ, ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume) := by
  let G : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3
  have hInt : IntervalIntegrable G volume t σ := by
    change IntervalIntegrable
      (fun r : ℝ =>
        h3AuditInitialActualSpectralLaplacianTotal hH3 r -
          h3AuditInitialActualSpectralLerayTotal hH3 r) volume t σ
    exact h3Audit_initialActualProjectedRHS_intervalIntegrable_between_positiveTimes
      hH3 t σ ht hσ
  have hNonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioc t σ)]
        (fun r : ℝ => ‖G r‖) := by
    filter_upwards [] with r
    exact norm_nonneg (G r)
  have hSubIntegral :
      (∫ r in t..s, ‖G r‖ ∂volume) ≤
        ∫ r in t..σ, ‖G r‖ ∂volume :=
    intervalIntegral.integral_mono_interval
      le_rfl hts hsσ hNonneg hInt.norm
  have hFirst := thirdFullPhysical_rawHighpass_transport_le_sourceL1244
    hH3 F n t s ht hs hts
  change ‖thirdFullSpectralVelocityHighRadialApply244 n
      (F (h3AuditInitialOldPhysicalHilbertTotal hH3 s))‖ ≤
    ‖thirdFullSpectralVelocityHighRadialApply244 n
      (F (h3AuditInitialOldPhysicalHilbertTotal hH3 t))‖ +
      ‖F‖ * (∫ r in t..σ, ‖G r‖ ∂volume)
  exact hFirst.trans (add_le_add_right
    (mul_le_mul_of_nonneg_left hSubIntegral (norm_nonneg F)) _)

/-- Actual raw annular kinetic mass at every intermediate time is bounded
by the source integral on the enclosing physical window. -/
theorem thirdFullPhysical_rawBandMass_window_le_sourceL1244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (n : ℕ) (Q : ℝ) (t σ s : ℝ)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hσ : σ ∈ Set.Ioo (0 : ℝ) T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (hts : t ≤ s) (hsσ : s ≤ σ) :
    h3PathActualBandRawKineticMass244 ((n : ℝ) + 1) Q
      (h3AuditActualSpectralVelocityTotal hH3 s) ≤
      3 * (‖thirdFullSpectralVelocityHighRadialApply244 n
          (h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap
            (h3AuditInitialOldPhysicalHilbertTotal hH3 t))‖ +
        ‖h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap‖ *
          (∫ r in t..σ,
            ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume)) ^ 2 := by
  let F : H3PhysicalRealFinVectorL2Hilbert →L[ℝ] H3SpectralVelocityState :=
    h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap
  let X : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3
  let G : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3
  have hHigh := thirdFullPhysical_rawHighpass_window_le_sourceL1244
    hH3 F n t σ s ht hσ hs hts hsσ
  have hRaw := thirdFullPhysical_actualRawFourierVector_eq_physical244
    hH3 s hs
  have hMass := thirdFull_bandRawKineticMass_le_three_highpass244
    n Q (h3AuditActualSpectralVelocityTotal hH3 s)
  rw [hRaw] at hMass
  change h3PathActualBandRawKineticMass244 ((n : ℝ) + 1) Q
      (h3AuditActualSpectralVelocityTotal hH3 s) ≤
    3 * ‖thirdFullSpectralVelocityHighRadialApply244 n (F (X s))‖ ^ 2 at hMass
  have hUpper :
      ‖thirdFullSpectralVelocityHighRadialApply244 n (F (X s))‖ ≤
        ‖thirdFullSpectralVelocityHighRadialApply244 n (F (X t))‖ +
          ‖F‖ * (∫ r in t..σ, ‖G r‖ ∂volume) := hHigh
  have hPositive : 0 ≤
      ‖thirdFullSpectralVelocityHighRadialApply244 n (F (X t))‖ +
        ‖F‖ * (∫ r in t..σ, ‖G r‖ ∂volume) :=
    (norm_nonneg _).trans hUpper
  have hSquare := (sq_le_sq₀ (norm_nonneg _) hPositive).2 hUpper
  have hMultiply := mul_le_mul_of_nonneg_left hSquare (by norm_num : (0 : ℝ) ≤ 3)
  exact hMass.trans (by
    change 3 * ‖thirdFullSpectralVelocityHighRadialApply244 n (F (X s))‖ ^ 2 ≤
      3 * (‖thirdFullSpectralVelocityHighRadialApply244 n (F (X t))‖ +
        ‖F‖ * (∫ r in t..σ, ‖G r‖ ∂volume)) ^ 2
    exact hMultiply)

/-- Hard same-window transfer: finite full H³ dissipation gives a terminal
physical L² trace and absolutely integrable physical source. Hence the
unweighted Fourier mass in a MOVING annulus vanishes uniformly throughout
the actual minimal-crossing physical persistence windows, not just at their
initial times. Neither the outer radii nor the source peaks are bounded. -/
theorem thirdFullPhysical_minimalWindows_uniformMovingRawMass244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (M : ℕ → ℝ) (τ : ℕ → ℝ) (N : ℕ → ℕ)
    (K C δ : ℕ → ℝ) (v : ℕ → ℕ)
    (hMono : StrictMono v)
    (hLimit : Tendsto (fun k : ℕ => τ (v k)) atTop (𝓝 T))
    (hWindows : ∀ k : ℕ,
      ThirdFullProfileMinimalAttainedSourceWindow244 hH3 M τ N K C δ (v k)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
      ∀ s : ℝ, s ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k)) →
        h3PathActualBandRawKineticMass244
          ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 s) < ε := by
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
  have hLimitLeft : Tendsto (fun k : ℕ => τ (v k))
      atTop (𝓝[<] T) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hLimit, Filter.Eventually.of_forall
      (fun k => hBefore k)⟩
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
  have hL1 : Tendsto (fun k : ℕ =>
      ∫ r in τ (v k)..(τ (v k) + δ (v k)), ‖G r‖ ∂volume)
      atTop (𝓝 (0 : ℝ)) :=
    thirdFullPhysical_criticalEighth_minimalWindows_sourceL1_tendsto_zero244
      hH3 hClass hDInt b hb M τ N K C δ v hLimit hWindows
  have hBound : Tendsto (fun k : ℕ =>
      3 * (‖thirdFullSpectralVelocityHighRadialApply244 (v k)
          (F (X (τ (v k))))‖ +
        ‖F‖ * (∫ r in τ (v k)..(τ (v k) + δ (v k)),
          ‖G r‖ ∂volume)) ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
    have hCombined := hHigh.add (hL1.const_mul ‖F‖)
    have hSquared := hCombined.pow 2
    have hScaled := hSquared.const_mul 3
    simpa using hScaled
  intro ε hε
  have hAfter : ∀ᶠ k : ℕ in atTop, b < τ (v k) :=
    hLimit.eventually (isOpen_Ioi.mem_nhds hb.2)
  have hSmall : ∀ᶠ k : ℕ in atTop,
      3 * (‖thirdFullSpectralVelocityHighRadialApply244 (v k)
          (F (X (τ (v k))))‖ +
        ‖F‖ * (∫ r in τ (v k)..(τ (v k) + δ (v k)),
          ‖G r‖ ∂volume)) ^ 2 < ε :=
    hBound.eventually (eventually_lt_nhds hε)
  filter_upwards [hAfter, hSmall] with k hkAfter hkSmall
  intro s hs
  have ht : τ (v k) ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 (lt_trans hb.1 hkAfter),
      hBefore k⟩
  have hσ : τ (v k) + δ (v k) ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans ht.1 (by linarith only [(hPos k).1]),
      (hPos k).2⟩
  have hsTime : s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_of_lt_of_le ht.1 hs.1, lt_of_le_of_lt hs.2 (hPos k).2⟩
  have hMassBound := thirdFullPhysical_rawBandMass_window_le_sourceL1244
    hH3 (v k) ((N (v k) : ℝ) + 1)
    (τ (v k)) (τ (v k) + δ (v k)) s
    ht hσ hsTime hs.1 hs.2
  exact hMassBound.trans_lt (by
    change 3 * (‖thirdFullSpectralVelocityHighRadialApply244 (v k)
        (F (X (τ (v k))))‖ +
      ‖F‖ * (∫ r in τ (v k)..(τ (v k) + δ (v k)),
        ‖G r‖ ∂volume)) ^ 2 < ε at hkSmall
    exact hkSmall)

/-- The constructive no-terminal-H³-trace branch now has UNIFORM raw kinetic
Fourier tightness throughout the very same windows with positive weighted
H³ annular dissipation, summable critical-eighth clocks, and diverging
minimal outer/inner frequency ratio. -/
theorem thirdFullPhysical_noH3Trace_criticalEighth_uniformWindowRawMass244
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
      (∀ k, ThirdFullProfileMinimalAttainedSourceWindow244
        hH3 (thirdFullConstructiveCriticalEighthProfile244 η)
        τ N K C δ (v k)) ∧
      Summable (fun k : ℕ => δ (v k) * (((v k : ℝ) + 1) ^ 8)) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
        ∀ s : ℝ, s ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k)) →
          h3PathActualBandRawKineticMass244
            ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s) < ε) ∧
      Tendsto (fun k : ℕ =>
        ((N (v k) : ℝ) + 2) / ((v k : ℝ) + 1)) atTop atTop ∧
      Tendsto (fun k : ℕ =>
        ∫ r in τ (v k)..(τ (v k) + δ (v k)),
          ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume)
        atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨τ, N, K, C, δ, v, hMono, hLimit,
      hWindows, hClock, hL1, _hMass, hEscape, _hPeaks⟩ :=
    thirdFullPhysical_noH3Trace_criticalEighth_sourceL1Tail244
      hH3 hClass b hb hNoTrace hDInt η hη
  have hUniform := thirdFullPhysical_minimalWindows_uniformMovingRawMass244
    hH3 hClass hDInt b hb
    (thirdFullConstructiveCriticalEighthProfile244 η)
    τ N K C δ v hMono hLimit hWindows
  exact ⟨τ, N, K, C, δ, v, hMono, hLimit,
    hWindows, hClock, hUniform, hEscape, hL1⟩

end
end PrimeTensor.FirstMonomialTriad
