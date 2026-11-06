import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileCriticalEighthDynamicMomentBarrier
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.FiniteDissipationTerminalTrace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Exact terminal physical source primitive and critical-eighth carrier forcing

The dynamic moment barrier uses the physical raw highpass at the start of each
selected window, plus the absolute projected-momentum-source action on that
window. The physical Hilbert FTC and terminal source Bochner integrability
allow both quantities to be replaced by a SINGLE terminal source-tail modulus.

The actual physical terminal state is the explicit Bochner primitive
  U = X(b) + ∫_b^T G(r) dr.
For any b < s < T, the exact physical momentum equation gives
  X(s) + ∫_s^T G(r) dr = U.
Hence the Fourier highpass at s is bounded by the highpass of U plus the
absolute physical source tail from s to T. On a selected minimal-crossing
window, monotonicity of the nonnegative norm integral gives the uniform bound
  η R_k^8 < 48 Q_k^8 (‖P^+_(v k) F U‖ + ‖F‖ ∫_(τ_(v k))^T ‖G‖)^2.

Both terms inside the bracket converge to zero, with one fixed actual
terminal physical L2 state U. The result does not constrain Q_k from above,
prove H3 regularity, or introduce new terminal spectral assumptions.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

/-- Exact physical terminal Duhamel identity from the existing unconditional
positive-time Hilbert FTC. The endpoint state is an ACTUAL Bochner primitive,
not an independently chosen subsequential Fourier limit. -/
theorem thirdFullPhysical_terminalProjectedSource_primitive_exact244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b : ℝ) (hb : b ∈ Set.Ioo (0 : ℝ) T)
    (hG : IntervalIntegrable (h3PathActualProjectedMomentumSource244 hH3)
      volume b T) :
    ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      ∀ t : ℝ, t ∈ Set.Ioo b T →
        h3AuditInitialOldPhysicalHilbertTotal hH3 t +
          ∫ r in t..T, h3PathActualProjectedMomentumSource244 hH3 r ∂volume = U := by
  let X : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3
  let G : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3
  let U : H3PhysicalRealFinVectorL2Hilbert :=
    X b + ∫ r in b..T, G r ∂volume
  refine ⟨U, ?_⟩
  intro t ht
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hb.1 ht.1, ht.2⟩
  have hFirst : IntervalIntegrable G volume b t := by
    change IntervalIntegrable
      (fun r : ℝ =>
        h3AuditInitialActualSpectralLaplacianTotal hH3 r -
          h3AuditInitialActualSpectralLerayTotal hH3 r) volume b t
    exact h3Audit_initialActualProjectedRHS_intervalIntegrable_between_positiveTimes
      hH3 b t hb htAbs
  have hSecond : IntervalIntegrable G volume t T := by
    apply hG.mono_set
    intro r hr
    have hr' : r ∈ Set.Icc t T := by
      simpa only [Set.uIcc_of_le ht.2.le] using hr
    have hr'' : r ∈ Set.Icc b T :=
      ⟨le_trans ht.1.le hr'.1, hr'.2⟩
    simpa only [Set.uIcc_of_le hb.2.le] using hr''
  have hAdd := intervalIntegral.integral_add_adjacent_intervals hFirst hSecond
  have hFTC := h3Path_physicalHilbertEvolution_betweenPositiveTimes244
    hH3 b t hb htAbs
  change X t = X b + ∫ r in b..t, G r ∂volume at hFTC
  change X t + ∫ r in t..T, G r ∂volume = U
  calc
    X t + ∫ r in t..T, G r ∂volume =
        (X b + ∫ r in b..t, G r ∂volume) +
          ∫ r in t..T, G r ∂volume := by rw [hFTC]
    _ = X b + ((∫ r in b..t, G r ∂volume) +
        ∫ r in t..T, G r ∂volume) := by rw [add_assoc]
    _ = X b + ∫ r in b..T, G r ∂volume := by rw [hAdd]
    _ = U := rfl

/-- The terminal physical L2 state directly dominates the moving raw Fourier
highpass, with the ACTUAL source L1 tail as its sole time-dependent error.
The physical Fourier map remains parametric here to avoid expensive unfolding. -/
theorem thirdFullPhysical_terminalHighpass_le_endpointPlusSourceTail244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b : ℝ) (U : H3PhysicalRealFinVectorL2Hilbert)
    (hU : ∀ t : ℝ, t ∈ Set.Ioo b T →
      h3AuditInitialOldPhysicalHilbertTotal hH3 t +
        ∫ r in t..T, h3PathActualProjectedMomentumSource244 hH3 r ∂volume = U)
    (F : H3PhysicalRealFinVectorL2Hilbert →L[ℝ] H3SpectralVelocityState)
    (n : ℕ) (t : ℝ) (ht : t ∈ Set.Ioo b T) :
    ‖thirdFullSpectralVelocityHighRadialApply244 n
        (F (h3AuditInitialOldPhysicalHilbertTotal hH3 t))‖ ≤
      ‖thirdFullSpectralVelocityHighRadialApply244 n (F U)‖ +
      ‖F‖ * (∫ r in t..T,
        ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume) := by
  let X : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3
  let G : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3
  have hIdentity : X t + ∫ r in t..T, G r ∂volume = U :=
    hU t ht
  have hDifference : X t - U = -(∫ r in t..T, G r ∂volume) := by
    rw [← hIdentity]
    abel
  have hVelocity : ‖X t - U‖ ≤ ∫ r in t..T, ‖G r‖ ∂volume := by
    rw [hDifference, norm_neg]
    exact intervalIntegral.norm_integral_le_integral_norm ht.2.le
  have hMap : ‖F (X t) - F U‖ ≤ ‖F‖ * ‖X t - U‖ := by
    calc
      ‖F (X t) - F U‖ = ‖F (X t - U)‖ := by rw [map_sub]
      _ ≤ ‖F‖ * ‖X t - U‖ :=
        ContinuousLinearMap.le_opNorm F (X t - U)
  have hTriangle :
      ‖thirdFullSpectralVelocityHighRadialApply244 n (F (X t))‖ ≤
        ‖thirdFullSpectralVelocityHighRadialApply244 n (F U)‖ +
          ‖F (X t) - F U‖ := by
    calc
      ‖thirdFullSpectralVelocityHighRadialApply244 n (F (X t))‖ =
          ‖thirdFullSpectralVelocityHighRadialApply244 n
            ((F (X t) - F U) + F U)‖ := by rw [sub_add_cancel]
      _ = ‖thirdFullSpectralVelocityHighRadialApply244 n (F (X t) - F U) +
          thirdFullSpectralVelocityHighRadialApply244 n (F U)‖ := by
            rw [thirdFullSpectralVelocityHighRadialApply_add244]
      _ ≤ ‖thirdFullSpectralVelocityHighRadialApply244 n (F (X t) - F U)‖ +
          ‖thirdFullSpectralVelocityHighRadialApply244 n (F U)‖ := norm_add_le _ _
      _ ≤ ‖F (X t) - F U‖ +
          ‖thirdFullSpectralVelocityHighRadialApply244 n (F U)‖ :=
            add_le_add_left
              (thirdFullSpectralVelocityHighRadialApply_norm_le244 n
                (F (X t) - F U)) _
      _ = _ := add_comm _ _
  change ‖thirdFullSpectralVelocityHighRadialApply244 n (F (X t))‖ ≤
    ‖thirdFullSpectralVelocityHighRadialApply244 n (F U)‖ +
      ‖F‖ * ∫ r in t..T, ‖G r‖ ∂volume
  exact hTriangle.trans (add_le_add_right
    (hMap.trans (mul_le_mul_of_nonneg_left hVelocity (norm_nonneg F))) _)

/-- Exact critical-eighth dissipation persistence on the MINIMAL physical
annulus, charged only to the fixed terminal Fourier tail and the absolute
physical momentum-source tail. The coefficient 48 comes from the existing
fourth-derivative annular moment and three-component raw Fourier estimates. -/
theorem thirdFullPhysical_criticalEighth_window_endpointTailMomentBarrier244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (η : ℝ) (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hG : IntervalIntegrable (h3PathActualProjectedMomentumSource244 hH3)
      volume b T)
    (U : H3PhysicalRealFinVectorL2Hilbert)
    (hU : ∀ t : ℝ, t ∈ Set.Ioo b T →
      h3AuditInitialOldPhysicalHilbertTotal hH3 t +
        ∫ r in t..T, h3PathActualProjectedMomentumSource244 hH3 r ∂volume = U)
    (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ) (n : ℕ)
    (ht : τ n ∈ Set.Ioo b T)
    (hWindow : ThirdFullProfileMinimalAttainedSourceWindow244 hH3
      (thirdFullConstructiveCriticalEighthProfile244 η) τ N K C δ n)
    (s : ℝ) (hs : s ∈ Set.Icc (τ n) (τ n + δ n)) :
    η * (((n : ℝ) + 1) ^ 8) <
      48 * (((N n : ℝ) + 2) ^ 8) *
      (‖thirdFullSpectralVelocityHighRadialApply244 n
          (h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap U)‖ +
        ‖h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap‖ *
          (∫ r in τ n..T, ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume)) ^ 2 := by
  let X : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3
  let G : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3
  let F : H3PhysicalRealFinVectorL2Hilbert →L[ℝ] H3SpectralVelocityState :=
    h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap
  let μ : ℝ := h3PathActualBandRawKineticMass244
    ((n : ℝ) + 1) ((N n : ℝ) + 1)
    (h3AuditActualSpectralVelocityTotal hH3 s)
  let B : ℝ := ‖thirdFullSpectralVelocityHighRadialApply244 n (F U)‖ +
    ‖F‖ * (∫ r in τ n..T, ‖G r‖ ∂volume)
  let D : ℝ :=
    h3PathActualLowRadialDissipation244 ((N n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 s) -
      h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 s)
  rcases hWindow.1.1 with
    ⟨hnN, _, _, hδ, _, hEnd, _, _, _, _, _, hFloor, _⟩
  have htClass : τ n ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 ht.1, ht.2⟩
  have hsClass : s ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le htClass.1 hs.1, lt_of_le_of_lt hs.2 hEnd⟩
  have hsB : s ∈ Set.Ioo b T :=
    ⟨lt_of_lt_of_le ht.1 hs.1, lt_of_le_of_lt hs.2 hEnd⟩
  have hTailInt : IntervalIntegrable G volume (τ n) T := by
    apply hG.mono_set
    intro r hr
    have hr' : r ∈ Set.Icc (τ n) T := by
      simpa only [Set.uIcc_of_le ht.2.le] using hr
    have hr'' : r ∈ Set.Icc b T :=
      ⟨le_trans ht.1.le hr'.1, hr'.2⟩
    simpa only [Set.uIcc_of_le hb.2.le] using hr''
  have hNonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioc (τ n) T)]
        (fun r : ℝ => ‖G r‖) := by
    filter_upwards [] with r
    exact norm_nonneg (G r)
  have hTailMono :
      (∫ r in s..T, ‖G r‖ ∂volume) ≤
        ∫ r in τ n..T, ‖G r‖ ∂volume :=
    intervalIntegral.integral_mono_interval
      hs.1 hsB.2.le le_rfl hNonneg hTailInt.norm
  have hHigh := thirdFullPhysical_terminalHighpass_le_endpointPlusSourceTail244
    hH3 b U hU F n s hsB
  have hHighBound :
      ‖thirdFullSpectralVelocityHighRadialApply244 n (F (X s))‖ ≤ B := by
    exact hHigh.trans (add_le_add_right
      (mul_le_mul_of_nonneg_left hTailMono (norm_nonneg F)) _)
  have hBNonneg : 0 ≤ B :=
    (norm_nonneg _).trans hHighBound
  have hRaw := thirdFullPhysical_actualRawFourierVector_eq_physical244
    hH3 s ⟨lt_trans hClass.terminal_start.1 hsClass.1, hsClass.2⟩
  have hMass := thirdFull_bandRawKineticMass_le_three_highpass244
    n ((N n : ℝ) + 1)
      (h3AuditActualSpectralVelocityTotal hH3 s)
  rw [hRaw] at hMass
  change μ ≤ 3 * ‖thirdFullSpectralVelocityHighRadialApply244 n
      (F (X s))‖ ^ 2 at hMass
  have hSquare :=
    (sq_le_sq₀ (norm_nonneg _) hBNonneg).2 hHighBound
  have hMassBound : μ ≤ 3 * B ^ 2 :=
    hMass.trans (mul_le_mul_of_nonneg_left hSquare (by norm_num))
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
    D μ B η hCritical hFloorD hDiss hMassBound

/-- Same-witness necessary consequence of missing the terminal H³ trace:
the ORIGINAL minimal crossing cascade must be amplified against a single
terminal physical L2 Fourier tail plus the ACTUAL endpoint source L1 tail.
Both error terms vanish, and no endpoint H³ trace is assumed. -/
theorem thirdFullPhysical_noH3Trace_criticalEighth_endpointTailMomentBarrier244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (η : ℝ) (hη : 0 < η) :
    ∃ (U : H3PhysicalRealFinVectorL2Hilbert)
      (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ) (v : ℕ → ℕ),
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
                (h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap U)‖ +
              ‖h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap‖ *
                (∫ r in τ (v k)..T,
                  ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume)) ^ 2) ∧
      Tendsto (fun k : ℕ =>
        ‖thirdFullSpectralVelocityHighRadialApply244 (v k)
          (h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap U)‖ +
        ‖h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap‖ *
          (∫ r in τ (v k)..T,
            ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume))
        atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨τ, N, K, C, δ, v, hMono, hLimit, hWindows, hClock,
      hUniform, hEscape, _hL1⟩ :=
    thirdFullPhysical_noH3Trace_criticalEighth_uniformWindowRawMass244
      hH3 hClass b hb hNoTrace hDInt η hη
  let G : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3
  let F : H3PhysicalRealFinVectorL2Hilbert →L[ℝ] H3SpectralVelocityState :=
    h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap
  have hG : IntervalIntegrable G volume b T :=
    h3Critical_projected_source_integrable_of_finite_dissipation
      hH3 hClass hDInt b hb
  have hb0 : b ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 hb.1, hb.2⟩
  obtain ⟨U, hU⟩ :=
    thirdFullPhysical_terminalProjectedSource_primitive_exact244
      hH3 b hb0 hG
  have hPos (k : ℕ) : 0 < δ (v k) ∧ τ (v k) + δ (v k) < T := by
    rcases (hWindows k).1.1 with
      ⟨_, _, _, hδ, _, hEnd, _, _, _, _, _, _, _⟩
    exact ⟨hδ, hEnd⟩
  have hBefore (k : ℕ) : τ (v k) < T := by
    linarith only [(hPos k).1, (hPos k).2]
  have hAfter : ∀ᶠ k : ℕ in atTop, b < τ (v k) :=
    hLimit.eventually (isOpen_Ioi.mem_nhds hb.2)
  have hAllowed : ∀ᶠ k : ℕ in atTop,
      b ≤ τ (v k) ∧ τ (v k) ≤ T ∧ T ≤ T := by
    filter_upwards [hAfter] with k hk
    exact ⟨hk.le, (hBefore k).le, le_rfl⟩
  have hSourceTail : Tendsto (fun k : ℕ =>
      ∫ r in τ (v k)..T, ‖G r‖ ∂volume)
      atTop (𝓝 (0 : ℝ)) :=
    thirdFull_terminalSourceL1_on_cofinalWindows_tendsto_zero244
      G b T hb.2 hG (fun k => τ (v k)) (fun _ : ℕ => T)
      hLimit tendsto_const_nhds hAllowed
  have hFourierTail : Tendsto (fun k : ℕ =>
      ‖thirdFullSpectralVelocityHighRadialApply244 (v k) (F U)‖)
      atTop (𝓝 (0 : ℝ)) :=
    (thirdFullSpectralVelocityHighRadialApply_norm_tendsto_zero244 (F U)).comp
      hMono.tendsto_atTop
  have hAmplitude : Tendsto (fun k : ℕ =>
      ‖thirdFullSpectralVelocityHighRadialApply244 (v k) (F U)‖ +
        ‖F‖ * (∫ r in τ (v k)..T, ‖G r‖ ∂volume))
      atTop (𝓝 (0 : ℝ)) := by
    have hSum := hFourierTail.add (hSourceTail.const_mul ‖F‖)
    simpa only [mul_zero, add_zero] using hSum
  have hBarrier : ∀ᶠ k : ℕ in atTop,
      ∀ s : ℝ, s ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k)) →
        η * (((v k : ℝ) + 1) ^ 8) <
          48 * (((N (v k) : ℝ) + 2) ^ 8) *
          (‖thirdFullSpectralVelocityHighRadialApply244 (v k) (F U)‖ +
            ‖F‖ * (∫ r in τ (v k)..T, ‖G r‖ ∂volume)) ^ 2 := by
    filter_upwards [hAfter] with k hk
    intro s hs
    have ht : τ (v k) ∈ Set.Ioo b T := ⟨hk, hBefore k⟩
    exact thirdFullPhysical_criticalEighth_window_endpointTailMomentBarrier244
      hH3 hClass η b hb hG U hU τ N K C δ (v k)
      ht (hWindows k) s hs
  exact ⟨U, τ, N, K, C, δ, v, hMono, hLimit,
    hWindows, hClock, hUniform, hEscape, hBarrier, hAmplitude⟩

end
end PrimeTensor.FirstMonomialTriad
