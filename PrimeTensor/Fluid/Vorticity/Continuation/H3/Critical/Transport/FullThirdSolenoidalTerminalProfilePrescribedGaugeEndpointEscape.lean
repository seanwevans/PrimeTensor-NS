import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileCriticalEighthEndpointSourceTail
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileMinimalAttainedWindows
import Mathlib.Tactic

/-!
# Prescribed-gauge outer-frequency escape from terminal physical momentum

The previous critical-eighth endpoint barrier is not specific to a fixed
polynomial profile. In the no-terminal-H3-trace alternative, the existing
arbitrary-height first-crossing construction accepts the positive profile
`M(n) = H(n)^8` for ANY prescribed frequency gauge `H(n) ≥ 1`.

The physical projected-source Bochner primitive gives one fixed terminal
kinetic state `U` independent of the selected windows. For the genuine
first-crossing annulus and the exact source tail the positive H4 moment obeys

  H(vk)^8 < 48 (N(vk)+2)^8 B(k)^2,
  B(k) = ||P⁺_(vk) Fourier(U)|| + ||Fourier|| ∫_(τ(vk))^T ||G(r)|| dr,
  B(k) -> 0.

Thus the selected outer frequency satisfies `(N(vk)+2)/H(vk) -> +∞`.
The selection depends on H. In particular, selecting H(n)=(n+1)^p
forces polynomially accelerated escape, for each individually chosen p.
No one sequence is claimed to exceed every gauge simultaneously.

This exposes the exact unresolved mechanism: a no-H3-terminal-trace cascade
would have to access arbitrarily distant outer frequencies while still
paying disjoint finite physical viscous charges. It is a necessary
conditional escape statement, not a contradiction or a regularity proof.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- Pure real algebra: the profile height is paid by the eighth Fourier
moment and an actual raw kinetic/source amplitude. -/
theorem thirdFull_profile_eighthMoment_transportAmplifier244
    (Q M D μ B : ℝ)
    (hFloor : M / 4 < D)
    (hDiss : D ≤ 4 * Q ^ 8 * μ)
    (hMass : μ ≤ 3 * B ^ 2) :
    M < 48 * Q ^ 8 * B ^ 2 := by
  have hScaled : 16 * Q ^ 8 * μ ≤ 16 * Q ^ 8 * (3 * B ^ 2) :=
    mul_le_mul_of_nonneg_left hMass (by positivity)
  calc
    M = 4 * (M / 4) := by ring
    _ < 4 * D := mul_lt_mul_of_pos_left hFloor (by norm_num)
    _ ≤ 4 * (4 * Q ^ 8 * μ) :=
      mul_le_mul_of_nonneg_left hDiss (by norm_num)
    _ = 16 * Q ^ 8 * μ := by ring
    _ ≤ 16 * Q ^ 8 * (3 * B ^ 2) := hScaled
    _ = 48 * Q ^ 8 * B ^ 2 := by ring

/-- An actual eighth-moment floor with a vanishing kinetic/source amplitude
forces a radius beyond EVERY fixed multiple of an arbitrary given positive
reference gauge; no rate assumption on the vanishing amplitude is needed. -/
theorem thirdFull_vanishingTail_eighthMoment_forces_gaugeEscape244
    (H Q B : ℕ → ℝ)
    (hH : ∀ k : ℕ, 0 < H k)
    (hQ : ∀ k : ℕ, 0 ≤ Q k)
    (hB : Tendsto B atTop (𝓝 (0 : ℝ)))
    (hBarrier : ∀ᶠ k : ℕ in atTop,
      H k ^ 8 < 48 * (Q k) ^ 8 * (B k) ^ 2) :
    Tendsto (fun k : ℕ => Q k / H k) atTop atTop := by
  have hBSquare : Tendsto (fun k : ℕ => B k ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
    simpa using hB.pow 2
  apply Filter.tendsto_atTop.2
  intro A
  let D : ℝ := max A 0
  have hAD : A ≤ D := le_max_left _ _
  have hD : 0 ≤ D := le_max_right _ _
  have hScaled : Tendsto (fun k : ℕ =>
      48 * D ^ 8 * B k ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hBSquare.const_mul (48 * D ^ 8)
  have hSmall : ∀ᶠ k : ℕ in atTop,
      48 * D ^ 8 * B k ^ 2 < 1 :=
    hScaled.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hBarrier, hSmall] with k hkCost hkSmall
  have hHpos : 0 < H k := hH k
  have hFar : D * H k < Q k := by
    by_contra hNot
    have hNear : Q k ≤ D * H k := le_of_not_gt hNot
    have hPower : (Q k) ^ 8 ≤ (D * H k) ^ 8 :=
      pow_le_pow_left₀ (hQ k) hNear 8
    have hPower' : (Q k) ^ 8 ≤ D ^ 8 * (H k) ^ 8 := by
      simpa only [mul_pow] using hPower
    have hMajor : 48 * (Q k) ^ 8 * (B k) ^ 2 ≤
        (H k) ^ 8 * (48 * D ^ 8 * (B k) ^ 2) := by
      calc
        48 * (Q k) ^ 8 * (B k) ^ 2 =
            (48 * (B k) ^ 2) * (Q k) ^ 8 := by ring
        _ ≤ (48 * (B k) ^ 2) * (D ^ 8 * (H k) ^ 8) :=
          mul_le_mul_of_nonneg_left hPower'
            (mul_nonneg (by norm_num) (sq_nonneg _))
        _ = (H k) ^ 8 * (48 * D ^ 8 * (B k) ^ 2) := by ring
    have hStrict : (H k) ^ 8 * (48 * D ^ 8 * (B k) ^ 2) <
        (H k) ^ 8 := by
      calc
        _ < (H k) ^ 8 * 1 :=
          mul_lt_mul_of_pos_left hkSmall (pow_pos hHpos 8)
        _ = (H k) ^ 8 := mul_one _
    exact (lt_asymm hkCost (hMajor.trans_lt hStrict))
  exact (hAD.trans_lt ((lt_div_iff₀ hHpos).2 hFar)).le

/-- The physical endpoint-tail eighth-moment inequality at an ARBITRARY
positive first-crossing height M, on the same actual PDE persistence window.
Unlike the critical-eighth specialization, no chosen polynomial profile is
built into this statement. -/
theorem thirdFullPhysical_profile_window_endpointTailMomentBarrier244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (M : ℕ → ℝ) (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hG : IntervalIntegrable (h3PathActualProjectedMomentumSource244 hH3)
      volume b T)
    (U : H3PhysicalRealFinVectorL2Hilbert)
    (hU : ∀ t : ℝ, t ∈ Set.Ioo b T →
      h3AuditInitialOldPhysicalHilbertTotal hH3 t +
        ∫ r in t..T, h3PathActualProjectedMomentumSource244 hH3 r ∂volume = U)
    (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ) (n : ℕ)
    (ht : τ n ∈ Set.Ioo b T)
    (hWindow : ThirdFullProfileMinimalAttainedSourceWindow244 hH3
      M τ N K C δ n)
    (s : ℝ) (hs : s ∈ Set.Icc (τ n) (τ n + δ n)) :
    M n <
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
  have hFloorD : M n / 4 < D :=
    hFloor s hs
  change M n <
      48 * (((N n : ℝ) + 2) ^ 8) * B ^ 2
  exact thirdFull_profile_eighthMoment_transportAmplifier244
    ((N n : ℝ) + 2) (M n) D μ B hFloorD hDiss hMassBound


/-- Any prescribed positive frequency gauge can be beaten by the outer
cutoff on a genuine no-terminal-H3-trace minimal first-crossing cascade.
The actual terminal physical state U is fixed; the witnesses depend on H.
The disjoint physical viscous charge, absolute source tail, and eighth
moment inequality all hold on those SAME witnesses. -/
theorem thirdFullPhysical_noH3Trace_prescribedGauge_endpointTailEscape244
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
      (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ) (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ k, ThirdFullProfileMinimalAttainedSourceWindow244 hH3
        (fun n : ℕ => (H n) ^ 8) τ N K C δ (v k)) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m,
          δ (v k) * ((H (v k)) ^ 8 / 4)) ≤
            ∫ r in a..T, velocityH3DissipationAt u r) ∧
      (∀ k : ℕ, ∀ s : ℝ,
        s ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k)) →
          (H (v k)) ^ 8 < 48 * (((N (v k) : ℝ) + 2) ^ 8) *
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
        atTop (𝓝 (0 : ℝ)) ∧
      Tendsto (fun k : ℕ =>
        ((N (v k) : ℝ) + 2) / H (v k)) atTop atTop := by
  let M : ℕ → ℝ := fun n => (H n) ^ 8
  have hM (n : ℕ) : 0 < M n :=
    pow_pos (lt_of_lt_of_le zero_lt_one (hH n)) 8
  obtain ⟨τ, N, K, C, δ, v, hMono, hLimit, _hSeparated,
      hTimeWindows, hCharges⟩ :=
    thirdFullPhysical_noH3Trace_disjointMinimalAttainedSourceCharges244
      hH3 hClass b hb hNoTrace hDInt M hM
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
  have hTime (k : ℕ) : τ (v k) ∈ Set.Ioo b T :=
    (hTimeWindows k).1
  have hWindow (k : ℕ) :
      ThirdFullProfileMinimalAttainedSourceWindow244 hH3 M τ N K C δ (v k) :=
    (hTimeWindows k).2
  have hAllowed : ∀ᶠ k : ℕ in atTop,
      b ≤ τ (v k) ∧ τ (v k) ≤ T ∧ T ≤ T := by
    filter_upwards with k
    exact ⟨(hTime k).1.le, (hTime k).2.le, le_rfl⟩
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
  have hMoment (k : ℕ) (s : ℝ)
      (hs : s ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k))) :
      M (v k) < 48 * (((N (v k) : ℝ) + 2) ^ 8) *
        (‖thirdFullSpectralVelocityHighRadialApply244 (v k) (F U)‖ +
          ‖F‖ * (∫ r in τ (v k)..T, ‖G r‖ ∂volume)) ^ 2 :=
    thirdFullPhysical_profile_window_endpointTailMomentBarrier244
      hH3 hClass M b hb hG U hU τ N K C δ (v k)
      (hTime k) (hWindow k) s hs
  have hPositiveWidth (k : ℕ) : 0 ≤ δ (v k) := by
    rcases (hWindow k).1.1 with
      ⟨_, _, _, hδ, _, _, _, _, _, _, _, _, _⟩
    exact hδ.le
  have hCost : ∀ᶠ k : ℕ in atTop,
      (H (v k)) ^ 8 < 48 * (((N (v k) : ℝ) + 2) ^ 8) *
        (‖thirdFullSpectralVelocityHighRadialApply244 (v k) (F U)‖ +
          ‖F‖ * (∫ r in τ (v k)..T, ‖G r‖ ∂volume)) ^ 2 := by
    filter_upwards with k
    have hs : τ (v k) ∈ Set.Icc
        (τ (v k)) (τ (v k) + δ (v k)) :=
      ⟨le_rfl, le_add_of_nonneg_right (hPositiveWidth k)⟩
    exact hMoment k (τ (v k)) hs
  have hGaugePos (k : ℕ) : 0 < H (v k) :=
    lt_of_lt_of_le zero_lt_one (hH (v k))
  have hOuterPos (k : ℕ) : 0 ≤ (N (v k) : ℝ) + 2 := by positivity
  have hRatio := thirdFull_vanishingTail_eighthMoment_forces_gaugeEscape244
    (fun k : ℕ => H (v k))
    (fun k : ℕ => (N (v k) : ℝ) + 2)
    (fun k : ℕ =>
      ‖thirdFullSpectralVelocityHighRadialApply244 (v k) (F U)‖ +
        ‖F‖ * (∫ r in τ (v k)..T, ‖G r‖ ∂volume))
    hGaugePos hOuterPos hAmplitude hCost
  exact ⟨U, τ, N, K, C, δ, v, hMono, hLimit,
    hWindow, hCharges, hMoment, hAmplitude, hRatio⟩

end
end PrimeTensor.FirstMonomialTriad
