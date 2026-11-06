import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfilePrescribedGaugeViscousPeakFiniteBandPersistence
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessEndpointViscousAnnularPDEPersistence
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessAttainedPhysicalPDEFactorGate
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# An explicit projected-Navier--Stokes clock for late viscous spikes

The last prescribed-gauge theorem forces an actual late full-H³ viscous
spike and captures it by a finite radial cutoff, but obtains its persistence
width only by continuity. Here the existing physical-PDE gradient variation
bound supplies an EXPLICIT, positive right-hand width in terms of the
attained source and weighted spectral-state maxima on the following strict
half-terminal interval.

Let V = H(vk)^4 and P = 168 (N(vk)+2)^4 ||Fourier|| C₀ (T-mk).
On the delayed viscous branch, V < P D_full(rk), rk in (mk,T). Capture
V/P below a finite low-radial cutoff J, and put A=V/(2P). With attained
strict-time maxima K and C and the existing exact physical Fourier-PDE
variation coefficient

  Λ = 6 (J+2)^2 K sqrt(3 W₃(J+1)) C,
  W₃(ρ) = h3TerminalRadialSobolevWeightSquareCeiling ρ,

the following clock is certified on the SAME delayed physical time tail:

  η = min ((T-r)/4) (A/(2(Λ+1))) > 0,
  A < D_low,J(s) <= D_full(s)  for all s in [r,r+η],
  η A <= integral_m^T D_full(s) ds.

The coefficient depends on the *actual attained* physical maxima and the
selected cutoff; it is not claimed uniformly bounded. The old minimal
first-crossing windows, disjoint viscous costs, and prescribed-gauge escape
remain unchanged. This proves a rate-dependent cost, not regularity.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- The exact low-radial projected-PDE variation rate, with finite radial
cutoff J and attained physical source/state norm ceilings K,C. -/
noncomputable def thirdFullLateViscousLowRadialPDERate244
    (J : ℕ) (K C : ℝ) : ℝ :=
  6 * (((J : ℝ) + 2) ^ 2) * K *
    Real.sqrt (3 * h3TerminalRadialSobolevWeightSquareCeiling ((J : ℝ) + 1)) * C

/-- Upgrade the late-spike finite radial capture to an EXACT physical-PDE
persistence clock. The maxima K,C are real attained values on the strict
compact interval [r, r+(T-r)/2]; the resulting real integral is paid by
the same physical terminal dissipation tail that produced the spike. -/
theorem thirdFullPhysical_lateLowRadialSpike_explicitPDEClock244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (m r P V : ℝ) (J : ℕ)
    (hm : m ∈ Set.Ioo a T) (hr : r ∈ Set.Ioo m T)
    (hP : 0 < P) (hV : 0 < V)
    (hPeak : V < P * h3PathActualLowRadialDissipation244 ((J : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 r)) :
    ∃ sSource sState η : ℝ,
      sSource ∈ Set.Icc r (r + (T - r) / 2) ∧
      sState ∈ Set.Icc r (r + (T - r) / 2) ∧
      η = min ((T - r) / 4)
        ((V / (2 * P)) /
          (2 * (thirdFullLateViscousLowRadialPDERate244 J
            ‖h3AuditActualSpectralVelocityTotal hH3 sState‖
            ‖h3PathActualProjectedMomentumSource244 hH3 sSource‖ + 1))) ∧
      0 < η ∧ r + η < T ∧
      (∀ s : ℝ, s ∈ Set.Icc r (r + η) →
        V / (2 * P) < h3PathActualLowRadialDissipation244 ((J : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 s) ∧
        V / (2 * P) < velocityH3DissipationAt u s) ∧
      η * (V / (2 * P)) ≤
        ∫ s in m..T, velocityH3DissipationAt u s ∂volume := by
  let D : ℝ → ℝ := velocityH3DissipationAt u
  let d : ℝ := (T - r) / 2
  let A : ℝ := V / (2 * P)
  have hrClass : r ∈ Set.Ioo a T := ⟨lt_trans hm.1 hr.1, hr.2⟩
  have hr0 : 0 < r := lt_trans hClass.terminal_start.1 hrClass.1
  have hd : 0 < d := by dsimp only [d]; linarith only [hr.2]
  have hEndD : r + d < T := by dsimp only [d]; linarith only [hr.2]
  obtain ⟨sSource, sState, hsSource, hsState, hMax⟩ :=
    h3Critical_actualSourceSpectral_attainedCompactMaxima
      hH3 r d hr0 hd hEndD
  let K : ℝ := ‖h3AuditActualSpectralVelocityTotal hH3 sState‖
  let C : ℝ := ‖h3PathActualProjectedMomentumSource244 hH3 sSource‖
  let Λ : ℝ := thirdFullLateViscousLowRadialPDERate244 J K C
  have hK : 0 ≤ K := norm_nonneg _
  have hC : 0 ≤ C := norm_nonneg _
  have hΛ : 0 ≤ Λ := by
    dsimp only [Λ, thirdFullLateViscousLowRadialPDERate244]
    positivity
  have hA : 0 < A := by dsimp only [A]; positivity
  have hDouble : 2 * A = V / P := by
    dsimp only [A]
    field_simp [ne_of_gt hP]
    <;> ring
  have hTop : V / P <
      h3PathActualLowRadialDissipation244 ((J : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 r) := by
    apply (div_lt_iff₀ hP).2
    simpa only [mul_comm] using hPeak
  obtain ⟨η, hη, hηHalf, hηEq, hRate⟩ :=
    h3Critical_scalar_annularPDE_positivePersistenceRadius
      A Λ d hA hΛ hd
  have hηLe : η ≤ d := by linarith only [hηHalf, hd]
  have hEnd : r + η < T := by
    dsimp only [d] at hηHalf
    linarith only [hηHalf, hr.2]
  have hExact : η = min ((T - r) / 4) (A / (2 * (Λ + 1))) := by
    have hFirst : d / 2 = (T - r) / 4 := by
      dsimp only [d]
      ring
    simpa only [hFirst] using hηEq
  have hLocal (s : ℝ) (hs : s ∈ Set.Icc r (r + η)) :
      A < h3PathActualLowRadialDissipation244 ((J : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 s) ∧
      A < D s := by
    have hsClass : s ∈ Set.Ioo a T :=
      ⟨lt_of_lt_of_le hrClass.1 hs.1, lt_of_le_of_lt hs.2 hEnd⟩
    have hs0 : s ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 hsClass.1, hsClass.2⟩
    have hSub (x : ℝ) (hx : x ∈ Set.Icc r s) :
        x ∈ Set.Icc r (r + d) :=
      ⟨hx.1, le_trans hx.2 (le_trans hs.2 (add_le_add_right hηLe r))⟩
    have hCoords (x : ℝ) (hx : x ∈ Set.Icc r (r + d))
        (j : Fin 3) :
        ‖(h3AuditActualSpectralVelocityTotal hH3 x) j‖ ≤ K := by
      exact (norm_le_pi_norm (h3AuditActualSpectralVelocityTotal hH3 x) j).trans
        (hMax x hx).2
    have hDiff :=
      h3Path_actualLowRadialDissipationVariation_le_PDECeiling244
        hH3 ((J : ℝ) + 1) K (by positivity) hK r s C
        ⟨hr0, hr.2⟩ hs0 hs.1
        (hCoords r ⟨le_rfl, le_add_of_nonneg_right hd.le⟩)
        (hCoords s ⟨hs.1, le_trans hs.2 (add_le_add_right hηLe r)⟩)
        (fun x hx => (hMax x (hSub x hx)).1)
    have hDiffRate :
        |h3PathActualLowRadialDissipation244 ((J : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 r) -
          h3PathActualLowRadialDissipation244 ((J : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s)| ≤
          Λ * (s - r) := by
      calc
        _ ≤ 6 * (((J : ℝ) + 1) + 1) ^ 2 * K *
          Real.sqrt (3 * h3TerminalRadialSobolevWeightSquareCeiling ((J : ℝ) + 1)) *
          (C * (s - r)) := hDiff
        _ = Λ * (s - r) := by
          dsimp only [Λ, thirdFullLateViscousLowRadialPDERate244]
          ring
    have hErr :
        h3PathActualLowRadialDissipation244 ((J : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 r) -
          h3PathActualLowRadialDissipation244 ((J : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s) ≤
          Λ * (s - r) :=
      (le_abs_self _).trans hDiffRate
    have hSpan : s - r ≤ η := by linarith only [hs.2]
    have hBound : Λ * (s - r) ≤ Λ * η :=
      mul_le_mul_of_nonneg_left hSpan hΛ
    have hTop2 : 2 * A <
        h3PathActualLowRadialDissipation244 ((J : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 r) := by
      rw [hDouble]
      exact hTop
    have hLow : A < h3PathActualLowRadialDissipation244 ((J : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 s) := by
      linarith only [hTop2, hErr, hBound, hRate, hA]
    have hPartition := h3Path_actualRadialDissipation_partition244
      hH3 hClass s hsClass ((J : ℝ) + 1)
    have hHigh : 0 ≤ h3PathActualHighRadialDissipation244 ((J : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 s) := by
      unfold h3PathActualHighRadialDissipation244
      apply integral_nonneg
      intro ξ
      exact h3TerminalSpectralDissipationSingleDensity_nonneg
        (h3AuditActualSpectralVelocityTotal hH3 s) ξ
    exact ⟨hLow, by dsimp only [D]; linarith only [hLow, hPartition, hHigh]⟩
  have hDtail : IntervalIntegrable D volume m T := by
    apply hDInt.mono_set
    intro x hx
    have hx' : x ∈ Set.Icc m T := by
      simpa only [Set.uIcc_of_le hm.2.le] using hx
    have hx'' : x ∈ Set.Icc a T := ⟨hm.1.le.trans hx'.1, hx'.2⟩
    simpa only [Set.uIcc_of_le hClass.terminal_start.2.le] using hx''
  have hDwindow : IntervalIntegrable D volume r (r + η) := by
    apply hDInt.mono_set
    intro x hx
    have hx' : x ∈ Set.Icc r (r + η) := by
      simpa only [Set.uIcc_of_le (le_add_of_nonneg_right hη.le)] using hx
    have hx'' : x ∈ Set.Icc a T :=
      ⟨hrClass.1.le.trans hx'.1, hx'.2.trans hEnd.le⟩
    simpa only [Set.uIcc_of_le hClass.terminal_start.2.le] using hx''
  have hWindowCharge : η * A ≤ ∫ s in r..(r + η), D s ∂volume := by
    have hIntegral :
        (∫ _s in r..(r + η), A ∂volume) ≤
          ∫ s in r..(r + η), D s ∂volume := by
      apply intervalIntegral.integral_mono_on
        (le_add_of_nonneg_right hη.le)
        intervalIntegrable_const hDwindow
      intro s hs
      exact (hLocal s hs).2.le
    calc
      η * A = ∫ _s in r..(r + η), A ∂volume := by
        simp [mul_comm] <;> ring
      _ ≤ ∫ s in r..(r + η), D s ∂volume := hIntegral
  have hNonnegative : 0 ≤ᵐ[volume.restrict (Set.Ioc m T)] D := by
    filter_upwards [] with x
    exact velocityH3DissipationAt_nonneg u x
  have hTailCharge :
      (∫ s in r..(r + η), D s ∂volume) ≤
        ∫ s in m..T, D s ∂volume :=
    intervalIntegral.integral_mono_interval
      hr.1.le (le_add_of_nonneg_right hη.le) hEnd.le hNonnegative hDtail
  refine ⟨sSource, sState, η, ?_, ?_, ?_, hη, hEnd, ?_, ?_⟩
  · simpa only [d] using hsSource
  · simpa only [d] using hsState
  · simpa only [A, Λ, K, C] using hExact
  · intro s hs
    simpa only [A, D] using hLocal s hs
  · simpa only [A] using hWindowCharge.trans hTailCharge


/-- The exact gauge-dependent minimal annulus witnesses retain their
physical Fourier/source/kinetic alternatives. On the remaining late-viscous
branch, a finite low-radial cutoff now has an EXPLICIT physical-PDE clock,
computed from the attained strict-time source and spectral maxima. Its
integrated floor is bounded by the already-vanishing terminal viscous tail.
No uniform bound on the cutoff, maxima, or inverse rate is inserted. -/
theorem thirdFullPhysical_noH3Trace_prescribedGauge_lateExplicitPDEClock244
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
      (∀ j : ℕ,
        (∑ k ∈ Finset.range j,
          δ (v k) * ((H (v k)) ^ 8 / 4)) ≤
            ∫ s in a..T, velocityH3DissipationAt u s) ∧
      Tendsto (fun k : ℕ =>
        ((N (v k) : ℝ) + 2) / H (v k)) atTop atTop ∧
      (∀ᶠ k : ℕ in atTop,
        let t := τ (v k)
        let m := (t + T) / 2
        let Q := (N (v k) : ℝ) + 2
        let F := h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap
        let C₀ := 3 + h3AuditInitialLerayEnergyCoefficient
        let E₀ := 1 + 6 * velocityH3Energy0At u b
        let P := 168 * Q ^ 4 * (‖F‖ * C₀) * (T - m)
        (H (v k)) ^ 4 < 14 * Q ^ 4 *
          ‖thirdFullSpectralVelocityHighRadialApply244 (v k) (F U)‖ ∨
        (∃ r : ℝ, r ∈ Set.Icc t m ∧
          (H (v k)) ^ 4 < 28 * Q ^ 4 *
            (‖F‖ * ((m - t) *
              ‖h3PathActualProjectedMomentumSource244 hH3 r‖))) ∨
        (H (v k)) ^ 4 < 56 * Q ^ 4 *
          (‖F‖ * C₀ * ((T - m) * E₀)) ∨
        (∃ (r : ℝ) (J : ℕ) (sSource sState η : ℝ),
          r ∈ Set.Ioo m T ∧ 0 < P ∧
          sSource ∈ Set.Icc r (r + (T - r) / 2) ∧
          sState ∈ Set.Icc r (r + (T - r) / 2) ∧
          η = min ((T - r) / 4)
            (((H (v k)) ^ 4 / (2 * P)) /
              (2 * (thirdFullLateViscousLowRadialPDERate244 J
                ‖h3AuditActualSpectralVelocityTotal hH3 sState‖
                ‖h3PathActualProjectedMomentumSource244 hH3 sSource‖ + 1))) ∧
          0 < η ∧ r + η < T ∧
          (∀ s : ℝ, s ∈ Set.Icc r (r + η) →
            (H (v k)) ^ 4 / (2 * P) <
              h3PathActualLowRadialDissipation244 ((J : ℝ) + 1)
                (h3AuditActualSpectralVelocityTotal hH3 s) ∧
            (H (v k)) ^ 4 / (2 * P) <
              velocityH3DissipationAt u s) ∧
          η * ((H (v k)) ^ 4 / (2 * P)) ≤
            ∫ s in m..T, velocityH3DissipationAt u s ∂volume)) ∧
      Tendsto (fun k : ℕ =>
        ∫ s in ((τ (v k) + T) / 2)..T,
          velocityH3DissipationAt u s ∂volume)
        atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨U, τ, N, K, C, δ, v, hMono, hLimit,
      hWindows, hCharges, hEscape, hOld, hViscousTail⟩ :=
    thirdFullPhysical_noH3Trace_prescribedGauge_lateFiniteBandCharge244
      hH3 hClass b hb hNoTrace hDInt H hH
  let F : H3PhysicalRealFinVectorL2Hilbert →L[ℝ] H3SpectralVelocityState :=
    h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap
  let C₀ : ℝ := 3 + h3AuditInitialLerayEnergyCoefficient
  have hAfter : ∀ᶠ k : ℕ in atTop, b < τ (v k) :=
    hLimit.eventually (isOpen_Ioi.mem_nhds hb.2)
  have hNew : ∀ᶠ k : ℕ in atTop,
      let t := τ (v k)
      let m := (t + T) / 2
      let Q := (N (v k) : ℝ) + 2
      let F := h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap
      let C₀ := 3 + h3AuditInitialLerayEnergyCoefficient
      let E₀ := 1 + 6 * velocityH3Energy0At u b
      let P := 168 * Q ^ 4 * (‖F‖ * C₀) * (T - m)
      (H (v k)) ^ 4 < 14 * Q ^ 4 *
        ‖thirdFullSpectralVelocityHighRadialApply244 (v k) (F U)‖ ∨
      (∃ r : ℝ, r ∈ Set.Icc t m ∧
        (H (v k)) ^ 4 < 28 * Q ^ 4 *
          (‖F‖ * ((m - t) *
            ‖h3PathActualProjectedMomentumSource244 hH3 r‖))) ∨
      (H (v k)) ^ 4 < 56 * Q ^ 4 *
        (‖F‖ * C₀ * ((T - m) * E₀)) ∨
      (∃ (r : ℝ) (J : ℕ) (sSource sState η : ℝ),
        r ∈ Set.Ioo m T ∧ 0 < P ∧
        sSource ∈ Set.Icc r (r + (T - r) / 2) ∧
        sState ∈ Set.Icc r (r + (T - r) / 2) ∧
        η = min ((T - r) / 4)
          (((H (v k)) ^ 4 / (2 * P)) /
            (2 * (thirdFullLateViscousLowRadialPDERate244 J
              ‖h3AuditActualSpectralVelocityTotal hH3 sState‖
              ‖h3PathActualProjectedMomentumSource244 hH3 sSource‖ + 1))) ∧
        0 < η ∧ r + η < T ∧
        (∀ s : ℝ, s ∈ Set.Icc r (r + η) →
          (H (v k)) ^ 4 / (2 * P) <
            h3PathActualLowRadialDissipation244 ((J : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 s) ∧
          (H (v k)) ^ 4 / (2 * P) <
            velocityH3DissipationAt u s) ∧
        η * ((H (v k)) ^ 4 / (2 * P)) ≤
          ∫ s in m..T, velocityH3DissipationAt u s ∂volume) := by
    filter_upwards [hOld, hAfter] with k hkOld hkAfter
    dsimp only at hkOld ⊢
    let t : ℝ := τ (v k)
    let m : ℝ := (t + T) / 2
    let Q : ℝ := (N (v k) : ℝ) + 2
    let P : ℝ := 168 * Q ^ 4 * (‖F‖ * C₀) * (T - m)
    rcases hkOld with hCarrier | hSource | hClock |
        ⟨r, J, η₀, hr, hη₀, _hEnd₀, hP, hFloor, _hCost⟩
    · exact Or.inl hCarrier
    · exact Or.inr (Or.inl hSource)
    · exact Or.inr (Or.inr (Or.inl hClock))
    · right; right; right
      have hEnd : t < T := by
        rcases (hWindows k).1.1 with
          ⟨_, _, _, hδ, _, hBefore, _, _, _, _, _, _, _⟩
        dsimp only [t]
        linarith only [hδ, hBefore]
      have hm : m ∈ Set.Ioo a T := by
        dsimp only [m, t]
        constructor <;> linarith only [hb.1, hkAfter, hEnd]
      have hV : 0 < (H (v k)) ^ 4 :=
        pow_pos (lt_of_lt_of_le zero_lt_one (hH (v k))) 4
      have hStart : r ∈ Set.Icc r (r + η₀) :=
        ⟨le_rfl, le_add_of_nonneg_right hη₀.le⟩
      have hLow : (H (v k)) ^ 4 <
          P * h3PathActualLowRadialDissipation244 ((J : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 r) :=
        (hFloor r hStart).1
      obtain ⟨sSource, sState, η, hsSource, hsState,
          hηEq, hη, hηEnd, hNewFloor, hNewCharge⟩ :=
        thirdFullPhysical_lateLowRadialSpike_explicitPDEClock244
          hH3 hClass hDInt m r P ((H (v k)) ^ 4) J
          hm hr hP hV hLow
      exact ⟨r, J, sSource, sState, η, hr, hP,
        hsSource, hsState, hηEq, hη, hηEnd, hNewFloor, hNewCharge⟩
  exact ⟨U, τ, N, K, C, δ, v, hMono, hLimit,
    hWindows, hCharges, hEscape, hNew, hViscousTail⟩

end
end PrimeTensor.FirstMonomialTriad
