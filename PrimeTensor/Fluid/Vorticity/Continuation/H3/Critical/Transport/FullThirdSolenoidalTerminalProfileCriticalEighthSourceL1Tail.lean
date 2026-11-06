import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileCriticalEighthSourceClock
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.FiniteDissipationTerminalTrace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Absolute projected-source action on the actual cofinal critical-eighth windows

The previous peak theorem extracts source maxima C on the half-terminal interval
and an eighth-power dissipation-clock constraint. Peak-times-width is only an
upper bound for the source integral; it need not be an actual L¹ action.

Finite full H³ dissipation already gives *Bochner L¹ integrability* of the
physical projected-momentum source up to T. Applying continuity of the scalar
norm-integral primitive at the terminal endpoint yields a stronger statement:
the **actual, nonnegative integral of the source norm** over ANY cofinal
shrinking physical window tends to zero. This holds on the minimal first-
crossing windows of the critical-eighth construction, even when the attained
source maximum grows faster than the eighth power.

This rules out treating a large pointwise source peak as positive source
transport. It does not bound the selected peak times the selected width, and
it does not imply an H³ terminal trace or continuation.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

/-- Absolute-continuity principle for a Bochner-integrable physical source:
its *norm* has vanishing integral on windows whose two endpoints converge to
the same terminal endpoint. The interval is not replaced by an attained
source maximum. -/
theorem thirdFull_terminalSourceL1_on_cofinalWindows_tendsto_zero244
    (G : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (b T : ℝ) (hb : b < T)
    (hG : IntervalIntegrable G volume b T)
    (τ σ : ℕ → ℝ)
    (hτ : Tendsto τ atTop (𝓝 T))
    (hσ : Tendsto σ atTop (𝓝 T))
    (hWindow : ∀ᶠ k : ℕ in atTop,
      b ≤ τ k ∧ τ k ≤ σ k ∧ σ k ≤ T) :
    Tendsto (fun k : ℕ => ∫ s in τ k..σ k, ‖G s‖ ∂volume)
      atTop (𝓝 (0 : ℝ)) := by
  let f : ℝ → ℝ := fun s => ‖G s‖
  have hf : IntervalIntegrable f volume b T := hG.norm
  let P : ℝ → ℝ := fun t => ∫ s in b..t, f s ∂volume
  have hPContinuous : ContinuousOn P (Set.Icc b T) := by
    simpa only [P, Set.uIcc_of_le hb.le] using
      (intervalIntegral.continuousOn_primitive_interval'
        hf left_mem_uIcc)
  have hτIcc : ∀ᶠ k : ℕ in atTop, τ k ∈ Set.Icc b T := by
    filter_upwards [hWindow] with k hk
    exact ⟨hk.1, (hk.2.1).trans hk.2.2⟩
  have hσIcc : ∀ᶠ k : ℕ in atTop, σ k ∈ Set.Icc b T := by
    filter_upwards [hWindow] with k hk
    exact ⟨hk.1.trans hk.2.1, hk.2.2⟩
  have hPEnd : Tendsto P (𝓝[Set.Icc b T] T) (𝓝 (P T)) :=
    hPContinuous T ⟨hb.le, le_rfl⟩
  have hPτ : Tendsto (fun k : ℕ => P (τ k)) atTop (𝓝 (P T)) :=
    hPEnd.comp (tendsto_nhdsWithin_iff.mpr ⟨hτ, hτIcc⟩)
  have hPσ : Tendsto (fun k : ℕ => P (σ k)) atTop (𝓝 (P T)) :=
    hPEnd.comp (tendsto_nhdsWithin_iff.mpr ⟨hσ, hσIcc⟩)
  have hDifference : Tendsto (fun k : ℕ => P (σ k) - P (τ k))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self] using hPσ.sub hPτ
  have hIntervalIdentity :
      (fun k : ℕ => ∫ s in τ k..σ k, ‖G s‖ ∂volume) =ᶠ[atTop]
        (fun k : ℕ => P (σ k) - P (τ k)) := by
    filter_upwards [hWindow] with k hk
    have hLeft : IntervalIntegrable f volume b (τ k) := by
      apply hf.mono_set
      intro s hs
      have hs' : s ∈ Set.Icc b (τ k) := by
        simpa only [Set.uIcc_of_le hk.1] using hs
      have hs'' : s ∈ Set.Icc b T :=
        ⟨hs'.1, hs'.2.trans (hk.2.1.trans hk.2.2)⟩
      simpa only [Set.uIcc_of_le hb.le] using hs''
    have hRight : IntervalIntegrable f volume (τ k) (σ k) := by
      apply hf.mono_set
      intro s hs
      have hs' : s ∈ Set.Icc (τ k) (σ k) := by
        simpa only [Set.uIcc_of_le hk.2.1] using hs
      have hs'' : s ∈ Set.Icc b T :=
        ⟨hk.1.trans hs'.1, hs'.2.trans hk.2.2⟩
      simpa only [Set.uIcc_of_le hb.le] using hs''
    have hAdd := intervalIntegral.integral_add_adjacent_intervals hLeft hRight
    change (∫ s in τ k..σ k, f s ∂volume) =
      (∫ s in b..σ k, f s ∂volume) -
      (∫ s in b..τ k, f s ∂volume)
    linarith only [hAdd]
  exact hDifference.congr' hIntervalIdentity.symm

/-- On the genuine minimal-first-crossing physical PDE windows, finite H³
dissipation controls absolute *integrated* source transport, not just a
signed momentum increment or a source peak times the clock. -/
theorem thirdFullPhysical_criticalEighth_minimalWindows_sourceL1_tendsto_zero244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (M : ℕ → ℝ) (τ : ℕ → ℝ) (N : ℕ → ℕ)
    (K C δ : ℕ → ℝ) (v : ℕ → ℕ)
    (hLimit : Tendsto (fun k : ℕ => τ (v k)) atTop (𝓝 T))
    (hWindows : ∀ k : ℕ,
      ThirdFullProfileMinimalAttainedSourceWindow244 hH3 M τ N K C δ (v k)) :
    Tendsto (fun k : ℕ =>
      ∫ s in τ (v k)..(τ (v k) + δ (v k)),
        ‖h3PathActualProjectedMomentumSource244 hH3 s‖ ∂volume)
      atTop (𝓝 (0 : ℝ)) := by
  let G : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3
  have hG : IntervalIntegrable G volume b T :=
    h3Critical_projected_source_integrable_of_finite_dissipation
      hH3 hClass hDInt b hb
  have hPos (k : ℕ) : 0 < δ (v k) ∧ τ (v k) + δ (v k) < T := by
    rcases (hWindows k).1.1 with
      ⟨_, _, _, hδ, _, hEnd, _, _, _, _, _, _, _⟩
    exact ⟨hδ, hEnd⟩
  have hGap : Tendsto (fun k : ℕ => T - τ (v k))
      atTop (𝓝 (0 : ℝ)) := by
    have hConst : Tendsto (fun _ : ℕ => (T : ℝ)) atTop (𝓝 T) :=
      tendsto_const_nhds
    simpa only [sub_self] using hConst.sub hLimit
  have hδZero : Tendsto (fun k : ℕ => δ (v k))
      atTop (𝓝 (0 : ℝ)) := by
    apply squeeze_zero'
      (Filter.Eventually.of_forall (fun k => (hPos k).1.le))
      (Filter.Eventually.of_forall (fun k => by
        have hk := (hPos k).2
        linarith only [hk]))
      hGap
  have hEndT : Tendsto (fun k : ℕ => τ (v k) + δ (v k))
      atTop (𝓝 T) := by
    simpa only [add_zero] using hLimit.add hδZero
  have hAfter : ∀ᶠ k : ℕ in atTop, b ≤ τ (v k) := by
    filter_upwards [hLimit.eventually (isOpen_Ioi.mem_nhds hb.2)] with k hk
    exact hk.le
  have hWindow : ∀ᶠ k : ℕ in atTop,
      b ≤ τ (v k) ∧ τ (v k) ≤ τ (v k) + δ (v k) ∧
        τ (v k) + δ (v k) ≤ T := by
    filter_upwards [hAfter] with k hk
    exact ⟨hk, by linarith only [(hPos k).1], (hPos k).2.le⟩
  exact thirdFull_terminalSourceL1_on_cofinalWindows_tendsto_zero244
    G b T hb.2 hG (fun k => τ (v k))
    (fun k => τ (v k) + δ (v k)) hLimit hEndT hWindow

/-- The constructed no-H³-trace critical-eighth cascade simultaneously
has carrier escape, a summable eighth-order clock, the attained source peak
alternative, and **vanishing absolute L¹ projected-source action** on the
very same minimal-crossing physical intervals. The latter is not a bound on
C_k δ_k, since source maxima can be narrow and large. -/
theorem thirdFullPhysical_noH3Trace_criticalEighth_sourceL1Tail244
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
      Tendsto (fun k : ℕ =>
        ∫ s in τ (v k)..(τ (v k) + δ (v k)),
          ‖h3PathActualProjectedMomentumSource244 hH3 s‖ ∂volume)
        atTop (𝓝 (0 : ℝ)) ∧
      Tendsto (fun k : ℕ =>
        h3PathActualBandRawKineticMass244
          ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))))
        atTop (𝓝 (0 : ℝ)) ∧
      Tendsto (fun k : ℕ =>
        ((N (v k) : ℝ) + 2) / ((v k : ℝ) + 1)) atTop atTop ∧
      (∀ ε : ℝ, 0 < ε → ∀ D : ℝ, 0 ≤ D → ∀ᶠ k : ℕ in atTop,
        C (v k) * δ (v k) < ε ∨
        ∃ sSource : ℝ,
          sSource ∈ Set.Icc (τ (v k)) ((τ (v k) + T) / 2) ∧
          D * (((v k : ℝ) + 1) ^ 8) <
            ‖h3PathActualProjectedMomentumSource244 hH3 sSource‖) := by
  obtain ⟨τ, N, K, C, δ, v, hMono, hLimit, _hSeparated,
      hWindows, _hCharge, hClockSummable, _hClock, hSourcePeak,
      hMass, hOuterEscape, _hMomentum⟩ :=
    thirdFullPhysical_noH3Trace_criticalEighthSourceClock_or_peak244
      hH3 hClass b hb hNoTrace hDInt η hη
  have hL1 :=
    thirdFullPhysical_criticalEighth_minimalWindows_sourceL1_tendsto_zero244
      hH3 hClass hDInt b hb
      (thirdFullConstructiveCriticalEighthProfile244 η)
      τ N K C δ v hLimit hWindows
  exact ⟨τ, N, K, C, δ, v,
    hMono, hLimit, hWindows, hClockSummable, hL1,
    hMass, hOuterEscape, hSourcePeak⟩

end
end PrimeTensor.FirstMonomialTriad
