import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileConstructiveCriticalEighthEscape
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-!
# Critical-eighth viscous clock and attained physical-source amplification

The disjoint actual H³ dissipation charges of the constructive critical-eighth
minimal-crossing cascade are summable. Since the constructed height satisfies
M_η(n) ≥ η (n+1)^8, these charges force the *physical widths* to obey

  δ_(v k) (v k + 1)^8 → 0.

On exactly the same selected source windows, the physical PDE source maximum
C_(v k) is attained. For any fixed D ≥ 0 and any ε > 0, eventually either

  δ_(v k) C_(v k) < ε,

or the actual attained source norm exceeds D (v k + 1)^8. In particular,
a persistent positive attained source action is possible only if the actual
physical projected-source peaks eventually beat EVERY fixed eighth-power
threshold. No artificial source rate or new compactness hypothesis is used.

This is a necessary dynamical alternative in the no-H³-terminal-trace
branch, not a contradiction or a regularity proof.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

/-- Summability, not just termwise decay: the exact eighth-power clock
is charged by the finite disjoint physical H³ dissipation budget. -/
theorem thirdFull_criticalEighth_summableCharge_forces_summableClock244
    (R H δ : ℕ → ℝ) (η : ℝ) (hη : 0 < η)
    (hδ : ∀ k : ℕ, 0 ≤ δ k)
    (hHeight : ∀ k : ℕ, η * (R k) ^ 8 ≤ H k)
    (hCharge : Summable (fun k : ℕ => δ k * (H k / 4))) :
    Summable (fun k : ℕ => δ k * (R k) ^ 8) := by
  have hη4 : 0 < η / 4 := by positivity
  have hNonneg (k : ℕ) : 0 ≤ δ k * (R k) ^ 8 :=
    mul_nonneg (hδ k) (by positivity)
  have hUpper (k : ℕ) :
      (η / 4) * (δ k * (R k) ^ 8) ≤ δ k * (H k / 4) := by
    calc
      (η / 4) * (δ k * (R k) ^ 8) =
          δ k * ((η * (R k) ^ 8) / 4) := by ring
      _ ≤ δ k * (H k / 4) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (hHeight k) (by norm_num))
          (hδ k)
  have hCompare (k : ℕ) :
      δ k * (R k) ^ 8 ≤ (δ k * (H k / 4)) / (η / 4) := by
    apply (le_div_iff₀ hη4).2
    calc
      (δ k * (R k) ^ 8) * (η / 4) =
          (η / 4) * (δ k * (R k) ^ 8) := by ring
      _ ≤ δ k * (H k / 4) := hUpper k
  exact (hCharge.div_const (η / 4)).of_nonneg_of_le hNonneg hCompare

/-- In particular, the actual natural eighth-order frequency clock tends
to zero on all disjoint selected windows, with no new rate assumption. -/
theorem thirdFull_criticalEighth_summableCharge_forces_clock244
    (R H δ : ℕ → ℝ) (η : ℝ) (hη : 0 < η)
    (hδ : ∀ k : ℕ, 0 ≤ δ k)
    (hHeight : ∀ k : ℕ, η * (R k) ^ 8 ≤ H k)
    (hCharge : Summable (fun k : ℕ => δ k * (H k / 4))) :
    Tendsto (fun k : ℕ => δ k * (R k) ^ 8)
      atTop (𝓝 (0 : ℝ)) :=
  (thirdFull_criticalEighth_summableCharge_forces_summableClock244
    R H δ η hη hδ hHeight hCharge).tendsto_atTop_zero

/-- If the critical-eighth viscous clock collapses, every late window has
small peak-times-width action or a source peak beyond the prescribed eighth
power threshold. This is a pointwise alternative for each fixed D and ε. -/
theorem thirdFull_criticalEighth_clock_sourceAction_or_largePeak244
    (R δ C : ℕ → ℝ) (hδ : ∀ k : ℕ, 0 ≤ δ k)
    (hClock : Tendsto (fun k : ℕ => δ k * (R k) ^ 8)
      atTop (𝓝 (0 : ℝ)))
    (D ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      C k * δ k < ε ∨ D * (R k) ^ 8 < C k := by
  have hScaled : Tendsto (fun k : ℕ =>
      D * (δ k * (R k) ^ 8)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hClock.const_mul D
  have hSmall : ∀ᶠ k : ℕ in atTop,
      D * (δ k * (R k) ^ 8) < ε :=
    hScaled.eventually (eventually_lt_nhds hε)
  filter_upwards [hSmall] with k hk
  by_cases hPeak : D * (R k) ^ 8 < C k
  · exact Or.inr hPeak
  · left
    have hBound : C k ≤ D * (R k) ^ 8 := le_of_not_gt hPeak
    calc
      C k * δ k ≤ (D * (R k) ^ 8) * δ k :=
        mul_le_mul_of_nonneg_right hBound (hδ k)
      _ = D * (δ k * (R k) ^ 8) := by ring
      _ < ε := hk

/-- Persistently nontrivial peak-times-width action entails source peak
amplification beyond every fixed eighth-order radial multiple. -/
theorem thirdFull_criticalEighth_persistentAction_forces_peakEscape244
    (R δ C : ℕ → ℝ) (hδ : ∀ k : ℕ, 0 ≤ δ k)
    (hClock : Tendsto (fun k : ℕ => δ k * (R k) ^ 8)
      atTop (𝓝 (0 : ℝ)))
    (ε : ℝ) (hε : 0 < ε)
    (hPersistent : ∀ᶠ k : ℕ in atTop, ε ≤ C k * δ k) :
    ∀ D : ℝ, ∀ᶠ k : ℕ in atTop, D * (R k) ^ 8 < C k := by
  intro D
  have hAlt := thirdFull_criticalEighth_clock_sourceAction_or_largePeak244
    R δ C hδ hClock D ε hε
  filter_upwards [hAlt, hPersistent] with k hk hAction
  rcases hk with hSmall | hLarge
  · exact False.elim ((not_lt_of_ge hAction) hSmall)
  · exact hLarge

/-- Concrete Navier--Stokes necessary alternative on the SAME disjoint
minimal-crossing windows, keeping the actual attained projected-source
maximum, full H³ disjoint dissipation charge, and raw L² carrier escape.
No prescribed height profile or assumed PDE source bound is introduced. -/
theorem thirdFullPhysical_noH3Trace_criticalEighthSourceClock_or_peak244
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
      (∀ k l, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      (∀ k, ThirdFullProfileMinimalAttainedSourceWindow244
        hH3 (thirdFullConstructiveCriticalEighthProfile244 η)
        τ N K C δ (v k)) ∧
      Summable (fun k : ℕ => δ (v k) *
        (thirdFullConstructiveCriticalEighthProfile244 η (v k) / 4)) ∧
      Summable (fun k : ℕ => δ (v k) * (((v k : ℝ) + 1) ^ 8)) ∧
      Tendsto (fun k : ℕ => δ (v k) * (((v k : ℝ) + 1) ^ 8))
        atTop (𝓝 (0 : ℝ)) ∧
      (∀ ε : ℝ, 0 < ε → ∀ D : ℝ, 0 ≤ D → ∀ᶠ k : ℕ in atTop,
        C (v k) * δ (v k) < ε ∨
        ∃ sSource : ℝ,
          sSource ∈ Set.Icc (τ (v k)) ((τ (v k) + T) / 2) ∧
          D * (((v k : ℝ) + 1) ^ 8) <
            ‖h3PathActualProjectedMomentumSource244 hH3 sSource‖) ∧
      Tendsto (fun k : ℕ =>
        h3PathActualBandRawKineticMass244
          ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))))
        atTop (𝓝 (0 : ℝ)) ∧
      Tendsto (fun k : ℕ =>
        ((N (v k) : ℝ) + 2) / ((v k : ℝ) + 1)) atTop atTop ∧
      (∀ᶠ k : ℕ in atTop,
        ‖h3AuditInitialOldPhysicalHilbertTotal hH3
            (τ (v k) + δ (v k)) -
          h3AuditInitialOldPhysicalHilbertTotal hH3 (τ (v k))‖ ≤
        C (v k) * δ (v k)) := by
  obtain ⟨τ, N, K, C, δ, v, hMono, hLimit, hSeparate,
      hWindows, hSummable, hMass, hEscape, hAction,
      _hRates, _hSourceAlt⟩ :=
    thirdFullPhysical_noH3Trace_constructiveCriticalEighthSourceEscape244
      hH3 hClass b hb hNoTrace hDInt η hη
  have hδ (k : ℕ) : 0 ≤ δ (v k) := by
    rcases (hWindows k).1.1 with
      ⟨_, _, _, hWidthPos, _, _, _, _, _, _, _, _, _⟩
    exact hWidthPos.le
  have hHeight (k : ℕ) :
      η * (((v k : ℝ) + 1) ^ 8) ≤
        thirdFullConstructiveCriticalEighthProfile244 η (v k) :=
    thirdFullConstructiveCriticalEighthProfile_lower244 η (v k)
  have hClockSummable :=
    thirdFull_criticalEighth_summableCharge_forces_summableClock244
      (fun k : ℕ => (v k : ℝ) + 1)
      (fun k : ℕ => thirdFullConstructiveCriticalEighthProfile244 η (v k))
      (fun k : ℕ => δ (v k)) η hη hδ hHeight hSummable
  have hClock : Tendsto (fun k : ℕ =>
      δ (v k) * (((v k : ℝ) + 1) ^ 8)) atTop (𝓝 (0 : ℝ)) :=
    hClockSummable.tendsto_atTop_zero
  have hSource (ε : ℝ) (hε : 0 < ε) (D : ℝ) (_hD : 0 ≤ D) :
      ∀ᶠ k : ℕ in atTop,
        C (v k) * δ (v k) < ε ∨
        ∃ sSource : ℝ,
          sSource ∈ Set.Icc (τ (v k)) ((τ (v k) + T) / 2) ∧
          D * (((v k : ℝ) + 1) ^ 8) <
            ‖h3PathActualProjectedMomentumSource244 hH3 sSource‖ := by
    have hAlt := thirdFull_criticalEighth_clock_sourceAction_or_largePeak244
      (fun k : ℕ => (v k : ℝ) + 1)
      (fun k : ℕ => δ (v k))
      (fun k : ℕ => C (v k)) hδ hClock D ε hε
    filter_upwards [hAlt] with k hk
    rcases hk with hSmall | hLarge
    · exact Or.inl hSmall
    · obtain ⟨sSource, hsSource, hAttained⟩ := (hWindows k).1.2
      exact Or.inr ⟨sSource, hsSource, by simpa only [hAttained] using hLarge⟩
  exact ⟨τ, N, K, C, δ, v, hMono, hLimit, hSeparate,
    hWindows, hSummable, hClockSummable, hClock, hSource, hMass, hEscape, hAction⟩

end
end PrimeTensor.FirstMonomialTriad
