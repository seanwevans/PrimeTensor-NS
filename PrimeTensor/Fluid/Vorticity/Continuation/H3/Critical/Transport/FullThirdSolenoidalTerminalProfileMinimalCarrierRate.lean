import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileMinimalAttainedWindows
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfilePhysicalRatePolynomial
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-!
# Minimal occupied kinetic shell, attained source peaks, and physical rates

The same pairwise disjoint H3 terminal windows have MINIMAL crossing outer
frequencies, a positive raw-kinetic last shell, and the actual source
maximum as their polynomial PDE coefficient. Thus the source-ceiling
alternative is a literal physical source observation, with no efficiency
assumption. The remaining time compression and outer cutoff alternatives
are explicitly retained; no terminal regularity is deduced.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

/-- On the exact SAME disjoint, summably charged terminal windows from
absence of a strong H3 trace, the late-time endpoint rate obstruction is
an actual projected-source / high-frequency geometric alternative.
Neither physical kinetic L2 nontrace nor positive terminal kinetic mass
is needed. This is not an unconditional H3 terminal trace. -/
theorem thirdFullPhysical_noH3Trace_minimalCarrier_sourceClock_or_physicalRates244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (M : ℕ → ℝ) (hM : ∀ n : ℕ, 0 < M n)
    (hMTop : Tendsto M atTop atTop) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ) (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ k l, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      (∀ k, ThirdFullProfileMinimalAttainedSourceWindow244 hH3 M τ N K C δ (v k)) ∧
      Summable (fun k : ℕ => δ (v k) * (M (v k) / 4)) ∧
      (∀ k : ℕ, ∃ m : ℕ, N (v k) = m + 1 ∧ v k ≤ m ∧
        0 < h3PathActualBandRawKineticMass244
          ((m : ℝ) + 1) ((N (v k) : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) ∧
        (h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) -
          h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))) -
              M (v k) / 2 ≤
          4 * (((N (v k) : ℝ) + 2) ^ 8) *
            h3PathActualBandRawKineticMass244
              ((m : ℝ) + 1) ((N (v k) : ℝ) + 1)
                (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))) ∧
      (∀ k : ℕ, ∃ m : ℕ, v k ≤ m ∧ m < N (v k) ∧
        0 < h3PathActualBandRawKineticMass244
          ((m : ℝ) + 1) ((m : ℝ) + 2)
            (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) ∧
        M (v k) / 2 < ((N (v k) - v k : ℕ) : ℝ) *
          (4 * (((m : ℝ) + 3) ^ 8) *
            h3PathActualBandRawKineticMass244
              ((m : ℝ) + 1) ((m : ℝ) + 2)
                (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))))) ∧
      (∀ᶠ k : ℕ in atTop,
        (T - τ (v k)) * M (v k) < 4 ∨
        M (v k) ^ 2 < 384 * K (v k) * C (v k) *
            (((N (v k) : ℝ) + 2) ^ 5 + ((v k : ℝ) + 2) ^ 5) + 8 ∨
        M (v k) ^ 2 < 576 * C (v k) ^ 2 *
            (((N (v k) : ℝ) + 2) ^ 8 + ((v k : ℝ) + 2) ^ 8) + 8) ∧
      (∀ S : ℝ, 0 ≤ S → ∀ᶠ k : ℕ in atTop,
        (T - τ (v k)) * M (v k) < 4 ∨
        (∃ sSource : ℝ,
          sSource ∈ Set.Icc (τ (v k)) ((τ (v k) + T) / 2) ∧
          S < ‖h3PathActualProjectedMomentumSource244 hH3 sSource‖) ∨
        M (v k) ^ 2 < 8 *
          (S * h3PathFiniteAnnulusPDELinearGain244
              ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) (K (v k)) +
           S ^ 2 * h3PathFiniteAnnulusPDEQuadraticGain244
              ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) + 1)) := by
  obtain ⟨τ, N, K, C, δ, v, hMono, hLimit, hSeparated,
    hWindows, hSum⟩ :=
    thirdFullPhysical_noH3Trace_disjointMinimalAttainedSourceCharges244
      hH3 hClass b hb hNoTrace hDInt M hM
  have hNonneg (k : ℕ) : 0 ≤ δ (v k) * (M (v k) / 4) := by
    rcases (hWindows k).2.1.1 with
      ⟨_, _, _, hδ, _, _, _, _, _, _, _, _, _⟩
    exact mul_nonneg hδ.le (div_nonneg (hM (v k)).le (by norm_num))
  have hSummable : Summable (fun k : ℕ =>
      δ (v k) * (M (v k) / 4)) :=
    summable_of_sum_range_le hNonneg hSum
  have hZero : Tendsto (fun k : ℕ => δ (v k) * (M (v k) / 4))
      atTop (𝓝 (0 : ℝ)) := hSummable.tendsto_atTop_zero
  have hSmall : ∀ᶠ k : ℕ in atTop, δ (v k) * M (v k) < 1 := by
    have hEv : ∀ᶠ k : ℕ in atTop,
        δ (v k) * (M (v k) / 4) < 1 / 4 :=
      hZero.eventually (eventually_lt_nhds (by norm_num))
    filter_upwards [hEv] with k hk
    nlinarith only [hk]
  have hLarge : ∀ᶠ k : ℕ in atTop, 1 ≤ M (v k) :=
    (hMTop.comp hMono.tendsto_atTop).eventually (eventually_ge_atTop 1)
  have hBarrier : ∀ᶠ k : ℕ in atTop,
      (T - τ (v k)) * M (v k) < 4 ∨
      M (v k) ^ 2 < 8 *
        (h3PathFiniteAnnulusPDEVariationCoefficient244
          ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
            (K (v k)) (C (v k)) +
         h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
          ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
            (C (v k)) + 1) := by
    filter_upwards [hSmall, hLarge] with k hSmallK hLargeK
    rcases (hWindows k).2.1.1 with
      ⟨_, hK, hC, _hδ, _hδone, _hEnd, _hBase, _hSource,
        hHeight, hClock, _hBudget, _hFloor, _hCost⟩
    let G : H3SpectralVelocityState :=
      h3AuditActualSpectralVelocityTotal hH3 (τ (v k))
    let B : ℝ :=
      h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1) G -
      h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1) G
    let Λ : ℝ := h3PathFiniteAnnulusPDEVariationCoefficient244
      ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
      (K (v k)) (C (v k))
    let Ξ : ℝ := h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
      ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) (C (v k))
    have hB : M (v k) / 2 < B := by
      simpa only [B, G] using hHeight
    have hΛ : 0 ≤ Λ :=
      h3Path_finiteAnnulusPDEVariationCoefficient_nonneg244
        ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
        (K (v k)) (C (v k)) hK hC
    have hΞ : 0 ≤ Ξ :=
      h3Path_finiteAnnulusPDEAnchoredQuadraticCoefficient_nonneg244
        ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) (C (v k))
    have hExact : δ (v k) = min ((T - τ (v k)) / 4)
        (min (1 : ℝ) ((B - M (v k) / 4) / (2 * (Λ + Ξ + 1)))) := by
      simpa only [thirdFullProfileAnchoredPDEWidth244, B, Λ, Ξ, G]
        using hClock
    have hAlt := thirdFull_exactPDEClock_smallCharge_forces_clockOrQuadraticRate244
      (τ (v k)) T (M (v k)) B Λ Ξ (δ (v k))
      hLargeK hB hΛ hΞ hExact hSmallK
    simpa only [Λ, Ξ] using hAlt
  have hKC (k : ℕ) : 0 ≤ K (v k) ∧ 0 ≤ C (v k) := by
    rcases (hWindows k).2.1.1 with
      ⟨_, hK, hC, _, _, _, _, _, _, _, _, _, _⟩
    exact ⟨hK, hC⟩
  refine ⟨τ, N, K, C, δ, v, hMono, hLimit, hSeparated,
    (fun k => (hWindows k).2), hSummable, ?_, ?_, ?_, ?_⟩
  · intro k
    have ht : τ (v k) ∈ Set.Ioo a T :=
      ⟨lt_trans hb.1 (hWindows k).1.1, (hWindows k).1.2⟩
    have hData := (hWindows k).2.1.1
    rcases hData with
      ⟨hnN, _, _, _, _, _, _, _, hCross, _, _, _, _⟩
    obtain ⟨m, hmN, hnm, _hPositiveDiss, hMass, hOvershoot⟩ :=
      thirdFullPhysical_profileFirstCrossing_lastShellKinetic244
        hH3 hClass (τ (v k)) ht (v k) (N (v k))
        (M (v k)) (hM (v k)) hnN hCross (hWindows k).2.2
    exact ⟨m, hmN, hnm, hMass, hOvershoot⟩
  · intro k
    have ht : τ (v k) ∈ Set.Ioo a T :=
      ⟨lt_trans hb.1 (hWindows k).1.1, (hWindows k).1.2⟩
    have hData := (hWindows k).2.1.1
    rcases hData with
      ⟨hnN, _, _, _, _, _, _, _, hCross, _, _, _, _⟩
    exact thirdFullPhysical_profileFirstCrossing_averagedKineticShell244
      hH3 hClass (τ (v k)) ht (v k) (N (v k))
      (M (v k)) (hM (v k)) hnN hCross
  · filter_upwards [hBarrier] with k hk
    rcases hk with hClock | hRate
    · exact Or.inl hClock
    · have hR : (1 : ℝ) ≤ (v k : ℝ) + 1 := by
        have hn : (0 : ℝ) ≤ (v k : ℝ) := Nat.cast_nonneg _
        linarith only [hn]
      have hQ : (1 : ℝ) ≤ (N (v k) : ℝ) + 1 := by
        have hn : (0 : ℝ) ≤ (N (v k) : ℝ) := Nat.cast_nonneg _
        linarith only [hn]
      have hSplit := thirdFull_quadraticPDESum_forces_quinticOrEighth244
        ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
        (K (v k)) (C (v k)) (M (v k))
        hR hQ (hKC k).1 (hKC k).2 hRate
      have hRewriteR : (((v k : ℝ) + 1) + 1) = (v k : ℝ) + 2 := by ring
      have hRewriteQ : (((N (v k) : ℝ) + 1) + 1) =
          (N (v k) : ℝ) + 2 := by ring
      exact Or.inr (by
        simpa only [hRewriteR, hRewriteQ] using hSplit)
  · intro S hS
    filter_upwards [hBarrier] with k hk
    rcases hk with hClock | hRate
    · exact Or.inl hClock
    · rcases thirdFull_quadraticPDESum_forces_sourceOrSpectralGains244
          ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
          (K (v k)) (C (v k)) S (M (v k))
          (hKC k).1 (hKC k).2 hS hRate with hSourceLarge | hGain
      · obtain ⟨sSource, hsSource, hAttained⟩ := (hWindows k).2.1.2
        exact Or.inr (Or.inl ⟨sSource, hsSource,
          by simpa only [hAttained] using hSourceLarge⟩)
      · exact Or.inr (Or.inr hGain)

end
end PrimeTensor.FirstMonomialTriad
