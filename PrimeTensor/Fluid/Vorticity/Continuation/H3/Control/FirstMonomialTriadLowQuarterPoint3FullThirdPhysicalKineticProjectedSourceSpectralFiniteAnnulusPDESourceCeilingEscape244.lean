import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDESourceGainSplit244
import Mathlib.Tactic

/-!
# Intermittent source escape under controlled cutoff amplification

The exact anchored physical PDE coefficient is C*L + C^2*H + 1,
where L,H are nonnegative for the selected physical spectral ceilings.
The existing intermittent-sixth theorem supplies an arbitrarily large
sixth-power lower rate on sufficiently late noncompressed exact clocks.

If the same cutoff gains evaluated at a fixed hypothetical ceiling S
stay bounded by D times the inner sixth power, the source C must exceed S
on those late noncompressed witnesses. Keeping the spectral and source
nonnegativity in the existential witness avoids any unrecorded assumption
about the arbitrary selectors.

The cutoff-gain hypothesis is conditional. No uniform cutoff ceiling,
source bound, or exclusion of geometric compression is asserted.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- A physical sixth-order PDE coefficient cannot be above B*R^6 while
its cutoff gains at a source ceiling S are below D*R^6 (D < B) unless
its actual nonnegative source ceiling C exceeds S. -/
theorem h3Path_sixthPDERate_boundedGain_forces_sourceEscape244
    (R Q K C S D B : ℝ)
    (hR : 0 < R) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hS : 0 ≤ S) (hDB : D < B)
    (hRate : B * R ^ 6 ≤
      h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C +
        h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244 R Q C + 1)
    (hGain :
      S * h3PathFiniteAnnulusPDELinearGain244 R Q K +
        S ^ 2 * h3PathFiniteAnnulusPDEQuadraticGain244 R Q + 1 ≤
          D * R ^ 6) :
    S < C := by
  rcases h3Path_sixthRate_forces_sourceOrCutoffAmplification244
    R Q K C B S hK hC hS hRate with hSource | hCutoff
  · exact hSource
  · exfalso
    have hR6 : 0 < R ^ 6 := pow_pos hR _
    have hImpossible : B * R ^ 6 ≤ D * R ^ 6 :=
      le_trans hCutoff hGain
    have hStrict : D * R ^ 6 < B * R ^ 6 :=
      mul_lt_mul_of_pos_right hDB hR6
    exact (not_le_of_gt hStrict) hImpossible

/-- Transfer the pointwise split to intermittent terminal witnesses.
The lower coefficient barrier is assumed for every positive height B;
it may be supplied directly by the exact-clock intermittent theorem. -/
theorem h3Path_intermittentPDEGainCap_forces_sourceEscape244
    (T : ℝ) (τ : ℕ → ℝ) (N v : ℕ → ℕ)
    (K C : ℕ → ℝ)
    (hNonneg : ∀ k : ℕ, 0 ≤ K (v k) ∧ 0 ≤ C (v k))
    (η : ℝ) (hη : 0 < η)
    (hSpike : ∀ B : ℝ, 0 < B →
      ∀ᶠ k : ℕ in atTop,
        η ≤ ((v k : ℝ) + 1) ^ 3 * (T - τ (v k)) / 4 →
          B * ((v k : ℝ) + 1) ^ 6 ≤
            h3PathCubicAnnulusActualLinearRate244 N K C (v k) +
              h3PathCubicAnnulusActualQuadraticRate244 N C (v k) + 1)
    (S D : ℝ) (hS : 0 ≤ S) (hD : 0 ≤ D)
    (hGain : ∀ᶠ k : ℕ in atTop,
      S * h3PathFiniteAnnulusPDELinearGain244
        ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) (K (v k)) +
      S ^ 2 * h3PathFiniteAnnulusPDEQuadraticGain244
        ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) + 1 ≤
          D * ((v k : ℝ) + 1) ^ 6) :
    ∀ᶠ k : ℕ in atTop,
      η ≤ ((v k : ℝ) + 1) ^ 3 * (T - τ (v k)) / 4 →
        S < C (v k) := by
  have hB : 0 < D + 1 := by linarith only [hD]
  have hBarrier := hSpike (D + 1) hB
  filter_upwards [hBarrier, hGain] with k hkBarrier hkGain
  intro hkLag
  have hRate : (D + 1) * ((v k : ℝ) + 1) ^ 6 ≤
      h3PathFiniteAnnulusPDEVariationCoefficient244
        ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) (K (v k)) (C (v k)) +
      h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
        ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) (C (v k)) + 1 := by
    simpa only [h3PathCubicAnnulusActualLinearRate244,
      h3PathCubicAnnulusActualQuadraticRate244] using hkBarrier hkLag
  exact h3Path_sixthPDERate_boundedGain_forces_sourceEscape244
    ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
    (K (v k)) (C (v k)) S D (D + 1)
    (by positivity) (hNonneg k).1 (hNonneg k).2 hS
    (by linarith) hRate hkGain

/-- Without any cutoff-gain hypothesis, a bounded source on a late
noncompressed witness forces its cutoff/spectral gain at that source
ceiling to exceed every fixed sixth-order threshold. -/
theorem h3Path_intermittentBoundedSource_forces_cutoffGainGrowth244
    (T : ℝ) (τ : ℕ → ℝ) (N v : ℕ → ℕ)
    (K C : ℕ → ℝ)
    (hNonneg : ∀ k : ℕ, 0 ≤ K (v k) ∧ 0 ≤ C (v k))
    (η : ℝ) (hη : 0 < η)
    (hSpike : ∀ B : ℝ, 0 < B →
      ∀ᶠ k : ℕ in atTop,
        η ≤ ((v k : ℝ) + 1) ^ 3 * (T - τ (v k)) / 4 →
          B * ((v k : ℝ) + 1) ^ 6 ≤
            h3PathCubicAnnulusActualLinearRate244 N K C (v k) +
              h3PathCubicAnnulusActualQuadraticRate244 N C (v k) + 1)
    (S B : ℝ) (hS : 0 ≤ S) (hB : 0 < B) :
    ∀ᶠ k : ℕ in atTop,
      η ≤ ((v k : ℝ) + 1) ^ 3 * (T - τ (v k)) / 4 →
        C (v k) ≤ S →
          B * ((v k : ℝ) + 1) ^ 6 ≤
            S * h3PathFiniteAnnulusPDELinearGain244
              ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) (K (v k)) +
            S ^ 2 * h3PathFiniteAnnulusPDEQuadraticGain244
              ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) + 1 := by
  filter_upwards [hSpike B hB] with k hkSpike
  intro hkLag hkCeiling
  have hRate : B * ((v k : ℝ) + 1) ^ 6 ≤
      h3PathFiniteAnnulusPDEVariationCoefficient244
        ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) (K (v k)) (C (v k)) +
      h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
        ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) (C (v k)) + 1 := by
    simpa only [h3PathCubicAnnulusActualLinearRate244,
      h3PathCubicAnnulusActualQuadraticRate244] using hkSpike hkLag
  rcases h3Path_sixthRate_forces_sourceOrCutoffAmplification244
    ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
    (K (v k)) (C (v k)) B S
    (hNonneg k).1 (hNonneg k).2 hS hRate with hEscape | hGain
  · exact False.elim ((not_lt_of_ge hkCeiling) hEscape)
  · exact hGain

/-- Physical source escape on all late noncompressed exact cubic clocks,
conditional on an explicit sixth-order cutoff-gain bound at any chosen
source ceiling S. The same selected witnesses have their actual
nonnegative K,C and their original quarter-cubic annular surplus. -/
theorem h3Path_noL2Trace_finiteDissipation_intermitSourceEscape_of_gainBound244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ)
        (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k : ℕ => τ (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      (∀ k : ℕ,
        ((v k : ℝ) + 1) ^ 3 / 4 <
          h3PathCubicAnnulusActualGap244 hH3 τ N (v k)) ∧
      Summable (fun k : ℕ =>
        δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ∧
      (∀ k : ℕ, 0 ≤ K (v k) ∧ 0 ≤ C (v k)) ∧
      (∀ η S B : ℝ, 0 < η → 0 ≤ S → 0 < B →
        ∀ᶠ k : ℕ in atTop,
          η ≤ ((v k : ℝ) + 1) ^ 3 * (T - τ (v k)) / 4 →
            C (v k) ≤ S →
              B * ((v k : ℝ) + 1) ^ 6 ≤
                S * h3PathFiniteAnnulusPDELinearGain244
                  ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) (K (v k)) +
                S ^ 2 * h3PathFiniteAnnulusPDEQuadraticGain244
                  ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) + 1) ∧
      (∀ η S D : ℝ, 0 < η → 0 ≤ S → 0 ≤ D →
        (∀ᶠ k : ℕ in atTop,
          S * h3PathFiniteAnnulusPDELinearGain244
            ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) (K (v k)) +
          S ^ 2 * h3PathFiniteAnnulusPDEQuadraticGain244
            ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) + 1 ≤
              D * ((v k : ℝ) + 1) ^ 6) →
        ∀ᶠ k : ℕ in atTop,
          η ≤ ((v k : ℝ) + 1) ^ 3 * (T - τ (v k)) / 4 →
            S < C (v k)) := by
  obtain ⟨τ, N, K, C, δ, hTime, hLimit, hAll⟩ :=
    h3Path_noL2Trace_forces_quarterGapExactPDEClocks244
      hH3 hClass hMass hNoTrace
  have hδ (n : ℕ) : 0 < δ n := by
    rcases hAll n with ⟨_, _, _, hp, _, _, _, _⟩
    exact hp
  have hEnd (n : ℕ) : τ n + δ n < T := by
    rcases hAll n with ⟨_, _, _, _, he, _, _, _⟩
    exact he
  obtain ⟨v, hv, hCofinal, hSeparate⟩ :=
    h3Path_exists_strictMono_pairwiseSeparatedTerminalWindows244
      τ δ T hLimit hδ hEnd
  let M : ℝ := ∫ r in a..T, velocityH3DissipationAt u r
  have hBound : ∀ m : ℕ,
      (∑ k ∈ Finset.range m,
        δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ≤ M := by
    have hFloor (k : ℕ) (r : ℝ)
        (hr : r ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k))) :
        ((v k : ℝ) + 1) ^ 3 / 2 ≤ velocityH3DissipationAt u r := by
      rcases hAll (v k) with ⟨_, _, _, _, hb', _, hAnnulus, _⟩
      have hrClass : r ∈ Set.Ioo a T :=
        ⟨lt_of_lt_of_le (hTime (v k)).1 hr.1,
          lt_of_le_of_lt hr.2 hb'⟩
      exact (hAnnulus r hr).le.trans
        (h3Path_actualFiniteAnnulusDissipation_le_fullAt244
          hH3 hClass r hrClass ((v k : ℝ) + 1)
            ((N (v k) : ℝ) + 1))
    have hSum := h3Path_disjointNonnegativeWindows_finiteHeightCost_le244
      (velocityH3DissipationAt u) a T
      (fun k => τ (v k)) (fun k => δ (v k))
      (fun k => ((v k : ℝ) + 1) ^ 3 / 2)
      hClass.terminal_start.2.le
      (fun r => velocityH3DissipationAt_nonneg u r)
      hDInt
      (fun k => (hTime (v k)).1.le)
      (fun k => (hδ (v k)).le)
      (fun k => (hEnd (v k)).le)
      (fun k => (hSeparate k (k + 1) (Nat.lt_succ_self k)).le)
      hFloor
    simpa only [M] using hSum
  have hΛ (n : ℕ) :
      0 ≤ h3PathCubicAnnulusActualLinearRate244 N K C n := by
    unfold h3PathCubicAnnulusActualLinearRate244
    rcases hAll n with ⟨_, hK, hC, _, _, _, _, _⟩
    exact h3Path_finiteAnnulusPDEVariationCoefficient_nonneg244
      ((n : ℝ) + 1) ((N n : ℝ) + 1) (K n) (C n) hK hC
  have hΞ (n : ℕ) :
      0 ≤ h3PathCubicAnnulusActualQuadraticRate244 N C n := by
    unfold h3PathCubicAnnulusActualQuadraticRate244
    exact h3Path_finiteAnnulusPDEAnchoredQuadraticCoefficient_nonneg244
      ((n : ℝ) + 1) ((N n : ℝ) + 1) (C n)
  have hExact (k : ℕ) :
      δ (v k) = h3PathCubicAnnulusExactPDEWidth244
        ((T - τ (v k)) / 2)
        (h3PathCubicAnnulusActualGap244 hH3 τ N (v k))
        (h3PathCubicAnnulusActualLinearRate244 N K C (v k))
        (h3PathCubicAnnulusActualQuadraticRate244 N C (v k)) := by
    exact (hAll (v k)).2.2.2.2.2.1
  obtain ⟨hSummable, hCollapse, _⟩ :=
    h3Path_exactCubicClocks_finiteCosts_forces_alternative244
      v δ (fun n => (T - τ n) / 2)
      (h3PathCubicAnnulusActualGap244 hH3 τ N)
      (h3PathCubicAnnulusActualLinearRate244 N K C)
      (h3PathCubicAnnulusActualQuadraticRate244 N C)
      M hv (fun n => (hδ n).le) hΛ hΞ
      (fun n => (hAll n).2.2.2.2.2.1) hBound
  have hQuarter : ∀ᶠ k : ℕ in atTop,
      ((v k : ℝ) + 1) ^ 3 / 4 ≤
        h3PathCubicAnnulusActualGap244 hH3 τ N (v k) := by
    apply Filter.Eventually.of_forall
    intro k
    rcases hAll (v k) with ⟨_, _, _, _, _, _, _, hg⟩
    exact hg.le
  have hZPos : ∀ᶠ k : ℕ in atTop,
      0 < h3PathCubicAnnulusActualLinearRate244 N K C (v k) +
        h3PathCubicAnnulusActualQuadraticRate244 N C (v k) + 1 := by
    apply Filter.Eventually.of_forall
    intro k
    have hL := hΛ (v k)
    have hQ := hΞ (v k)
    linarith only [hL, hQ]
  have hPositive : ∀ k : ℕ, 0 ≤ K (v k) ∧ 0 ≤ C (v k) := by
    intro k
    rcases hAll (v k) with ⟨_, hK, hC, _, _, _, _, _⟩
    exact ⟨hK, hC⟩
  have hSpike (η : ℝ) (hη : 0 < η) (B : ℝ) (hB : 0 < B) :
      ∀ᶠ k : ℕ in atTop,
        η ≤ ((v k : ℝ) + 1) ^ 3 * (T - τ (v k)) / 4 →
          B * ((v k : ℝ) + 1) ^ 6 ≤
            h3PathCubicAnnulusActualLinearRate244 N K C (v k) +
              h3PathCubicAnnulusActualQuadraticRate244 N C (v k) + 1 := by
    have hSpike' :=
      h3Path_exactCubicClocks_intermittentNoncompression_forces_sixthRate244
        v δ (fun n => (T - τ n) / 2)
        (h3PathCubicAnnulusActualGap244 hH3 τ N)
        (h3PathCubicAnnulusActualLinearRate244 N K C)
        (h3PathCubicAnnulusActualQuadraticRate244 N C)
        hv hExact hCollapse hQuarter hZPos η B hη hB
    filter_upwards [hSpike'] with k hk
    intro hkLag
    apply hk
    convert hkLag using 1 <;> ring
  refine ⟨τ, N, K, C, δ, v, hv, hCofinal, hSeparate, ?_,
    hSummable, hPositive, ?_, ?_⟩
  · intro k
    rcases hAll (v k) with ⟨_, _, _, _, _, _, _, hg⟩
    exact hg
  · intro η S B hη hS hB
    exact h3Path_intermittentBoundedSource_forces_cutoffGainGrowth244
      T τ N v K C hPositive η hη
      (fun B' hB' => hSpike η hη B' hB') S B hS hB
  · intro η S D hη hS hD hGain
    exact h3Path_intermittentPDEGainCap_forces_sourceEscape244
      T τ N v K C hPositive η hη
      (fun B hB => hSpike η hη B hB) S D hS hD hGain

end
end PrimeTensor.FirstMonomialTriad
