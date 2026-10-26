import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEBoundedSixthClockCompression244
import Mathlib.Tactic

/-!
# Intermittent super-sixth PDE growth on uncompressed cubic clocks

The earlier noncompression theorem requires an eventual positive lower
bound on the cubic terminal lag, while the bounded-rate converse assumes
an eventual sixth-order upper bound. Neither assumption is known to follow
from path admissibility. Their pointwise quantitative alternative admits a
stronger conclusion without either eventual branch assumption:

For every positive geometric threshold η and rate threshold B, *every
sufficiently late witness whose scaled lag is at least η* has anchored
projected-PDE coefficient at least B times the sixth power of the inner
radius. Thus source/spectral coefficient spikes are forced on intermittent
noncompressed witnesses, even when the sequence alternates between branches.

A further corollary says that any sufficiently late witness whose rate is
at most B times the sixth power must have scaled geometric lag below η.
Neither statement excludes terminal geometric compression or asserts
unconditional physical regularity.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Arbitrarily large sixth-order PDE coefficient on *each late index*
whose cubic geometric cap stays above a fixed positive threshold. Unlike
the prior super-sixth theorem, no eventual geometric lower bound is
required. The conclusion is an eventual implication, not an unconditional
limit of the coefficient ratio. -/
theorem h3Path_exactCubicClocks_intermittentNoncompression_forces_sixthRate244
    (v : ℕ → ℕ) (δ b gap Λ Ξ : ℕ → ℝ)
    (hv : StrictMono v)
    (hExact : ∀ k : ℕ,
      δ (v k) = h3PathCubicAnnulusExactPDEWidth244
        (b (v k)) (gap (v k)) (Λ (v k)) (Ξ (v k)))
    (hCollapse : Tendsto (fun k : ℕ =>
      δ (v k) * ((v k : ℝ) + 1) ^ 3) atTop (𝓝 0))
    (hQuarter : ∀ᶠ k : ℕ in atTop,
      ((v k : ℝ) + 1) ^ 3 / 4 ≤ gap (v k))
    (hZPos : ∀ᶠ k : ℕ in atTop,
      0 < Λ (v k) + Ξ (v k) + 1)
    (η B : ℝ) (hη : 0 < η) (hB : 0 < B) :
    ∀ᶠ k : ℕ in atTop,
      (η ≤ ((v k : ℝ) + 1) ^ 3 * (b (v k) / 2) →
        B * ((v k : ℝ) + 1) ^ 6 ≤
          Λ (v k) + Ξ (v k) + 1) := by
  let ε : ℝ := min (η / 2) (1 / (8 * B))
  have hε : 0 < ε := by
    dsimp only [ε]
    apply lt_min
    · linarith only [hη]
    · positivity
  have hSmallLag : ε ≤ η / 2 := by
    dsimp only [ε]
    exact min_le_left _ _
  have hProduct : 8 * ε * B ≤ 1 := by
    have hE : ε ≤ 1 / (8 * B) := by
      dsimp only [ε]
      exact min_le_right _ _
    have hCross := (le_div_iff₀ (by positivity : 0 < 8 * B)).mp hE
    nlinarith only [hCross]
  have hBarrier :=
    h3Path_exactCubicClocks_quarterGap_forces_twoScaleBarrier244
      v δ b gap Λ Ξ hv hExact hCollapse hQuarter hZPos ε hε
  filter_upwards [hBarrier, hZPos] with k hkBarrier hkZ
  intro hkLag
  rcases hkBarrier with hkTime | hkRate
  · have hImpossible : False := by
      linarith only [hkLag, hkTime, hSmallLag, hη]
    exact False.elim hImpossible
  · calc
      B * ((v k : ℝ) + 1) ^ 6 ≤
          B * (8 * ε * (Λ (v k) + Ξ (v k) + 1)) :=
        mul_le_mul_of_nonneg_left hkRate hB.le
      _ = (8 * ε * B) * (Λ (v k) + Ξ (v k) + 1) := by ring
      _ ≤ 1 * (Λ (v k) + Ξ (v k) + 1) :=
        mul_le_mul_of_nonneg_right hProduct hkZ.le
      _ = Λ (v k) + Ξ (v k) + 1 := by ring

/-- Sparse sixth-order bounded-rate indices are forced into geometric
compression: the upper bound need not hold eventually or on an entire
subsequence. The quantified conclusion applies at each sufficiently late
index where the bound happens to hold. -/
theorem h3Path_exactCubicClocks_boundedRateIndices_force_smallLag244
    (v : ℕ → ℕ) (δ b gap Λ Ξ : ℕ → ℝ)
    (hv : StrictMono v)
    (hExact : ∀ k : ℕ,
      δ (v k) = h3PathCubicAnnulusExactPDEWidth244
        (b (v k)) (gap (v k)) (Λ (v k)) (Ξ (v k)))
    (hCollapse : Tendsto (fun k : ℕ =>
      δ (v k) * ((v k : ℝ) + 1) ^ 3) atTop (𝓝 0))
    (hQuarter : ∀ᶠ k : ℕ in atTop,
      ((v k : ℝ) + 1) ^ 3 / 4 ≤ gap (v k))
    (hZPos : ∀ᶠ k : ℕ in atTop,
      0 < Λ (v k) + Ξ (v k) + 1)
    (η B : ℝ) (hη : 0 < η) (hB : 0 ≤ B) :
    ∀ᶠ k : ℕ in atTop,
      (Λ (v k) + Ξ (v k) + 1 ≤
          B * ((v k : ℝ) + 1) ^ 6 →
        ((v k : ℝ) + 1) ^ 3 * (b (v k) / 2) < η) := by
  have hPositive : 0 < B + 1 := by linarith only [hB]
  have hGrowth :=
    h3Path_exactCubicClocks_intermittentNoncompression_forces_sixthRate244
      v δ b gap Λ Ξ hv hExact hCollapse hQuarter hZPos
      η (B + 1) hη hPositive
  filter_upwards [hGrowth] with k hkGrowth
  intro hkRate
  by_contra hkNot
  have hkLag : η ≤ ((v k : ℝ) + 1) ^ 3 * (b (v k) / 2) :=
    le_of_not_gt hkNot
  have hkLower := hkGrowth hkLag
  have hRadius : 0 < ((v k : ℝ) + 1) ^ 6 := by positivity
  nlinarith only [hkLower, hkRate, hRadius]

/-- The actual preterminal Navier–Stokes witnesses admit the intermittent
barrier under the same explicit finite H³-dissipation hypothesis as the
previous clock theorems. The statement does not assume global geometric
noncompression or any growth-rate bound. -/
theorem h3Path_noL2Trace_finiteDissipation_intermittentSixthBarrier244
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
      (∀ η B : ℝ, 0 < η → 0 < B →
        ∀ᶠ k : ℕ in atTop,
          η ≤ ((v k : ℝ) + 1) ^ 3 * (T - τ (v k)) / 4 →
            B * ((v k : ℝ) + 1) ^ 6 ≤
              h3PathCubicAnnulusActualLinearRate244 N K C (v k) +
                h3PathCubicAnnulusActualQuadraticRate244 N C (v k) + 1) := by
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
  refine ⟨τ, N, K, C, δ, v, hv, hCofinal, hSeparate, ?_,
    hSummable, ?_⟩
  · intro k
    rcases hAll (v k) with ⟨_, _, _, _, _, _, _, hg⟩
    exact hg
  · intro η B hη hB
    have hSpike :=
      h3Path_exactCubicClocks_intermittentNoncompression_forces_sixthRate244
        v δ (fun n => (T - τ n) / 2)
        (h3PathCubicAnnulusActualGap244 hH3 τ N)
        (h3PathCubicAnnulusActualLinearRate244 N K C)
        (h3PathCubicAnnulusActualQuadraticRate244 N C)
        hv hExact hCollapse hQuarter hZPos η B hη hB
    filter_upwards [hSpike] with k hk
    intro hkLag
    apply hk
    convert hkLag using 1 <;> ring

end
end PrimeTensor.FirstMonomialTriad
