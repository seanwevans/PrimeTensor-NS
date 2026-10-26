import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEQuantitativeGapGrowth244
import Mathlib.Tactic

/-!
# Sixth-scale coefficient bounds force cubic terminal-time compression

On the disjoint exact PDE windows, vanishing cubic-weighted costs and the
quantitative quarter-cubic annular gap give a two-way asymptotic obstruction:
either the cubic-scaled geometric clock is small or the normalized projected
PDE coefficient is large. This module proves the converse to the previously
conditional super-sixth theorem: an eventual *upper* bound of order R^6 on
the actual coefficient forces cubic terminal-time compression to zero.

The physical theorem retains the same actual cofinal annuli, exact widths,
quarter-gap selection and disjoint-window dissipation assumptions. It does
not assert the rate bound as a consequence of admissibility, and it makes
no terminal-regularity claim.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- A quarter-cubic annular gap transfers a small normalized PDE cap to a
lower bound on the sixth-power projected-PDE coefficient. -/
theorem h3Path_quarterCubicGap_smallPDECap_forces_sixthRate244
    (R gap Z ε : ℝ)
    (hR : 0 < R) (hZ : 0 < Z)
    (hGap : R ^ 3 / 4 ≤ gap)
    (hCap : R ^ 3 * (gap / (2 * Z)) ≤ ε) :
    R ^ 6 ≤ 8 * ε * Z := by
  have hR3 : 0 ≤ R ^ 3 := pow_nonneg hR.le _
  have hGapMult : R ^ 3 * (R ^ 3 / 4) ≤ R ^ 3 * gap :=
    mul_le_mul_of_nonneg_left hGap hR3
  have hSixth : R ^ 6 / 4 ≤ R ^ 3 * gap := by
    nlinarith only [hGapMult]
  have hCap' : R ^ 3 * gap / (2 * Z) ≤ ε := by
    calc
      R ^ 3 * gap / (2 * Z) = R ^ 3 * (gap / (2 * Z)) := by ring
      _ ≤ ε := hCap
  have hScaled : R ^ 3 * gap ≤ ε * (2 * Z) :=
    (div_le_iff₀ (by positivity : 0 < 2 * Z)).mp hCap'
  calc
    R ^ 6 = 4 * (R ^ 6 / 4) := by ring
    _ ≤ 4 * (R ^ 3 * gap) :=
      mul_le_mul_of_nonneg_left hSixth (by norm_num)
    _ ≤ 4 * (ε * (2 * Z)) :=
      mul_le_mul_of_nonneg_left hScaled (by norm_num)
    _ = 8 * ε * Z := by ring

/-- For every positive tolerance the exact cubic clocks choose one of two
explicitly scaled obstructions: geometric compression, or a sixth-power
lower bound for the physical PDE coefficient. No boundedness assumption. -/
theorem h3Path_exactCubicClocks_quarterGap_forces_twoScaleBarrier244
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
      0 < Λ (v k) + Ξ (v k) + 1) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
      ((v k : ℝ) + 1) ^ 3 * (b (v k) / 2) ≤ ε ∨
      ((v k : ℝ) + 1) ^ 6 ≤
        8 * ε * (Λ (v k) + Ξ (v k) + 1) := by
  intro ε hε
  have hAlt := h3Path_exactCubicClocks_vanishingCapAlternative244
    v δ b gap Λ Ξ hv hExact hCollapse ε hε
  filter_upwards [hAlt, hQuarter, hZPos] with k hkAlt hkGap hkZ
  rcases hkAlt with hTime | hCap
  · exact Or.inl hTime
  · right
    apply h3Path_quarterCubicGap_smallPDECap_forces_sixthRate244
      ((v k : ℝ) + 1) (gap (v k))
      (Λ (v k) + Ξ (v k) + 1) ε
      (by positivity) hkZ hkGap hCap

/-- A uniform sixth-order *upper* rate bound forces the alternative's
geometric clock to converge to zero. This is the complementary conclusion
to super-sixth growth under geometric noncompression. -/
theorem h3Path_exactCubicClocks_boundedSixthRate_forces_geometricCollapse244
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
    (hb : ∀ᶠ k : ℕ in atTop, 0 ≤ b (v k))
    (B : ℝ) (hB : 0 < B)
    (hRate : ∀ᶠ k : ℕ in atTop,
      Λ (v k) + Ξ (v k) + 1 ≤ B * ((v k : ℝ) + 1) ^ 6) :
    Tendsto (fun k : ℕ =>
      ((v k : ℝ) + 1) ^ 3 * (b (v k) / 2)) atTop (𝓝 0) := by
  have hBarrier := h3Path_exactCubicClocks_quarterGap_forces_twoScaleBarrier244
    v δ b gap Λ Ξ hv hExact hCollapse hQuarter hZPos
  have hUpper : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
      ((v k : ℝ) + 1) ^ 3 * (b (v k) / 2) ≤ ε := by
    intro ε hε
    let E : ℝ := min ε (1 / (16 * B))
    have hE : 0 < E := by
      dsimp only [E]
      exact lt_min hε (by positivity)
    have hEbound : E ≤ ε := by
      dsimp only [E]
      exact min_le_left _ _
    have hEBound : E ≤ 1 / (16 * B) := by
      dsimp only [E]
      exact min_le_right _ _
    have hProduct : E * (16 * B) ≤ 1 :=
      (le_div_iff₀ (by positivity : 0 < 16 * B)).mp hEBound
    have hHalf : 8 * E * B ≤ 1 / 2 := by
      nlinarith only [hProduct]
    have hAlt := hBarrier E hE
    filter_upwards [hAlt, hRate] with k hkAlt hkRate
    rcases hkAlt with hkTime | hkPDE
    · exact le_trans hkTime hEbound
    · exfalso
      let R : ℝ := (v k : ℝ) + 1
      let Z : ℝ := Λ (v k) + Ξ (v k) + 1
      have hRpos : 0 < R := by dsimp only [R]; positivity
      have hR6 : 0 < R ^ 6 := pow_pos hRpos _
      have hBound : Z ≤ B * R ^ 6 := by simpa only [R, Z] using hkRate
      have hBad : R ^ 6 ≤ 8 * E * Z := by simpa only [R, Z] using hkPDE
      have hNonneg : 0 ≤ 8 * E := by positivity
      have hSmall : 8 * E * Z ≤ (1 / 2) * R ^ 6 := by
        calc
          8 * E * Z ≤ 8 * E * (B * R ^ 6) :=
            mul_le_mul_of_nonneg_left hBound hNonneg
          _ = (8 * E * B) * R ^ 6 := by ring
          _ ≤ (1 / 2) * R ^ 6 :=
            mul_le_mul_of_nonneg_right hHalf hR6.le
      linarith only [hBad, hSmall, hR6]
  apply tendsto_order.2
  constructor
  · intro c hc
    filter_upwards [hb] with k hbk
    have hGeom : 0 ≤ ((v k : ℝ) + 1) ^ 3 * (b (v k) / 2) :=
      mul_nonneg (by positivity) (div_nonneg hbk (by norm_num))
    exact lt_of_lt_of_le hc hGeom
  · intro c hc
    have hc2 : 0 < c / 2 := by linarith only [hc]
    filter_upwards [hUpper (c / 2) hc2] with k hk
    linarith only [hk, hc]

/-- In the physical no-terminal-L²-trace branch, the *same* separated
exact cubic witnesses support the conditional converse: a uniform O(R^6)
projected-PDE variation rate forces (v(k)+1)^3*(T-τ(v(k))) -> 0.
The rate bound and full H³ terminal dissipation integrability are explicit
additional assumptions, not conclusions of preterminal admissibility. -/
theorem h3Path_noL2Trace_finiteDissipation_boundedSixthRate_forces_terminalCompression244
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
      (∀ B : ℝ, 0 < B →
        (∀ᶠ k : ℕ in atTop,
          h3PathCubicAnnulusActualLinearRate244 N K C (v k) +
            h3PathCubicAnnulusActualQuadraticRate244 N C (v k) + 1 ≤
              B * ((v k : ℝ) + 1) ^ 6) →
        Tendsto (fun k : ℕ =>
          ((v k : ℝ) + 1) ^ 3 * (T - τ (v k))) atTop (𝓝 0)) := by
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
  have hb : ∀ᶠ k : ℕ in atTop,
      0 ≤ (T - τ (v k)) / 2 := by
    apply Filter.Eventually.of_forall
    intro k
    have ht := (hTime (v k)).2
    apply div_nonneg
    · exact sub_nonneg.mpr ht.le
    · norm_num
  refine ⟨τ, N, K, C, δ, v, hv, hCofinal, hSeparate, ?_,
    hSummable, ?_⟩
  · intro k
    rcases hAll (v k) with ⟨_, _, _, _, _, _, _, hg⟩
    exact hg
  · intro B hB hRate
    have hClock :=
      h3Path_exactCubicClocks_boundedSixthRate_forces_geometricCollapse244
        v δ (fun n => (T - τ n) / 2)
        (h3PathCubicAnnulusActualGap244 hH3 τ N)
        (h3PathCubicAnnulusActualLinearRate244 N K C)
        (h3PathCubicAnnulusActualQuadraticRate244 N C)
        hv hExact hCollapse hQuarter hZPos hb B hB hRate
    have hScale := hClock.const_mul (4 : ℝ)
    have hEq : (fun k : ℕ =>
        ((v k : ℝ) + 1) ^ 3 * (T - τ (v k))) =
        (fun k : ℕ => 4 *
          (((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2))) := by
      funext k
      ring
    rw [hEq]
    simpa only [mul_zero] using hScale

end
end PrimeTensor.FirstMonomialTriad
