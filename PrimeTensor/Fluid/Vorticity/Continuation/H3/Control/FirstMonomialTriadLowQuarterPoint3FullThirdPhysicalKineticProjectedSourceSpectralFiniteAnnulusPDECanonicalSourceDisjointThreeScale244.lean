import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalSourceQuadraticSharpClock244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEQuadraticSharpClock244
import Mathlib.Tactic

/-!
# Disjoint canonical-source quadratic-sharp physical PDE clocks

The strict interior projected-source maximum is constructed *before* the
persistence clock. We now select disjoint windows from those very same
canonical clocks, charge their cubic annular floors to finite full H³
dissipation, and recover the exact three-cap PDE obstruction.

In particular C(n) is exactly the attained physical L² projected-source
maximum on [τ n, (τ n+T)/2], rather than an arbitrary bound. Its divergence
therefore implies actual physical source peaks in those half-terminal windows.
No source divergence or PDE continuation result is inferred unconditionally.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- An attained nonnegative source ceiling cannot diverge in square without
real source observations crossing every fixed threshold in the same windows. -/
theorem h3Path_attainedSourceSquareEscape_forces_windowPeaks244
    (C a b : ℕ → ℝ) (p : ℝ → ℝ)
    (hC : ∀ k, 0 ≤ C k)
    (hPeak : ∀ k, ∃ s : ℝ, s ∈ Set.Icc (a k) (b k) ∧ p s = C k)
    (hSquare : Tendsto (fun k : ℕ => C k ^ 2) atTop atTop)
    (M : ℝ) :
    ∀ᶠ k : ℕ in atTop, ∃ s : ℝ,
      s ∈ Set.Icc (a k) (b k) ∧ M ≤ p s := by
  have hAbs := h3Path_sourceCeilingSquareEscape_forces_absEscape244 C hSquare
  have hLarge : ∀ᶠ k : ℕ in atTop, M ≤ |C k| :=
    hAbs.eventually (eventually_ge_atTop M)
  filter_upwards [hLarge] with k hk
  obtain ⟨s, hs, hEq⟩ := hPeak k
  refine ⟨s, hs, ?_⟩
  rw [hEq]
  simpa only [abs_of_nonneg (hC k)] using hk

/-- The no-terminal-trace first-crossing annuli now carry disjoint exact
quadratic-sharp clocks with CANONICAL attained projected-source maxima.
Finite full H³ dissipation makes the cubic window costs summable. The
three-scale PDE alternative is proved on the SAME canonical witnesses.
If the canonical coefficient square diverges, actual projected-source
norms reach every threshold at physical times in the half-terminal windows.
The last implication has an explicit antecedent. -/
theorem h3Path_noL2Trace_finiteDissipation_canonicalSourceDisjointThreeScale244
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
      (∀ n : ℕ, τ n ∈ Set.Ioo a T) ∧
      (∀ k l : ℕ, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      (∀ k : ℕ,
        C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
          (τ (v k)) (τ (v k) + (T - τ (v k)) / 2) ∧
        (∃ s : ℝ, s ∈ Set.Icc (τ (v k))
            (τ (v k) + (T - τ (v k)) / 2) ∧
          ‖h3PathActualProjectedMomentumSource244 hH3 s‖ = C (v k)) ∧
        0 < δ (v k) ∧ τ (v k) + δ (v k) < T ∧
        δ (v k) = h3PathCubicAnnulusQuadraticSharpPDEWidth244
          ((T - τ (v k)) / 2)
          (h3PathCubicAnnulusActualGap244 hH3 τ N (v k))
          (h3PathCubicAnnulusActualLinearRate244 N K C (v k))
          (h3PathCubicAnnulusActualQuadraticRate244 N C (v k)) ∧
        (∀ s : ℝ, s ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k)) →
          ((v k : ℝ) + 1) ^ 3 / 2 <
            h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 s) -
            h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
        ((v k : ℝ) + 1) ^ 3 / 4 <
          h3PathCubicAnnulusActualGap244 hH3 τ N (v k) ∧
        (∀ m : ℕ, v k ≤ m → m < N (v k) →
          h3PathActualLowRadialDissipation244 ((m : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) -
            h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) ≤
              3 * (((v k : ℝ) + 1) ^ 3) / 4)) ∧
      Summable (fun k : ℕ =>
        δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
        ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2) ≤ ε ∨
        ((v k : ℝ) + 1) ^ 6 ≤
          16 * ε * (h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1) ∨
        ((v k : ℝ) + 1) ^ 9 ≤
          16 * ε ^ 2 *
            (h3PathCubicAnnulusActualQuadraticRate244 N C (v k) + 1)) ∧
      (Tendsto (fun k : ℕ => C (v k) ^ 2) atTop atTop →
        ∀ M : ℝ, ∀ᶠ k : ℕ in atTop,
          ∃ s : ℝ,
            s ∈ Set.Icc (τ (v k))
              (τ (v k) + (T - τ (v k)) / 2) ∧
            M ≤ ‖h3PathActualProjectedMomentumSource244 hH3 s‖) := by
  obtain ⟨τ, N, K, C, δ, hTime, hLimit, hAll⟩ :=
    h3Path_noL2Trace_forces_canonicalSourceQuadraticSharpClocks244
      hH3 hClass hMass hNoTrace
  have hδ (n : ℕ) : 0 < δ n := by
    rcases hAll n with ⟨_, _, _, _, _, hp, _, _, _, _, _⟩
    exact hp
  have hEnd (n : ℕ) : τ n + δ n < T := by
    rcases hAll n with ⟨_, _, _, _, _, _, he, _, _, _, _⟩
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
      rcases hAll (v k) with ⟨_, _, _, _, _, _, hb, _, hAnnulus, _, _⟩
      have hrClass : r ∈ Set.Ioo a T :=
        ⟨lt_of_lt_of_le (hTime (v k)).1 hr.1,
          lt_of_le_of_lt hr.2 hb⟩
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
  let f : ℕ → ℝ := fun k =>
    δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)
  have hf (k : ℕ) : 0 ≤ f k := by
    dsimp only [f]
    exact mul_nonneg (hδ (v k)).le (by positivity)
  have hSummable : Summable f :=
    h3Path_nonnegativeBoundedRangeSums_summable244 f M hf
      (by simpa only [f] using hBound)
  have hCollapse : Tendsto (fun k : ℕ =>
      δ (v k) * ((v k : ℝ) + 1) ^ 3) atTop (𝓝 0) := by
    have hTwice := hSummable.tendsto_atTop_zero.const_mul (2 : ℝ)
    have hEq : (fun k : ℕ =>
        δ (v k) * ((v k : ℝ) + 1) ^ 3) =
        (fun k : ℕ => 2 * f k) := by
      funext k
      dsimp only [f]
      ring
    rw [hEq]
    simpa only [mul_zero] using hTwice
  have hΛ (n : ℕ) :
      0 ≤ h3PathCubicAnnulusActualLinearRate244 N K C n := by
    unfold h3PathCubicAnnulusActualLinearRate244
    rcases hAll n with ⟨_, hK, hC, _, _, _, _, _, _, _, _⟩
    exact h3Path_finiteAnnulusPDEVariationCoefficient_nonneg244
      ((n : ℝ) + 1) ((N n : ℝ) + 1) (K n) (C n) hK hC
  have hΞ (n : ℕ) :
      0 ≤ h3PathCubicAnnulusActualQuadraticRate244 N C n := by
    unfold h3PathCubicAnnulusActualQuadraticRate244
    exact h3Path_finiteAnnulusPDEAnchoredQuadraticCoefficient_nonneg244
      ((n : ℝ) + 1) ((N n : ℝ) + 1) (C n)
  have hExact (k : ℕ) :
      δ (v k) = h3PathCubicAnnulusQuadraticSharpPDEWidth244
        ((T - τ (v k)) / 2)
        (h3PathCubicAnnulusActualGap244 hH3 τ N (v k))
        (h3PathCubicAnnulusActualLinearRate244 N K C (v k))
        (h3PathCubicAnnulusActualQuadraticRate244 N C (v k)) := by
    rcases hAll (v k) with ⟨_, _, _, _, _, _, _, he, _, _, _⟩
    exact he
  have hQuarter : ∀ᶠ k : ℕ in atTop,
      ((v k : ℝ) + 1) ^ 3 / 4 ≤
        h3PathCubicAnnulusActualGap244 hH3 τ N (v k) := by
    apply Filter.Eventually.of_forall
    intro k
    rcases hAll (v k) with ⟨_, _, _, _, _, _, _, _, _, hg, _⟩
    exact hg.le
  have hΛEv : ∀ᶠ k : ℕ in atTop,
      0 ≤ h3PathCubicAnnulusActualLinearRate244 N K C (v k) :=
    Filter.Eventually.of_forall (fun k => hΛ (v k))
  have hΞEv : ∀ᶠ k : ℕ in atTop,
      0 ≤ h3PathCubicAnnulusActualQuadraticRate244 N C (v k) :=
    Filter.Eventually.of_forall (fun k => hΞ (v k))
  have hBarrier := h3Path_exactQuadraticSharpClocks_threeScaleBarrier244
    v δ (fun n => (T - τ n) / 2)
    (h3PathCubicAnnulusActualGap244 hH3 τ N)
    (h3PathCubicAnnulusActualLinearRate244 N K C)
    (h3PathCubicAnnulusActualQuadraticRate244 N C)
    hv hExact hCollapse hQuarter hΛEv hΞEv
  have hCanon (k : ℕ) : C (v k) =
      h3PathActualProjectedSourceWindowEnvelope244 hH3
        (τ (v k)) (τ (v k) + (T - τ (v k)) / 2) := by
    rcases hAll (v k) with ⟨_, _, _, hc, _, _, _, _, _, _, _⟩
    exact hc
  have hPeak (k : ℕ) :
      ∃ s : ℝ,
        s ∈ Set.Icc (τ (v k)) (τ (v k) + (T - τ (v k)) / 2) ∧
        ‖h3PathActualProjectedMomentumSource244 hH3 s‖ = C (v k) := by
    rcases hAll (v k) with ⟨_, _, _, _, hp, _, _, _, _, _, _⟩
    exact hp
  have hC (k : ℕ) : 0 ≤ C (v k) := by
    rcases hAll (v k) with ⟨_, _, hc, _, _, _, _, _, _, _, _⟩
    exact hc
  refine ⟨τ, N, K, C, δ, v, hv, hCofinal, hTime, hSeparate,
    ?_, ?_, hBarrier, ?_⟩
  · intro k
    rcases hAll (v k) with
      ⟨_, _, _, _, _, hp, he, hx, hflo, hg, hm⟩
    exact ⟨hCanon k, hPeak k, hp, he, hx, hflo, hg, hm⟩
  · simpa only [f] using hSummable
  · intro hSquare M₀
    exact h3Path_attainedSourceSquareEscape_forces_windowPeaks244
      (fun k => C (v k)) (fun k => τ (v k))
      (fun k => τ (v k) + (T - τ (v k)) / 2)
      (fun s => ‖h3PathActualProjectedMomentumSource244 hH3 s‖)
      hC hPeak hSquare M₀

end
end PrimeTensor.FirstMonomialTriad
