import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEExactClockAlternative244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEDisjointCostSum244
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-!
# Exact cubic PDE clocks: terminal geometry or source/spectral concentration

The previous cofinal theorem retains the exact polynomial PDE width, rather
than choosing an arbitrarily smaller time window. Extracting disjoint windows
only selects indices and does not shorten them. Consequently finite terminal
H³ dissipation makes the actual exact cubic costs summable, and the explicit
width trichotomy applies at every selected witness.

Since the cubic height tends to infinity along a strict index subsequence,
the fixed-mass alternative eventually disappears. The surviving statement
is an honest OR: geometric terminal-time compression or large anchored PDE
variation coefficients (which depend on cutoff, spectral norm and source).
It excludes neither branch and claims no terminal regularity theorem.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Along a strict increasing natural index selector the cubic height
exceeds any fixed real mass at sufficiently large indices. -/
theorem h3Path_strictMonoCubicHeight_eventually_above_mass244
    (v : ℕ → ℕ) (hv : StrictMono v) (M : ℝ) :
    ∀ᶠ k : ℕ in atTop,
      M < (((v k : ℝ) + 1) ^ 3) / 2 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * M)
  apply Filter.eventually_atTop.2
  refine ⟨n, ?_⟩
  intro k hk
  have hIndex : n ≤ v k := le_trans hk hv.le_apply
  have hIndexReal : (n : ℝ) ≤ (v k : ℝ) := by exact_mod_cast hIndex
  have hLinear : 2 * M < (v k : ℝ) + 1 := by
    linarith only [hn, hIndexReal]
  let x : ℝ := (v k : ℝ) + 1
  have hx : 1 ≤ x := by
    dsimp only [x]
    have hNat : (0 : ℝ) ≤ (v k : ℝ) := by positivity
    linarith only [hNat]
  have hCube : x ≤ x ^ 3 := by
    have hx0 : 0 ≤ x := le_trans zero_le_one hx
    have hx1 : 0 ≤ x - 1 := sub_nonneg.mpr hx
    have hx2 : 0 ≤ x + 1 := by linarith only [hx]
    have hProduct : 0 ≤ x * (x - 1) * (x + 1) :=
      mul_nonneg (mul_nonneg hx0 hx1) hx2
    nlinarith only [hProduct]
  dsimp only [x] at hCube
  linarith only [hLinear, hCube]

/-- Summable exact cubic window costs force an eventual terminal-compression
or PDE-coefficient-growth alternative. The cost bound is *finite sums*, not
an unjustified identity with a terminal integral. The selected widths must
be the literal minimum; merely shorter positive widths are insufficient. -/
theorem h3Path_exactCubicClocks_finiteCosts_forces_alternative244
    (v : ℕ → ℕ) (δ b gap Λ Ξ : ℕ → ℝ) (M : ℝ)
    (hv : StrictMono v)
    (hδ : ∀ n : ℕ, 0 ≤ δ n)
    (hΛ : ∀ n : ℕ, 0 ≤ Λ n)
    (hΞ : ∀ n : ℕ, 0 ≤ Ξ n)
    (hExact : ∀ n : ℕ,
      δ n = h3PathCubicAnnulusExactPDEWidth244
        (b n) (gap n) (Λ n) (Ξ n))
    (hCost : ∀ m : ℕ,
      (∑ k ∈ Finset.range m,
        δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ≤ M) :
    Summable (fun k : ℕ =>
      δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ∧
    Tendsto (fun k : ℕ =>
      δ (v k) * ((v k : ℝ) + 1) ^ 3) atTop (𝓝 0) ∧
    (∀ᶠ k : ℕ in atTop,
      2 * M ≥ (((v k : ℝ) + 1) ^ 3 / 2) * b (v k) ∨
      (((v k : ℝ) + 1) ^ 3 / 2) * gap (v k) ≤
        2 * M * (Λ (v k) + Ξ (v k) + 1)) := by
  let f : ℕ → ℝ := fun k =>
    δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)
  have hf (k : ℕ) : 0 ≤ f k := by
    dsimp only [f]
    exact mul_nonneg (hδ (v k)) (by positivity)
  have hSummable : Summable f :=
    h3Path_nonnegativeBoundedRangeSums_summable244 f M hf
      (by simpa only [f] using hCost)
  have hZero : Tendsto (fun k : ℕ =>
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
  have hEach (k : ℕ) : f k ≤ M := by
    have hPartial := hCost (k + 1)
    rw [Finset.sum_range_succ] at hPartial
    have hPrefix : 0 ≤ ∑ i ∈ Finset.range k, f i :=
      Finset.sum_nonneg (fun i _ => hf i)
    change (∑ i ∈ Finset.range k, f i) + f k ≤ M at hPartial
    linarith only [hPartial, hPrefix]
  have hLarge := h3Path_strictMonoCubicHeight_eventually_above_mass244
    v hv M
  have hEventually : ∀ᶠ k : ℕ in atTop,
      2 * M ≥ (((v k : ℝ) + 1) ^ 3 / 2) * b (v k) ∨
      (((v k : ℝ) + 1) ^ 3 / 2) * gap (v k) ≤
        2 * M * (Λ (v k) + Ξ (v k) + 1) := by
    filter_upwards [hLarge] with k hkLarge
    have hA : 0 < (((v k : ℝ) + 1) ^ 3 / 2) := by positivity
    have hChoice := h3Path_cubicAnnulusExactPDEWidth_costTrichotomy244
      (((v k : ℝ) + 1) ^ 3 / 2) M
      (b (v k)) (gap (v k)) (Λ (v k)) (Ξ (v k))
      (δ (v k)) hA (hΛ (v k)) (hΞ (v k))
      (hExact (v k)) (by
        calc
          (((v k : ℝ) + 1) ^ 3 / 2) * δ (v k) = f k := by
            dsimp only [f]
            ring
          _ ≤ M := hEach k)
    rcases hChoice with hTime | hUnit | hPDE
    · exact Or.inl hTime
    · exact False.elim ((not_le_of_gt hkLarge) hUnit)
    · exact Or.inr hPDE
  exact ⟨by simpa only [f] using hSummable, hZero, hEventually⟩

/-- Actual annular height surplus above the half-cubic threshold. -/
noncomputable def h3PathCubicAnnulusActualGap244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (τ : ℕ → ℝ) (N : ℕ → ℕ) (n : ℕ) : ℝ :=
  (h3PathActualLowRadialDissipation244 ((N n : ℝ) + 1)
      (h3AuditActualSpectralVelocityTotal hH3 (τ n)) -
    h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
      (h3AuditActualSpectralVelocityTotal hH3 (τ n))) -
      ((n : ℝ) + 1) ^ 3 / 2

/-- Physical projected-source linear coefficient at a cubic annulus. -/
noncomputable def h3PathCubicAnnulusActualLinearRate244
    (N : ℕ → ℕ) (K C : ℕ → ℝ) (n : ℕ) : ℝ :=
  h3PathFiniteAnnulusPDEVariationCoefficient244
    ((n : ℝ) + 1) ((N n : ℝ) + 1) (K n) (C n)

/-- Physical projected-source quadratic coefficient at a cubic annulus. -/
noncomputable def h3PathCubicAnnulusActualQuadraticRate244
    (N : ℕ → ℕ) (C : ℕ → ℝ) (n : ℕ) : ℝ :=
  h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
    ((n : ℝ) + 1) ((N n : ℝ) + 1) (C n)

/-- Physical no-terminal-L²-trace branch, assuming finite terminal H³
L¹ dissipation: one can extract pairwise separated genuine cubic witnesses
with the *exact* PDE widths, summable costs, and an eventual dichotomy.
The dichotomy does not exclude geometric time compression or coefficient
concentration, so it is not a terminal regularity contradiction. -/
theorem h3Path_noL2Trace_finiteDissipation_exactPDEClockConcentration244
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
      (∀ k : ℕ, 0 < δ (v k)) ∧
      (∀ k : ℕ,
        δ (v k) = h3PathCubicAnnulusExactPDEWidth244
          ((T - τ (v k)) / 2)
          (h3PathCubicAnnulusActualGap244 hH3 τ N (v k))
          (h3PathCubicAnnulusActualLinearRate244 N K C (v k))
          (h3PathCubicAnnulusActualQuadraticRate244 N C (v k))) ∧
      Summable (fun k : ℕ =>
        δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ∧
      Tendsto (fun k : ℕ =>
        δ (v k) * ((v k : ℝ) + 1) ^ 3) atTop (𝓝 0) ∧
      (∀ᶠ k : ℕ in atTop,
        2 * (∫ r in a..T, velocityH3DissipationAt u r) ≥
          (((v k : ℝ) + 1) ^ 3 / 2) * ((T - τ (v k)) / 2) ∨
        (((v k : ℝ) + 1) ^ 3 / 2) *
          h3PathCubicAnnulusActualGap244 hH3 τ N (v k) ≤
          2 * (∫ r in a..T, velocityH3DissipationAt u r) *
            (h3PathCubicAnnulusActualLinearRate244 N K C (v k) +
             h3PathCubicAnnulusActualQuadraticRate244 N C (v k) + 1)) := by
  obtain ⟨τ, N, K, C, δ, hTime, hLimit, hAll⟩ :=
    h3Path_noL2Trace_forces_cubicExactPDEClocks244
      hH3 hClass hMass hNoTrace
  have hδ (n : ℕ) : 0 < δ n := by
    rcases hAll n with ⟨_, _, _, hp, _, _, _, _, _, _, _⟩
    exact hp
  have hEnd (n : ℕ) : τ n + δ n < T := by
    rcases hAll n with ⟨_, _, _, _, _, he, _, _, _, _, _⟩
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
      rcases hAll (v k) with
        ⟨_, _, _, _, _, hb, _, _, _, hAnnulus, _⟩
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
  have hExact (n : ℕ) :
      δ n = h3PathCubicAnnulusExactPDEWidth244
        ((T - τ n) / 2)
        (h3PathCubicAnnulusActualGap244 hH3 τ N n)
        (h3PathCubicAnnulusActualLinearRate244 N K C n)
        (h3PathCubicAnnulusActualQuadraticRate244 N C n) := by
    rcases hAll n with ⟨_, _, _, _, _, _, _, _, he, _, _⟩
    simpa only [h3PathCubicAnnulusActualGap244,
      h3PathCubicAnnulusActualLinearRate244,
      h3PathCubicAnnulusActualQuadraticRate244] using he
  obtain ⟨hSummable, hCollapse, hAlternative⟩ :=
    h3Path_exactCubicClocks_finiteCosts_forces_alternative244
      v δ (fun n => (T - τ n) / 2)
      (h3PathCubicAnnulusActualGap244 hH3 τ N)
      (h3PathCubicAnnulusActualLinearRate244 N K C)
      (h3PathCubicAnnulusActualQuadraticRate244 N C)
      M hv (fun n => (hδ n).le) hΛ hΞ hExact hBound
  refine ⟨τ, N, K, C, δ, v, hv, hCofinal, hSeparate,
    (fun k => hδ (v k)), (fun k => hExact (v k)),
    hSummable, hCollapse, ?_⟩
  simpa only [M] using hAlternative

end
end PrimeTensor.FirstMonomialTriad
