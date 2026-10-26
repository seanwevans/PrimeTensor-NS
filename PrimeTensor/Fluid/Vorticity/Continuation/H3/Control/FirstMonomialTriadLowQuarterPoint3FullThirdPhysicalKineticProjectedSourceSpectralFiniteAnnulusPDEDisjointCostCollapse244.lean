import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEDisjointCostSum244
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-!
# Terminal L¹ dissipation forces summability and collapse of disjoint cubic clocks

The preceding exact finite-sum theorem controls disjoint, positive, cubic
annular costs by the actual full physical H³ dissipation integrated to T.
The bounded partial sums of positive costs are now converted to genuine
summability, and hence to vanishing weighted persistence widths.

Under the existing no-terminal-physical-L²-trace branch, with positive
terminal kinetic mass and the ADDITIONAL assumption of integrable full H³
dissipation on [a,T], some pairwise separated cofinal cubic annulus witnesses
obey

  Summable (fun k => δ(v k) * (v k + 1)^3 / 2),
  δ(v k) * (v k + 1)^3 → 0.

This says every persistent cubic dissipation window on the extracted
subsequence collapses *faster than its inverse-cubic spectral label*.
It does NOT imply any regularity, terminal contradiction, or control on
source ceilings, since the explicit local widths can shrink arbitrarily.

We also prove a sharp algebraic alternative for the explicit polynomial
PDE budget width min(b/2, 1, gap/(2*(Λ+Ξ+1))): when terminal slack and the
unit cap are too large to explain a small integrated cost, the *PDE
variation coefficient* must be large instead. Its application to the
selected actual witness widths requires retaining the explicit selector
identity, a separate next step not asserted here.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- A nonnegative sequence with uniformly bounded finite partial sums is
summable. This is the exact passage needed to interpret the cubic window
costs as a genuine finite series, not merely as finite inequalities. -/
theorem h3Path_nonnegativeBoundedRangeSums_summable244
    (f : ℕ → ℝ) (M : ℝ)
    (hf : ∀ k : ℕ, 0 ≤ f k)
    (hBound : ∀ m : ℕ, (∑ k ∈ Finset.range m, f k) ≤ M) :
    Summable f := by
  exact summable_of_sum_range_le hf hBound

/-- Each term of the summable, nonnegative disjoint-window cost sequence
converges to zero. Its index may be a sparse cofinal subsequence. -/
theorem h3Path_nonnegativeBoundedRangeSums_tendsto_zero244
    (f : ℕ → ℝ) (M : ℝ)
    (hf : ∀ k : ℕ, 0 ≤ f k)
    (hBound : ∀ m : ℕ, (∑ k ∈ Finset.range m, f k) ≤ M) :
    Tendsto f atTop (𝓝 0) := by
  exact (h3Path_nonnegativeBoundedRangeSums_summable244
    f M hf hBound).tendsto_atTop_zero

/-- A concentration barrier intrinsic to the *explicit* anchored-PDE
polynomial width selector. Let the proposed window be

    δ = min (b/2) (min 1 (gap / (2*(Λ+Ξ+1)))).

If its cost A*δ is bounded by M, while neither the geometric time cap
nor the unit cap could have forced that small a width, then the physical
PDE rate budget must obey A*gap ≤ 2*M*(Λ+Ξ+1).

This is an algebraic necessity, not an assertion of the analytic premises
for the cofinal terminal witnesses. -/
theorem h3Path_explicitBudgetWidth_forces_PDECoefficientGrowth244
    (A M b gap Λ Ξ : ℝ)
    (hA : 0 < A)
    (hΛ : 0 ≤ Λ) (hΞ : 0 ≤ Ξ)
    (hMass :
      A * min (b / 2)
        (min (1 : ℝ) (gap / (2 * (Λ + Ξ + 1)))) ≤ M)
    (hClock : 2 * M < A * b)
    (hUnit : M < A) :
    A * gap ≤ 2 * M * (Λ + Ξ + 1) := by
  let Z : ℝ := Λ + Ξ + 1
  let δ : ℝ := min (b / 2) (min (1 : ℝ) (gap / (2 * Z)))
  have hZ : 0 < Z := by
    dsimp only [Z]
    linarith only [hΛ, hΞ]
  have hδMass : δ ≤ M / A := by
    apply (le_div_iff₀ hA).2
    calc
      δ * A = A * δ := by ring
      _ ≤ M := by simpa only [δ, Z] using hMass
  have hClock' : M / A < b / 2 := by
    apply (div_lt_iff₀ hA).2
    nlinarith only [hClock]
  have hUnit' : M / A < 1 := by
    exact (div_lt_iff₀ hA).2 (by simpa only [one_mul] using hUnit)
  have hLast : gap / (2 * Z) ≤ M / A := by
    by_contra hNot
    have hGt : M / A < gap / (2 * Z) := lt_of_not_ge hNot
    have hContrary : M / A < δ := by
      dsimp only [δ]
      exact lt_min hClock' (lt_min hUnit' hGt)
    exact (not_lt_of_ge hδMass) hContrary
  calc
    A * gap = gap * A := by ring
    _ ≤ M * (2 * Z) :=
      (div_le_div_iff₀ (by positivity : 0 < 2 * Z) hA).mp hLast
    _ = 2 * M * (Λ + Ξ + 1) := by dsimp only [Z]; ring

/-- If the actual full H³ dissipation has a finite terminal L¹ integral,
then the pairwise-separated cofinal cubic-annulus witnesses selected from
the no-physical-L²-terminal-trace branch have SUMMABLE costs and their
inverse-cubic-normalized persistence widths collapse to zero.

The extra terminal integrability is explicit. No terminal contradiction is
claimed: the local projected-PDE ceilings and outer Fourier cutoff may
concentrate sufficiently rapidly to enforce this shrinking. -/
theorem h3Path_noL2Trace_finiteDissipation_forces_cubicWindowCostCollapse244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T) :
    ∃ (τ δ : ℕ → ℝ) (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k : ℕ => τ (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      (∀ k : ℕ, 0 < δ (v k)) ∧
      Summable (fun k : ℕ =>
        δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ∧
      Tendsto (fun k : ℕ =>
        δ (v k) * ((v k : ℝ) + 1) ^ 3) atTop (𝓝 0) ∧
      (∀ k : ℕ,
        δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2) ≤
          ∫ r in a..T, velocityH3DissipationAt u r) := by
  obtain ⟨τ, δ, v, hMono, hCofinal, hSeparated, hδ, hSum⟩ :=
    h3Path_noL2Trace_cubicDisjointCost_finiteSums_le_fullDissipation244
      hH3 hClass hMass hNoTrace hDInt
  let f : ℕ → ℝ := fun k : ℕ =>
    δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)
  let M : ℝ := ∫ r in a..T, velocityH3DissipationAt u r
  have hf (k : ℕ) : 0 ≤ f k := by
    dsimp only [f]
    exact mul_nonneg (hδ k).le (by positivity)
  have hBound (m : ℕ) : (∑ k ∈ Finset.range m, f k) ≤ M := by
    simpa only [f, M] using hSum m
  have hSummable : Summable f :=
    h3Path_nonnegativeBoundedRangeSums_summable244 f M hf hBound
  have hCostZero : Tendsto f atTop (𝓝 0) := hSummable.tendsto_atTop_zero
  have hScaledZero : Tendsto
      (fun k : ℕ => δ (v k) * ((v k : ℝ) + 1) ^ 3) atTop (𝓝 0) := by
    have hTwice := hCostZero.const_mul (2 : ℝ)
    have hEq :
        (fun k : ℕ => δ (v k) * ((v k : ℝ) + 1) ^ 3) =
        (fun k : ℕ => 2 * f k) := by
      funext k
      dsimp only [f]
      ring
    rw [hEq]
    simpa only [mul_zero] using hTwice
  have hEach (k : ℕ) : f k ≤ M := by
    have hPartial := hBound (k + 1)
    rw [Finset.sum_range_succ] at hPartial
    have hPrefix : 0 ≤ ∑ i ∈ Finset.range k, f i :=
      Finset.sum_nonneg (fun i _ => hf i)
    linarith only [hPartial, hPrefix]
  refine ⟨τ, δ, v, hMono, hCofinal, hSeparated, hδ, ?_, hScaledZero, ?_⟩
  · simpa only [f] using hSummable
  · intro k
    simpa only [f, M] using hEach k

end
end PrimeTensor.FirstMonomialTriad
