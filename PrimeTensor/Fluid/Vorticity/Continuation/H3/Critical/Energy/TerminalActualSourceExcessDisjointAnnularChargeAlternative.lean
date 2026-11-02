import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessDisjointActiveAnnulusDiagonal
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEDisjointCostCollapse244
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-!
# Nonvacuous cumulative charge alternative for disjoint physical H³ annuli

The disjoint active annular windows of the preceding checkpoint have genuinely
positive, physical finite-band H³ dissipation costs, but no global L¹ budget
is available on the no-physical-L²-terminal-trace branch. In fact a prior
proof shows that finite full H³ dissipation and no terminal L² trace are
incompatible. Therefore the present argument does NOT assume finite full
terminal dissipation.

Define the local cubic-height charge f(k) = δ(v(k))*(v(k)+1)^3/2. The PDE
annular integral is at least f(k). The exact mathematical alternative is:

* either the partial sums of these actual certified lower charges exceed
  every prescribed real number;
* or their partial sums are bounded, and the spectral-cubic-weighted
  persistence widths δ(v(k))*(v(k)+1)^3 tend to zero.

This is a real alternative, not a theorem that all annular charges diverge.
In the second branch the complementary full-dissipation nonintegrability
must be carried by the remaining time-frequency regions; the local windows
may shrink. No claim about smooth Navier–Stokes continuation is made.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- For ANY nonnegative cubic charges, either the finite sums are unbounded
above, or the cubic-weighted widths vanish. There is no terminal L¹
hypothesis and no PDE-specific assumption in this scalar dichotomy. -/
theorem h3Critical_scalar_disjointCubicCharges_unbounded_or_widthCollapse
    (v : ℕ → ℕ) (δ : ℕ → ℝ)
    (hδ : ∀ k : ℕ, 0 ≤ δ (v k)) :
    (∀ M : ℝ, ∃ m : ℕ,
      M < ∑ k ∈ Finset.range m,
        δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ∨
    Tendsto (fun k : ℕ => δ (v k) * ((v k : ℝ) + 1) ^ 3)
      atTop (𝓝 (0 : ℝ)) := by
  classical
  let f : ℕ → ℝ := fun k => δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)
  have hf (k : ℕ) : 0 ≤ f k := by
    dsimp only [f]
    exact mul_nonneg (hδ k) (by positivity)
  by_cases hBound : ∃ M : ℝ, ∀ m : ℕ,
      (∑ k ∈ Finset.range m, f k) ≤ M
  · right
    obtain ⟨M, hM⟩ := hBound
    have hSummable : Summable f :=
      h3Path_nonnegativeBoundedRangeSums_summable244 f M hf hM
    have hZero : Tendsto f atTop (𝓝 (0 : ℝ)) :=
      hSummable.tendsto_atTop_zero
    have hTwice := hZero.const_mul (2 : ℝ)
    have hEq :
        (fun k : ℕ => δ (v k) * ((v k : ℝ) + 1) ^ 3) =
          (fun k : ℕ => 2 * f k) := by
      funext k
      dsimp only [f]
      ring
    rw [hEq]
    simpa only [mul_zero] using hTwice
  · left
    intro M
    by_contra hNo
    apply hBound
    refine ⟨M, ?_⟩
    intro m
    have hNot : ¬ M < ∑ k ∈ Finset.range m, f k := by
      intro hLarge
      apply hNo
      exact ⟨m, by simpa only [f] using hLarge⟩
    exact le_of_not_gt hNot

/-- The actual integrated annular costs dominate the cubic-height charge
partial sums, index by index. This comparison does not invoke a full
terminal physical dissipation integral. -/
theorem h3Critical_scalar_finiteAnnularChargeSum_le_actualIntegralSum
    (v : ℕ → ℕ) (δ : ℕ → ℝ) (I : ℕ → ℝ)
    (hCost : ∀ k : ℕ,
      δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2) ≤ I k) :
    ∀ m : ℕ,
      (∑ k ∈ Finset.range m,
        δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ≤
      ∑ k ∈ Finset.range m, I k := by
  intro m
  exact Finset.sum_le_sum (fun k _ => hCost k)

/-- The actual no-L²-trace branch has separated, increasing-frequency,
exact PDE-certified annuli. Either THEIR certified cumulative cubic charges
are unbounded, or the cubic-height-weighted physical persistence widths
collapse. Both branches preserve the original local physical integral
charges and exact source-envelope quadratic PDE width selector.

In particular this theorem does not add the contradictory assumption of
finite full H³ dissipation. -/
theorem h3Critical_noL2Trace_disjointActiveAnnuli_unboundedCharge_or_cubicClockCollapse
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ t : ℕ → ℝ, ∃ N : ℕ → ℕ, ∃ C δ : ℕ → ℝ, ∃ v : ℕ → ℕ,
      StrictMono v ∧
      Tendsto (fun k : ℕ => t (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → t (v k) + δ (v k) < t (v l)) ∧
      (∀ k : ℕ,
        k ≤ v k ∧ 0 < δ (v k) ∧ t (v k) + δ (v k) < T ∧
        C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
          (t (v k)) (t (v k) + (T - t (v k)) / 2) ∧
        δ (v k) = h3PathCubicAnnulusQuadraticSharpPDEWidth244
          ((T - t (v k)) / 2)
          ((h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
                (h3AuditActualSpectralVelocityTotal hH3 (t (v k))) -
              h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
                (h3AuditActualSpectralVelocityTotal hH3 (t (v k)))) -
              ((v k : ℝ) + 1) ^ 3 / 2)
          (h3PathFiniteAnnulusPDEVariationCoefficient244
            ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
            ‖h3AuditActualSpectralVelocityTotal hH3 (t (v k))‖ (C (v k)))
          (h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
            ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) (C (v k))) ∧
        (∀ r : ℝ, r ∈ Set.Icc (t (v k)) (t (v k) + δ (v k)) →
          ((v k : ℝ) + 1) ^ 3 / 2 <
            h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 r) -
            h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 r) ∧
          h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 r) -
            h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 r) ≤
            velocityH3DissipationAt u r) ∧
        δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2) ≤
          ∫ r in t (v k)..(t (v k) + δ (v k)),
            h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 r) -
            h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 r)) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m,
          δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ≤
        ∑ k ∈ Finset.range m,
          (∫ r in t (v k)..(t (v k) + δ (v k)),
            h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 r) -
            h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 r))) ∧
      ((∀ M : ℝ, ∃ m : ℕ,
        M < ∑ k ∈ Finset.range m,
          δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ∨
       Tendsto (fun k : ℕ => δ (v k) * ((v k : ℝ) + 1) ^ 3)
         atTop (𝓝 (0 : ℝ))) := by
  obtain ⟨t, N, C, δ, v, _hTimes, _hDist, _hLimit,
      hWindows, hMono, hCofinal, hSeparated, hIndex⟩ :=
    h3Critical_noL2Trace_disjointCofinalActiveCubicAnnuli
      hH3 hClass hNoTrace
  have hSelected (k : ℕ) :
      k ≤ v k ∧ 0 < δ (v k) ∧ t (v k) + δ (v k) < T ∧
      C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
        (t (v k)) (t (v k) + (T - t (v k)) / 2) ∧
      δ (v k) = h3PathCubicAnnulusQuadraticSharpPDEWidth244
        ((T - t (v k)) / 2)
        ((h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (t (v k))) -
            h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (t (v k)))) -
            ((v k : ℝ) + 1) ^ 3 / 2)
        (h3PathFiniteAnnulusPDEVariationCoefficient244
          ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
          ‖h3AuditActualSpectralVelocityTotal hH3 (t (v k))‖ (C (v k)))
        (h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
          ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) (C (v k))) ∧
      (∀ r : ℝ, r ∈ Set.Icc (t (v k)) (t (v k) + δ (v k)) →
        ((v k : ℝ) + 1) ^ 3 / 2 <
          h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 r) -
          h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 r) ∧
        h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 r) -
          h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 r) ≤
          velocityH3DissipationAt u r) ∧
      δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2) ≤
        ∫ r in t (v k)..(t (v k) + δ (v k)),
          h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 r) -
          h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 r) := by
    obtain ⟨_, _, hEnvelope, hδ, hEnd, hExact, _, hFloor, hCost⟩ :=
      hWindows (v k)
    exact ⟨hIndex k, hδ, hEnd, hEnvelope, hExact, hFloor, hCost⟩
  let I : ℕ → ℝ := fun k =>
    ∫ r in t (v k)..(t (v k) + δ (v k)),
      h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 r) -
      h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 r)
  have hCosts (k : ℕ) :
      δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2) ≤ I k :=
    (hSelected k).2.2.2.2.2.2
  have hSum : ∀ m : ℕ,
      (∑ k ∈ Finset.range m,
        δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ≤
      ∑ k ∈ Finset.range m, I k :=
    h3Critical_scalar_finiteAnnularChargeSum_le_actualIntegralSum
      v δ I hCosts
  have hDichotomy := h3Critical_scalar_disjointCubicCharges_unbounded_or_widthCollapse
    v δ (fun k => (hSelected k).2.1.le)
  refine ⟨t, N, C, δ, v, hMono, hCofinal, hSeparated,
    hSelected, ?_, hDichotomy⟩
  simpa only [I] using hSum

end
end PrimeTensor.Bridge.Euclidean
