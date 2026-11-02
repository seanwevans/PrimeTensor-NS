import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessEndpointViscousResidualBudget
import Mathlib.Tactic

/-!
# Adaptive inverse-height persistence obstruction

The exact physical finite-H³ dissipation budget bounds the charges
`η k * H k` on the selected cofinal endpoint-spike windows. Instead of a
constant lower target γ, this module permits an arbitrary proposed
sequence `γ k` whose sums diverge on EACH tail.

If `H k > 0` and these charges have uniformly bounded partial sums,
every tail contains a selected index with

  η k < γ k / H k.

Thus no eventually persistent adaptive inverse-height lower scale can
have an unbounded cumulative demanded charge. This conclusion does NOT
supply a lower width estimate, exclude PDE-clock alternatives, or establish
continuation. No continuity of the full H³ dissipation is assumed.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- A uniformly bounded series of charges cannot dominate, from some
index onward, a proposed adaptive price sequence whose finite sums are
unbounded on every tail. The argument retains the prefix charge: no
positivity assumption on the preceding terms is needed. -/
theorem h3Critical_scalar_boundedCharge_adaptiveShortfallEveryTail
    (η H γ : ℕ → ℝ) (B : ℝ)
    (hHeight : ∀ k : ℕ, 0 < H k)
    (hBudget : ∀ m : ℕ,
      (∑ k ∈ Finset.range m, η k * H k) ≤ B)
    (hUnbounded : ∀ (n : ℕ) (C : ℝ),
      ∃ m : ℕ, C < ∑ j ∈ Finset.range m, γ (n + j))
    (n : ℕ) :
    ∃ k : ℕ, n ≤ k ∧ η k < γ k / H k := by
  classical
  by_contra hNo
  have hLower (j : ℕ) : γ (n + j) ≤ η (n + j) * H (n + j) := by
    have hNoShort : γ (n + j) / H (n + j) ≤ η (n + j) := by
      apply le_of_not_gt
      intro hShort
      exact hNo ⟨n + j, Nat.le_add_right n j, hShort⟩
    exact (div_le_iff₀ (hHeight (n + j))).mp hNoShort
  obtain ⟨m, hHuge⟩ := hUnbounded n
    (B - ∑ k ∈ Finset.range n, η k * H k)
  have hBlock :
      (∑ j ∈ Finset.range m, γ (n + j)) ≤
        ∑ j ∈ Finset.range m, η (n + j) * H (n + j) := by
    apply Finset.sum_le_sum
    intro j _
    exact hLower j
  have hSplit :
      (∑ k ∈ Finset.range (n + m), η k * H k) =
        (∑ k ∈ Finset.range n, η k * H k) +
          ∑ j ∈ Finset.range m, η (n + j) * H (n + j) := by
    exact Finset.sum_range_add (fun k => η k * H k) n m
  have hTotal := hBudget (n + m)
  linarith only [hHuge, hBlock, hSplit, hTotal]

/-- Adaptive inverse-height persistence cannot eventually hold at all
selected indices if its required charge sums are unbounded on each tail. -/
theorem h3Critical_scalar_boundedCharge_noEventualAdaptivePersistence
    (η H γ : ℕ → ℝ) (B : ℝ)
    (hHeight : ∀ k : ℕ, 0 < H k)
    (hBudget : ∀ m : ℕ,
      (∑ k ∈ Finset.range m, η k * H k) ≤ B)
    (hUnbounded : ∀ (n : ℕ) (C : ℝ),
      ∃ m : ℕ, C < ∑ j ∈ Finset.range m, γ (n + j)) :
    ¬ (∀ᶠ k : ℕ in atTop, γ k / H k ≤ η k) := by
  intro hPersistent
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.1 hPersistent
  obtain ⟨k, hnk, hShort⟩ :=
    h3Critical_scalar_boundedCharge_adaptiveShortfallEveryTail
      η H γ B hHeight hBudget hUnbounded n
  exact (not_lt_of_ge (hn k hnk)) hShort

/-- Applied to the SAME cofinal source/spectral maximizers and the exact
physical H³ dissipation budget. An arbitrary adaptive target γ with
unbounded finite sums on every tail cannot be paid by endpoint persistence
at every sufficiently late index. Every tail contains a shorter window.
The original four-way physical PDE-clock alternative is unchanged. -/
theorem h3Critical_noL2Trace_cofinalFivefold_adaptiveEndpointPersistenceBarrier
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (c ρ σ M q : ℕ → ℝ)
    (hc : ∀ n, c n ∈ Set.Ioo b T)
    (hcLimit : Tendsto c atTop (𝓝 T))
    (hρ : ∀ n, 0 ≤ ρ n)
    (hσ : ∀ n, 0 ≤ σ n)
    (hM : ∀ n, 0 ≤ M n)
    (hq : ∀ n, 0 < q n)
    (R ε : ℕ → ℝ) (hR : ∀ k, 0 < R k) (hε : ∀ k, 0 < ε k)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (γ : ℕ → ℝ)
    (hGammaUnbounded : ∀ (n : ℕ) (C : ℝ),
      ∃ m : ℕ, C < ∑ j ∈ Finset.range m, γ (n + j)) :
    ∃ i : Fin 3, ∃ t w : ℕ → ℝ, ∃ v : ℕ → ℕ,
    ∃ sSource sState δ p η : ℕ → ℝ, ∃ N : ℕ → ℕ,
      StrictMono v ∧
      Tendsto (fun k : ℕ => t (v k)) atTop (𝓝 T) ∧
      Summable (fun k : ℕ => η k * (R k ^ 2 * ε k ^ 2 / 8)) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m, η k * (R k ^ 2 * ε k ^ 2 / 8)) ≤
          ∫ r in a..T, velocityH3DissipationAt u r) ∧
      (∀ n : ℕ, ∃ k : ℕ, n ≤ k ∧
        η k < γ k / (R k ^ 2 * ε k ^ 2 / 8)) ∧
      (¬ (∀ᶠ k : ℕ in atTop,
        γ k / (R k ^ 2 * ε k ^ 2 / 8) ≤ η k)) ∧
      (∀ k : ℕ,
        3 + 4 * h3AuditInitialLerayEnergyCoefficient * ε k ≤
          max 1 (σ (v k)) + 1 →
        h3Critical_fivefold_nonSpectralExcursionAlternative hH3
          (t (v k)) (w (v k)) (δ k) (σ (v k))
          (M (v k)) (q (v k)) (sSource k) ∨
        ε k ^ 2 ≤ 2 * (3 * h3TerminalRadialSobolevWeightSquareCeiling (R k)) *
          (‖h3PathActualProjectedMomentumSource244 hH3 (sSource k)‖ *
            w (v k)) ^ 2 ∨
        R k ^ 2 * ε k ^ 2 < 8 * velocityH3DissipationAt u (t (v k)) ∨
        (0 < η k ∧
          ∀ r : ℝ, r ∈ Set.Icc (p k) (p k + η k) →
            R k ^ 2 * ε k ^ 2 / 8 <
              h3PathActualLowRadialDissipation244 ((N k : ℝ) + 1)
                (h3AuditActualSpectralVelocityTotal hH3 r) ∧
            R k ^ 2 * ε k ^ 2 / 8 < velocityH3DissipationAt u r)) := by
  obtain ⟨i, t, w, v, sSource, sState, δ, p, η, N,
      hv, hLimit, _hSep, hSum, _hCharge, hBudget,
      _hResidual, hGate⟩ :=
    h3Critical_noL2Trace_cofinalFivefold_residualCriticalWindowBudget
      hH3 hClass b hb hNoTrace c ρ σ M q
      hc hcLimit hρ hσ hM hq R ε hR hε hDInt
  have hHeight (k : ℕ) : 0 < R k ^ 2 * ε k ^ 2 / 8 := by
    have hr := hR k
    have he := hε k
    positivity
  have hAdaptive : ∀ n : ℕ, ∃ k : ℕ, n ≤ k ∧
      η k < γ k / (R k ^ 2 * ε k ^ 2 / 8) := by
    intro n
    exact h3Critical_scalar_boundedCharge_adaptiveShortfallEveryTail
      η (fun k => R k ^ 2 * ε k ^ 2 / 8) γ
      (∫ r in a..T, velocityH3DissipationAt u r)
      hHeight hBudget hGammaUnbounded n
  have hNoEventual :
      ¬ (∀ᶠ k : ℕ in atTop,
        γ k / (R k ^ 2 * ε k ^ 2 / 8) ≤ η k) :=
    h3Critical_scalar_boundedCharge_noEventualAdaptivePersistence
      η (fun k => R k ^ 2 * ε k ^ 2 / 8) γ
      (∫ r in a..T, velocityH3DissipationAt u r)
      hHeight hBudget hGammaUnbounded
  exact ⟨i, t, w, v, sSource, sState, δ, p, η, N,
    hv, hLimit, hSum, hBudget, hAdaptive, hNoEventual, hGate⟩

end
end PrimeTensor.Bridge.Euclidean
