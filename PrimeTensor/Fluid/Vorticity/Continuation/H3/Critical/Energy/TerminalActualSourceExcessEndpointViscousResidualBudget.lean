import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessEndpointViscousCriticalWindowCount
import Mathlib.Tactic

/-!
# Residual finite-H³ budget on arbitrary terminal blocks of selected endpoint windows

The previous global critical-window count bound charges all costly endpoint
windows against the same physical H³ dissipation integral. Here the *already
paid* windows are retained on the left of the bound: on any block of m
windows starting after n selected windows, the number of windows above the
critical inverse-height threshold is bounded by the remaining real budget
AFTER the first n endpoint charges.

The witnesses and calibrated physical PDE alternatives are precisely the
ones supplied by the synchronized cofinal fivefold spectral gate. Neither
actual source windows nor the endpoint windows are counted twice. We do
NOT infer an a priori positive persistence width or terminal continuation.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- Every charge in a later block is paid out of the unused portion of the
same bounded nonnegative series. This is stronger than the global count:
the already-paid prefix stays explicitly on the left. -/
theorem h3Critical_scalar_finiteBudget_depletedTailCount
    (charge : ℕ → ℝ) (B γ : ℝ)
    (hNonneg : ∀ k : ℕ, 0 ≤ charge k)
    (hBudget : ∀ m : ℕ,
      (∑ k ∈ Finset.range m, charge k) ≤ B)
    (n m : ℕ) :
    (((Finset.range m).filter
      (fun j : ℕ => γ ≤ charge (n + j))).card : ℝ) * γ +
        (∑ k ∈ Finset.range n, charge k) ≤ B := by
  let s : Finset ℕ :=
    (Finset.range m).filter (fun j : ℕ => γ ≤ charge (n + j))
  have hEach : ∀ j ∈ s, γ ≤ charge (n + j) := by
    intro j hj
    exact (Finset.mem_filter.mp hj).2
  have hLower : (s.card : ℝ) * γ ≤
      ∑ j ∈ s, charge (n + j) := by
    calc
      (s.card : ℝ) * γ = ∑ j ∈ s, γ := by simp [mul_comm]
      _ ≤ ∑ j ∈ s, charge (n + j) := Finset.sum_le_sum hEach
  have hSubset : s ⊆ Finset.range m := Finset.filter_subset _ _
  have hUpper : (∑ j ∈ s, charge (n + j)) ≤
      ∑ j ∈ Finset.range m, charge (n + j) :=
    Finset.sum_le_sum_of_subset_of_nonneg hSubset
      (fun j _ _ => hNonneg (n + j))
  have hSplit :
      (∑ k ∈ Finset.range (n + m), charge k) =
        (∑ k ∈ Finset.range n, charge k) +
          ∑ j ∈ Finset.range m, charge (n + j) := by
    exact Finset.sum_range_add charge n m
  have hTotal := hBudget (n + m)
  have hFinal : (s.card : ℝ) * γ +
      (∑ k ∈ Finset.range n, charge k) ≤ B := by
    linarith only [hLower, hUpper, hSplit, hTotal]
  simpa only [s] using hFinal

/-- Explicit critical inverse-height tail-window count, with the costs of
all previously chosen windows subtracted from the available physical budget.
No lower bound on the lengths of the new windows is assumed. -/
theorem h3Critical_scalar_finiteBudget_depletedInverseHeightTailCount
    (η H : ℕ → ℝ) (B γ : ℝ)
    (hHeight : ∀ k : ℕ, 0 < H k)
    (hWidth : ∀ k : ℕ, 0 ≤ η k)
    (hBudget : ∀ m : ℕ,
      (∑ k ∈ Finset.range m, η k * H k) ≤ B)
    (n m : ℕ) :
    (((Finset.range m).filter
      (fun j : ℕ => γ / H (n + j) ≤ η (n + j))).card : ℝ) * γ +
        (∑ k ∈ Finset.range n, η k * H k) ≤ B := by
  have hNonneg (k : ℕ) : 0 ≤ η k * H k :=
    mul_nonneg (hWidth k) (hHeight k).le
  have hEq :
      (Finset.range m).filter
        (fun j : ℕ => γ / H (n + j) ≤ η (n + j)) =
      (Finset.range m).filter
        (fun j : ℕ => γ ≤ η (n + j) * H (n + j)) := by
    ext j
    simp only [Finset.mem_filter]
    rw [div_le_iff₀ (hHeight (n + j))]
  rw [hEq]
  exact h3Critical_scalar_finiteBudget_depletedTailCount
    (fun k => η k * H k) B γ hNonneg hBudget n m

/-- The original cofinal source/spectral maxima have a *residual* terminal
physical H³ budget on every later block. For γ > 0, the number of later
windows persisting for at least γ times the reciprocal endpoint height,
multiplied by γ, plus ALL previous endpoint charges cannot exceed the
one physical dissipation integral. In particular the remaining budget
cannot be refreshed between successive cofinal observations.

The finite-band PDE-clock and all other four-way alternatives are retained
unchanged on the same witness sequences. -/
theorem h3Critical_noL2Trace_cofinalFivefold_residualCriticalWindowBudget
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
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T) :
    ∃ i : Fin 3, ∃ t w : ℕ → ℝ, ∃ v : ℕ → ℕ,
    ∃ sSource sState δ p η : ℕ → ℝ, ∃ N : ℕ → ℕ,
      StrictMono v ∧
      Tendsto (fun k : ℕ => t (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → p k + η k < p l) ∧
      Summable (fun k : ℕ => η k * (R k ^ 2 * ε k ^ 2 / 8)) ∧
      Tendsto (fun k : ℕ => η k * (R k ^ 2 * ε k ^ 2 / 8))
        atTop (𝓝 (0 : ℝ)) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m,
          η k * (R k ^ 2 * ε k ^ 2 / 8)) ≤
          ∫ r in a..T, velocityH3DissipationAt u r) ∧
      (∀ γ : ℝ, 0 < γ → ∀ n m : ℕ,
        (((Finset.range m).filter
          (fun j : ℕ =>
            γ / (R (n + j) ^ 2 * ε (n + j) ^ 2 / 8) ≤
              η (n + j))).card : ℝ) * γ +
          (∑ k ∈ Finset.range n,
            η k * (R k ^ 2 * ε k ^ 2 / 8)) ≤
              ∫ r in a..T, velocityH3DissipationAt u r) ∧
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
  obtain ⟨i, t, w, v, sSource, sState, A, B, δ, p, η, N,
      hv, hLimit, _hSep, _hSepShort, hInternalSep,
      _hSourceCost, _hInternalCost, hWindows, hGate⟩ :=
    h3Critical_noL2Trace_cofinalFivefold_synchronizedEndpointViscousCosts
      hH3 hClass b hb hNoTrace c ρ σ M q
      hc hcLimit hρ hσ hM hq R ε hR hε
  have hInside (k : ℕ) :
      a ≤ p k ∧ 0 ≤ η k ∧ p k + η k ≤ T := by
    obtain ⟨ht, _hw, hEnd, _hPeaks, _hsSource, _hsState, _hMax,
      _hA, _hB, _hδ, _hδw, _hWidth, _hDissFloor,
      hp, hη, hpEnd, _hSpike, _hZero⟩ := hWindows k
    have hta : a ≤ t (v k) :=
      le_of_lt (lt_trans hb.1 (lt_trans (hc (v k)).1 ht.1))
    exact ⟨hta.trans hp, hη, (hpEnd.trans hEnd.le)⟩
  have hFloor (k : ℕ) (hPositive : 0 < η k) (r : ℝ)
      (hr : r ∈ Set.Icc (p k) (p k + η k)) :
      R k ^ 2 * ε k ^ 2 / 8 ≤ velocityH3DissipationAt u r := by
    obtain ⟨_ht, _hw, _hEnd, _hPeaks, _hsSource, _hsState, _hMax,
      _hA, _hB, _hδ, _hδw, _hWidth, _hDissFloor,
      _hp, _hη, _hpEnd, hSpike, hZero⟩ := hWindows k
    by_cases hAtMax :
        R k ^ 2 * ε k ^ 2 <
          8 * velocityH3DissipationAt u (sState k)
    · exact ((hSpike hAtMax).2 r hr).2.le
    · have hZeroWidth : η k = 0 := hZero hAtMax
      exfalso
      linarith only [hPositive, hZeroWidth]
  have hHeight (k : ℕ) : 0 < R k ^ 2 * ε k ^ 2 / 8 := by
    have hr := hR k
    have he := hε k
    positivity
  obtain ⟨hSummable, hCharge, hBound⟩ :=
    h3Critical_disjointInternalViscousHeights_finiteRealBudget
      a T p η (fun k => R k ^ 2 * ε k ^ 2 / 8)
      hClass.terminal_start.2.le hDInt
      (fun k => (hHeight k).le)
      (fun k => (hInside k).1)
      (fun k => (hInside k).2.1)
      (fun k => (hInside k).2.2)
      (fun k => (hInternalSep k (k + 1) (Nat.lt_succ_self k)).le)
      hFloor
  have hResidual (γ : ℝ) (_hγ : 0 < γ) (n m : ℕ) :
      (((Finset.range m).filter
        (fun j : ℕ =>
          γ / (R (n + j) ^ 2 * ε (n + j) ^ 2 / 8) ≤
            η (n + j))).card : ℝ) * γ +
        (∑ k ∈ Finset.range n,
          η k * (R k ^ 2 * ε k ^ 2 / 8)) ≤
            ∫ r in a..T, velocityH3DissipationAt u r :=
    h3Critical_scalar_finiteBudget_depletedInverseHeightTailCount
      η (fun k => R k ^ 2 * ε k ^ 2 / 8)
      (∫ r in a..T, velocityH3DissipationAt u r) γ
      hHeight (fun k => (hInside k).2.1) hBound n m
  exact ⟨i, t, w, v, sSource, sState, δ, p, η, N,
    hv, hLimit, hInternalSep, hSummable, hCharge, hBound,
    hResidual, hGate⟩

end
end PrimeTensor.Bridge.Euclidean
