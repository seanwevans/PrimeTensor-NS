import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessEndpointViscousInverseHeightBarrier
import Mathlib.Tactic

/-!
# Quantitative counting of critical-height terminal persistence windows

Finite terminal physical H³ dissipation rules out more than a bounded
NUMBER of endpoint windows carrying a fixed positive charge. This is
stronger than a merely eventual inverse-height restriction: it gives an
explicit real-valued count bound by the actual physical dissipation budget.

The cofinal statement retains the SAME chosen source/spectral peaks and
physical PDE alternatives as the synchronized fivefold gate. Its endpoint
intervals are pairwise disjoint; it never combines them with the possibly
overlapping source-window family.

The finiteness of terminal H³ dissipation remains an explicit hypothesis.
No terminal uniform persistence estimate or global regularity is inferred.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- A budget for nonnegative real charges gives an *explicit* count bound
on indices whose charge reaches a fixed threshold. The threshold is paid
once for each selected index, so no source/endpoint double charging occurs. -/
theorem h3Critical_scalar_finiteBudget_boundsExpensiveIndexCount
    (charge : ℕ → ℝ) (B γ : ℝ)
    (hNonneg : ∀ k : ℕ, 0 ≤ charge k)
    (hBudget : ∀ m : ℕ,
      (∑ k ∈ Finset.range m, charge k) ≤ B)
    (m : ℕ) :
    (((Finset.range m).filter (fun k : ℕ => γ ≤ charge k)).card : ℝ) * γ ≤ B := by
  let s : Finset ℕ :=
    (Finset.range m).filter (fun k : ℕ => γ ≤ charge k)
  have hEach : ∀ k ∈ s, γ ≤ charge k := by
    intro k hk
    exact (Finset.mem_filter.mp hk).2
  have hLower : (s.card : ℝ) * γ ≤ ∑ k ∈ s, charge k := by
    calc
      (s.card : ℝ) * γ = ∑ k ∈ s, γ := by simp [mul_comm]
      _ ≤ ∑ k ∈ s, charge k := Finset.sum_le_sum hEach
  have hSubset : s ⊆ Finset.range m := Finset.filter_subset _ _
  have hUpper : (∑ k ∈ s, charge k) ≤
      ∑ k ∈ Finset.range m, charge k :=
    Finset.sum_le_sum_of_subset_of_nonneg hSubset
      (fun k _ _ => hNonneg k)
  exact (hLower.trans hUpper).trans (hBudget m)

/-- Each index satisfying width ≥ γ / height pays at least γ in real
physical budget. This counts ALL such indices, not just a terminal tail. -/
theorem h3Critical_scalar_finiteBudget_boundsInverseHeightWindowCount
    (η H : ℕ → ℝ) (B γ : ℝ)
    (hHeight : ∀ k : ℕ, 0 < H k)
    (hWidth : ∀ k : ℕ, 0 ≤ η k)
    (hBudget : ∀ m : ℕ,
      (∑ k ∈ Finset.range m, η k * H k) ≤ B)
    (m : ℕ) :
    (((Finset.range m).filter
      (fun k : ℕ => γ / H k ≤ η k)).card : ℝ) * γ ≤ B := by
  have hNonneg (k : ℕ) : 0 ≤ η k * H k :=
    mul_nonneg (hWidth k) (hHeight k).le
  have hEq :
      (Finset.range m).filter (fun k : ℕ => γ / H k ≤ η k) =
      (Finset.range m).filter (fun k : ℕ => γ ≤ η k * H k) := by
    ext k
    simp only [Finset.mem_filter]
    rw [div_le_iff₀ (hHeight k)]
  rw [hEq]
  exact h3Critical_scalar_finiteBudget_boundsExpensiveIndexCount
    (fun k => η k * H k) B γ hNonneg hBudget m

/-- Under finite terminal physical H³ dissipation, the SAME synchronized
cofinal fivefold witnesses have a finite *quantitative number* of terminal
endpoint windows of any prescribed critical inverse-height scale.

For every γ > 0 and every finite initial segment of m selected windows,

  γ · #{k < m | η(k) ≥ γ / (R(k)² ε(k)² / 8)} ≤ ∫_a^T D₃(t) dt.

The original non-spectral, finite-band PDE-clock, anchor viscosity and
positive internal-persistence alternatives survive verbatim. In particular
a late endpoint spike can exist only if it is paid for by the increasingly
short critical height-width budget. This does not force continuation. -/
theorem h3Critical_noL2Trace_cofinalFivefold_boundedCriticalWindowCount
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
        (∑ k ∈ Finset.range m, η k * (R k ^ 2 * ε k ^ 2 / 8)) ≤
          ∫ r in a..T, velocityH3DissipationAt u r) ∧
      (∀ γ : ℝ, 0 < γ → ∀ m : ℕ,
        (((Finset.range m).filter
          (fun k : ℕ => γ / (R k ^ 2 * ε k ^ 2 / 8) ≤ η k)).card : ℝ) * γ ≤
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
  have hCount (γ : ℝ) (_hγ : 0 < γ) (m : ℕ) :
      (((Finset.range m).filter
        (fun k : ℕ => γ / (R k ^ 2 * ε k ^ 2 / 8) ≤ η k)).card : ℝ) * γ ≤
          ∫ r in a..T, velocityH3DissipationAt u r :=
    h3Critical_scalar_finiteBudget_boundsInverseHeightWindowCount
      η (fun k => R k ^ 2 * ε k ^ 2 / 8)
      (∫ r in a..T, velocityH3DissipationAt u r) γ
      hHeight (fun k => (hInside k).2.1) hBound m
  exact ⟨i, t, w, v, sSource, sState, δ, p, η, N,
    hv, hLimit, hInternalSep, hSummable, hCharge, hBound,
    hCount, hGate⟩

end
end PrimeTensor.Bridge.Euclidean
