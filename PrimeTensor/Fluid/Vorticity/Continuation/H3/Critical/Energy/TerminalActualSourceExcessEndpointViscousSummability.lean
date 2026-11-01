import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessEndpointViscousSynchronizedGate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEDisjointCostCollapse244
import Mathlib.Tactic

/-!
# Finite physical H³ endpoint viscosity forces vanishing cofinal charges

The synchronized cofinal spectral gate now owns its ORIGINAL selected spectral
maximizers and strictly disjoint internal finite-band persistence intervals.
Under the *additional* hypothesis that actual full physical H³ dissipation is
interval-integrable through the terminal time, these windows have a finite
TOTAL REAL budget.

A zero-width window occurs at an index without an endpoint viscous spike.
Its formal positive height must NOT be used as a pointwise floor at the
degenerate closed singleton. We mask the floor by zero on such indices,
then remove the mask from every height-width product. This prevents a
zero-width endpoint from acquiring a fictitious pointwise dissipation bound.

No terminal-uniform persistence width and no regularity conclusion follow.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- Nonnegative height floors applying only to positive-width intervals
still give a finite physical budget over disjoint time windows. At zero
width the product vanishes, regardless of the uncharged positive height. -/
theorem h3Critical_disjointInternalViscousHeights_finiteRealBudget
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    (a T : ℝ) (p η H : ℕ → ℝ)
    (haT : a ≤ T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (hH : ∀ k, 0 ≤ H k)
    (hStart : ∀ k, a ≤ p k)
    (hWidth : ∀ k, 0 ≤ η k)
    (hEnd : ∀ k, p k + η k ≤ T)
    (hSeparate : ∀ k, p k + η k ≤ p (k + 1))
    (hFloor : ∀ k, 0 < η k → ∀ r,
      r ∈ Set.Icc (p k) (p k + η k) →
        H k ≤ velocityH3DissipationAt u r) :
    Summable (fun k : ℕ => η k * H k) ∧
    Tendsto (fun k : ℕ => η k * H k) atTop (𝓝 (0 : ℝ)) ∧
    (∀ m : ℕ, (∑ k ∈ Finset.range m, η k * H k) ≤
      ∫ r in a..T, velocityH3DissipationAt u r) := by
  let F : ℕ → ℝ := fun k => if 0 < η k then H k else 0
  have hFloorMasked (k : ℕ) (r : ℝ)
      (hr : r ∈ Set.Icc (p k) (p k + η k)) :
      F k ≤ velocityH3DissipationAt u r := by
    by_cases hPositive : 0 < η k
    · simpa only [F, if_pos hPositive] using hFloor k hPositive r hr
    · simp only [F, if_neg hPositive]
      exact velocityH3DissipationAt_nonneg u r
  have hMaskProduct (k : ℕ) : η k * F k = η k * H k := by
    by_cases hPositive : 0 < η k
    · simp only [F, if_pos hPositive]
    · have hZero : η k = 0 :=
        le_antisymm (le_of_not_gt hPositive) (hWidth k)
      simp [hZero]
  have hBoundMasked := h3Path_disjointNonnegativeWindows_finiteHeightCost_le244
    (velocityH3DissipationAt u) a T p η F haT
    (fun r => velocityH3DissipationAt_nonneg u r)
    hDInt hStart hWidth hEnd hSeparate hFloorMasked
  have hBound (m : ℕ) :
      (∑ k ∈ Finset.range m, η k * H k) ≤
        ∫ r in a..T, velocityH3DissipationAt u r := by
    calc
      (∑ k ∈ Finset.range m, η k * H k) =
          ∑ k ∈ Finset.range m, η k * F k := by
            apply Finset.sum_congr rfl
            intro k _
            exact (hMaskProduct k).symm
      _ ≤ ∫ r in a..T, velocityH3DissipationAt u r := hBoundMasked m
  have hTermNonneg (k : ℕ) : 0 ≤ η k * H k :=
    mul_nonneg (hWidth k) (hH k)
  have hSummable : Summable (fun k : ℕ => η k * H k) :=
    h3Path_nonnegativeBoundedRangeSums_summable244
      (fun k => η k * H k)
      (∫ r in a..T, velocityH3DissipationAt u r)
      hTermNonneg hBound
  exact ⟨hSummable, hSummable.tendsto_atTop_zero, hBound⟩

/-- If the endpoint charge goes to zero and its physical height is
eventually at least one, the positive-width persistence time also
vanishes. This does NOT establish a uniform radius near terminal time. -/
theorem h3Critical_scalar_endpointHeightLower_forces_widthCollapse
    (η H : ℕ → ℝ)
    (hWidth : ∀ k, 0 ≤ η k)
    (hTall : ∀ᶠ k : ℕ in atTop, 1 ≤ H k)
    (hCharge : Tendsto (fun k : ℕ => η k * H k) atTop (𝓝 (0 : ℝ))) :
    Tendsto η atTop (𝓝 (0 : ℝ)) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall hWidth
  · filter_upwards [hTall] with k hk
    have hMul := mul_le_mul_of_nonneg_left hk (hWidth k)
    simpa only [mul_one] using hMul
  · exact hCharge

/-- Applied to the SAME synchronized fivefold source selection and attained
spectral maximizers. Under a finite terminal physical H³ dissipation integral,
the internal endpoint viscosity charges are summable, tend to zero, and
have all partial sums bounded by the single full physical time integral.

The original spectral alternatives survive unchanged. Source-window costs
and endpoint-internal costs are each bounded, but are NOT added, because
their respective intervals may overlap for a fixed index. -/
theorem h3Critical_noL2Trace_cofinalFivefold_endpointViscousChargeCollapse
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
  have hHeight (k : ℕ) : 0 ≤ R k ^ 2 * ε k ^ 2 / 8 := by
    positivity
  obtain ⟨hSummable, hCollapse, hBound⟩ :=
    h3Critical_disjointInternalViscousHeights_finiteRealBudget
      a T p η (fun k => R k ^ 2 * ε k ^ 2 / 8)
      hClass.terminal_start.2.le hDInt hHeight
      (fun k => (hInside k).1)
      (fun k => (hInside k).2.1)
      (fun k => (hInside k).2.2)
      (fun k => (hInternalSep k (k + 1) (Nat.lt_succ_self k)).le)
      hFloor
  exact ⟨i, t, w, v, sSource, sState, δ, p, η, N,
    hv, hLimit, hInternalSep, hSummable, hCollapse, hBound, hGate⟩

end
end PrimeTensor.Bridge.Euclidean
