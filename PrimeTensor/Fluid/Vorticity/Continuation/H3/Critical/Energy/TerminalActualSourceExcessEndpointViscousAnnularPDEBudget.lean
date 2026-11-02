import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessEndpointViscousAnnularPDEPersistence
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessEndpointViscousSummability
import Mathlib.Tactic

/-!
# Finite physical H³ budget for the genuinely PDE-certified annular windows

The endpoint-spike windows of the synchronized gate were previously allowed
arbitrarily small widths. The physical finite-band PDE now constructs a
positive width with an explicit source-time / annular-variation minimum.
The new windows remain INSIDE the disjoint source windows, so finite terminal
physical H³ dissipation makes their actual height-times-width charges
summable. There is NO double counting of the original endpoint intervals.

Consequently, at every sufficiently late index, either the annular branch
is inactive, its available source-window time is insufficient to pay a fixed
charge, or its actual PDE variation coefficient is too large relative to the
square of the spike height. This is an obstruction, not terminal continuation.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- A vanishing minimum charge has only two possible small factors.  The
inactive branch is kept, and no estimate on the PDE coefficient is assumed. -/
theorem h3Critical_scalar_PDEAnnularCharge_eventualClockAlternative
    (active : ℕ → Prop) [∀ k, Decidable (active k)]
    (d H Λ θ : ℕ → ℝ)
    (hθ : ∀ k, θ k = if active k then
      min (d k / 2) ((H k / 4) / (2 * (Λ k + 1))) else 0)
    (hCharge : Tendsto (fun k => θ k * (H k / 4)) atTop (𝓝 (0 : ℝ)))
    (γ : ℝ) (hγ : 0 < γ) :
    ∀ᶠ k : ℕ in atTop,
      ¬ active k ∨
      (d k / 2) * (H k / 4) < γ ∨
      ((H k / 4) / (2 * (Λ k + 1))) * (H k / 4) < γ := by
  have hSmall : ∀ᶠ k : ℕ in atTop, θ k * (H k / 4) < γ :=
    hCharge.eventually (eventually_lt_nhds hγ)
  filter_upwards [hSmall] with k hk
  by_cases ha : active k
  · have hEq := hθ k
    rw [if_pos ha] at hEq
    rw [hEq] at hk
    by_cases hOrder : d k / 2 ≤ (H k / 4) / (2 * (Λ k + 1))
    · exact Or.inr (Or.inl (by simpa only [min_eq_left hOrder] using hk))
    · have hOrder' : (H k / 4) / (2 * (Λ k + 1)) ≤ d k / 2 :=
        le_of_not_ge hOrder
      exact Or.inr (Or.inr (by simpa only [min_eq_right hOrder'] using hk))
  · exact Or.inl ha

/-- The exact cofinal source windows, state maxima, and four-way physical
PDE/spectral gate now carry an EXPLICIT, globally summable annular PDE charge.
For every active qualifying index the width is the physical-PDE minimum, not
a continuity-chosen radius. The new intervals belong to the ORIGINAL disjoint
source windows; they are not added to the older endpoint-window charges. -/
theorem h3Critical_noL2Trace_cofinalFivefold_annularPDEBudget
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
    (L : ℕ → ℕ)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T) :
    ∃ i : Fin 3, ∃ t w : ℕ → ℝ, ∃ v : ℕ → ℕ,
    ∃ sSource sState δ p η : ℕ → ℝ, ∃ N : ℕ → ℕ,
    ∃ θ : ℕ → ℝ,
      StrictMono v ∧
      Tendsto (fun k : ℕ => t (v k)) atTop (𝓝 T) ∧
      (∀ k : ℕ, θ k = if
          η k ≠ 0 ∧
            8 * velocityH3Energy0At u b * ((L k : ℝ) + 1) ^ 8 <
              R k ^ 2 * ε k ^ 2 / 8
        then min ((t (v k) + w (v k) - p k) / 2)
          (((R k ^ 2 * ε k ^ 2 / 8) / 4) /
            (2 * (h3PathFiniteAnnulusPDEVariationCoefficient244
              ((L k : ℝ) + 1) ((N k : ℝ) + 1)
              ‖h3AuditActualSpectralVelocityTotal hH3 (sState k)‖
              ‖h3PathActualProjectedMomentumSource244 hH3 (sSource k)‖ + 1)))
        else 0) ∧
      (∀ k : ℕ, 0 ≤ θ k ∧ p k + θ k ≤ t (v k) + w (v k)) ∧
      (∀ k : ℕ, p k + θ k ≤ p (k + 1)) ∧
      Summable (fun k => θ k * (R k ^ 2 * ε k ^ 2 / 32)) ∧
      Tendsto (fun k => θ k * (R k ^ 2 * ε k ^ 2 / 32))
        atTop (𝓝 (0 : ℝ)) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m, θ k * (R k ^ 2 * ε k ^ 2 / 32)) ≤
          ∫ r in a..T, velocityH3DissipationAt u r) ∧
      (∀ γ : ℝ, 0 < γ → ∀ᶠ k : ℕ in atTop,
        ¬ (η k ≠ 0 ∧
          8 * velocityH3Energy0At u b * ((L k : ℝ) + 1) ^ 8 <
            R k ^ 2 * ε k ^ 2 / 8) ∨
        ((t (v k) + w (v k) - p k) / 2) *
          ((R k ^ 2 * ε k ^ 2 / 8) / 4) < γ ∨
        (((R k ^ 2 * ε k ^ 2 / 8) / 4) /
          (2 * (h3PathFiniteAnnulusPDEVariationCoefficient244
            ((L k : ℝ) + 1) ((N k : ℝ) + 1)
            ‖h3AuditActualSpectralVelocityTotal hH3 (sState k)‖
            ‖h3PathActualProjectedMomentumSource244 hH3 (sSource k)‖ + 1))) *
          ((R k ^ 2 * ε k ^ 2 / 8) / 4) < γ) ∧
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
  classical
  obtain ⟨i, t, w, v, sSource, sState, A, B, δ, p, η, N,
      hv, hLimit, hSep, _hShortSep, _hInternalSep,
      _hSourceCosts, _hInternalCosts, hWindows, hGate⟩ :=
    h3Critical_noL2Trace_cofinalFivefold_synchronizedEndpointViscousCosts
      hH3 hClass b hb hNoTrace c ρ σ M q
      hc hcLimit hρ hσ hM hq R ε hR hε
  let H : ℕ → ℝ := fun k => R k ^ 2 * ε k ^ 2 / 8
  let rate : ℕ → ℝ := fun k =>
    h3PathFiniteAnnulusPDEVariationCoefficient244
      ((L k : ℝ) + 1) ((N k : ℝ) + 1)
      ‖h3AuditActualSpectralVelocityTotal hH3 (sState k)‖
      ‖h3PathActualProjectedMomentumSource244 hH3 (sSource k)‖
  let d : ℕ → ℝ := fun k => t (v k) + w (v k) - p k
  let active : ℕ → Prop := fun k => η k ≠ 0 ∧
    8 * velocityH3Energy0At u b * ((L k : ℝ) + 1) ^ 8 < H k
  let θ : ℕ → ℝ := fun k =>
    if active k then min (d k / 2) ((H k / 4) / (2 * (rate k + 1)))
    else 0
  have hSelect (k : ℕ) :
      a ≤ p k ∧ 0 ≤ θ k ∧ p k + θ k ≤ t (v k) + w (v k) ∧
      (0 < θ k → ∀ r : ℝ, r ∈ Set.Icc (p k) (p k + θ k) →
        H k / 4 ≤ velocityH3DissipationAt u r) := by
    obtain ⟨ht, hw, hEnd, _hPeaks, _hsSource, _hsState, hMax,
      _hA, _hB, _hδ, _hδw, _hWidth, _hFloor,
      hp, hη, hpEnd, hSpike, hZero⟩ := hWindows k
    have hStart : a ≤ p k :=
      le_trans (le_of_lt (lt_trans hb.1 (lt_trans (hc (v k)).1 ht.1))) hp
    by_cases hActive : active k
    · have hηNonzero : η k ≠ 0 := hActive.1
      have hThreshold :
          8 * velocityH3Energy0At u b * ((L k : ℝ) + 1) ^ 8 < H k :=
        hActive.2
      have hηPos : 0 < η k := by
        have hLE : 0 ≤ η k := hη
        exact lt_of_le_of_ne hLE (Ne.symm hηNonzero)
      have hAtMax : R k ^ 2 * ε k ^ 2 <
          8 * velocityH3DissipationAt u (sState k) := by
        by_contra hNot
        exact hηNonzero (hZero hNot)
      have hpMem : p k ∈ Set.Icc (p k) (p k + η k) :=
        ⟨le_rfl, le_add_of_nonneg_right hη⟩
      have hCaptured : H k <
          h3PathActualLowRadialDissipation244 ((N k : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (p k)) := by
        simpa only [H] using ((hSpike hAtMax).2 (p k) hpMem).1
      have hTail : t (v k) ∈ Set.Ioo b T :=
        ⟨lt_trans (hc (v k)).1 ht.1, ht.2⟩
      have hL : (1 : ℝ) ≤ (L k : ℝ) + 1 := by
        have hn : (0 : ℝ) ≤ (L k : ℝ) := Nat.cast_nonneg _
        linarith only [hn]
      have hQ : (0 : ℝ) ≤ (N k : ℝ) + 1 := by positivity
      obtain ⟨z, hzPos, hzHalf, hzEq, _hzEnd, hzFloor, _hzCost⟩ :=
        h3Critical_sourceWindow_activeAnnularSpike_PDEPersistence
          hH3 hClass b hb (t (v k)) (w (v k)) (p k) (η k)
          (sSource k) (sState k) ((L k : ℝ) + 1) ((N k : ℝ) + 1)
          (H k) hTail hw hEnd hp hηPos hpEnd hMax hL hQ hCaptured
          hThreshold
      have hθz : θ k = z := by
        simp only [θ, if_pos hActive, d, rate, H]
        exact hzEq.symm
      have hzIn : p k + z ≤ t (v k) + w (v k) := by
        linarith only [hzHalf, hη, hpEnd]
      refine ⟨hStart, ?_, ?_, ?_⟩
      · rw [hθz]
        exact hzPos.le
      · rw [hθz]
        exact hzIn
      · intro hθPos r hr
        rw [hθz] at hr
        have hFloor := hzFloor r hr
        exact hFloor.1.le.trans hFloor.2
    · have hθzero : θ k = 0 := by simp only [θ, if_neg hActive]
      refine ⟨hStart, ?_, ?_, ?_⟩
      · rw [hθzero]
      · rw [hθzero]
        linarith only [hpEnd, hη]
      · intro hθPos
        rw [hθzero] at hθPos
        exact (False.elim (lt_irrefl (0 : ℝ) hθPos))
  have hStart (k : ℕ) : a ≤ p k := (hSelect k).1
  have hWidth (k : ℕ) : 0 ≤ θ k := (hSelect k).2.1
  have hEnd (k : ℕ) : p k + θ k ≤ T := by
    have hInside := (hSelect k).2.2.1
    obtain ⟨_, _, ht, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ :=
      hWindows k
    exact hInside.trans ht.le
  have hSeparate (k : ℕ) : p k + θ k ≤ p (k + 1) := by
    have hInside := (hSelect k).2.2.1
    have hSourceSep := hSep k (k + 1) (Nat.lt_succ_self k)
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hp, _, _, _, _⟩ :=
      hWindows (k + 1)
    exact (hInside.trans hSourceSep.le).trans hp
  have hHeight (k : ℕ) : 0 ≤ H k / 4 := by
    dsimp only [H]
    positivity
  have hFloor (k : ℕ) (hθPos : 0 < θ k) (r : ℝ)
      (hr : r ∈ Set.Icc (p k) (p k + θ k)) :
      H k / 4 ≤ velocityH3DissipationAt u r :=
    (hSelect k).2.2.2 hθPos r hr
  obtain ⟨hSum, hZero, hBound⟩ :=
    h3Critical_disjointInternalViscousHeights_finiteRealBudget
      a T p θ (fun k => H k / 4)
      hClass.terminal_start.2.le hDInt hHeight hStart hWidth hEnd
      hSeparate hFloor
  have hChargeEq (k : ℕ) :
      θ k * (H k / 4) = θ k * (R k ^ 2 * ε k ^ 2 / 32) := by
    dsimp only [H]
    congr 1
    ring
  have hChargeZero : Tendsto (fun k =>
      θ k * (R k ^ 2 * ε k ^ 2 / 32)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [hChargeEq] using hZero
  have hChargeSum : Summable (fun k =>
      θ k * (R k ^ 2 * ε k ^ 2 / 32)) := by
    simpa only [hChargeEq] using hSum
  have hChargeBound (m : ℕ) :
      (∑ k ∈ Finset.range m, θ k * (R k ^ 2 * ε k ^ 2 / 32)) ≤
        ∫ r in a..T, velocityH3DissipationAt u r := by
    simpa only [← hChargeEq] using hBound m
  have hThetaEq (k : ℕ) : θ k = if active k then
      min (d k / 2) ((H k / 4) / (2 * (rate k + 1))) else 0 := rfl
  have hClock (γ : ℝ) (hγ : 0 < γ) :
      ∀ᶠ k : ℕ in atTop,
        ¬ active k ∨
        (d k / 2) * (H k / 4) < γ ∨
        ((H k / 4) / (2 * (rate k + 1))) * (H k / 4) < γ :=
    h3Critical_scalar_PDEAnnularCharge_eventualClockAlternative
      active d H rate θ
      hThetaEq hZero γ hγ
  refine ⟨i, t, w, v, sSource, sState, δ, p, η, N, θ,
    hv, hLimit, ?_, ?_, hSeparate, hChargeSum, hChargeZero,
    hChargeBound, ?_, hGate⟩
  · intro k
    simpa only [active, d, H, rate] using hThetaEq k
  · intro k
    exact ⟨hWidth k, (hSelect k).2.2.1⟩
  · intro γ hγ
    simpa only [active, d, H, rate] using hClock γ hγ

end
end PrimeTensor.Bridge.Euclidean
