import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessEndpointDrainReplenishment
import Mathlib.Tactic

/-!
# Finite cumulative physical H³ source-window drain versus signed transport replenishment

For the ALREADY SELECTED source-excess windows, the previous endpoint theorem
provides either a genuine Riccati energy witness or an actual H³ endpoint
loss H_k δ_k. The losses can be added without discarding their signs. The
exact physical energy identity and real mean-value theorem give an actual
sample s_k in each intervening gap with

  E(t_{k+1}) - E(t_k+δ_k)
    = (t_{k+1}-t_k-δ_k) (-Transport(s_k)-2 D(s_k)).

Consequently, up to any finite index, either a window has a large Riccati
energy witness or the ENTIRE enhanced physical drain is paid by the initial
H³ energy and positive signed transport overshoots in the gaps.

There is no terminal-uniform energy/transport bound, no assumption that the
full H³ dissipation is integrable up to T, and no global continuation claim.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- Finite discrete energy accounting: all window losses telescope,
while the gap influxes remain explicitly charged. If even one window
uses its nonlinear-energy branch, that witness is kept instead. -/
theorem h3Critical_scalar_finiteDrainOrReplenishmentAccounting
    (x y c g : ℕ → ℝ) (P : ℕ → Prop)
    (hWindow : ∀ k, P k ∨ c k + y k ≤ x k)
    (hGap : ∀ k, x (k + 1) - y k ≤ g k) :
    ∀ m : ℕ,
      (∃ k : ℕ, k ≤ m ∧ P k) ∨
      (∑ k ∈ Finset.range (m + 1), c k) + y m ≤
        x 0 + ∑ k ∈ Finset.range m, g k := by
  intro m
  induction m with
  | zero =>
      rcases hWindow 0 with hp | hd
      · exact Or.inl ⟨0, le_rfl, hp⟩
      · right
        simpa only [Finset.sum_range_succ, Finset.sum_range_zero,
          zero_add, add_zero] using hd
  | succ m ih =>
      rcases ih with ⟨k, hk, hp⟩ | hPrevious
      · exact Or.inl ⟨k, le_trans hk (Nat.le_succ m), hp⟩
      · rcases hWindow (m + 1) with hp | hNext
        · exact Or.inl ⟨m + 1, le_rfl, hp⟩
        · right
          have hBridge := hGap m
          simp only [Finset.sum_range_succ] at hPrevious ⊢
          linarith only [hPrevious, hNext, hBridge]

/-- Differentiability on one compact real gap realizes its FULL signed
energy change as an exact derivative-times-gap-width. No integrability
of the derivative is assumed. -/
theorem h3Critical_scalar_gapEnergy_exactMeanValueSecant
    (E : ℝ → ℝ) (x y : ℝ) (hxy : x < y)
    (hDiff : ∀ s ∈ Set.Icc x y, DifferentiableAt ℝ E s) :
    ∃ s : ℝ, s ∈ Set.Ioo x y ∧
      E y - E x = (y - x) * deriv E s := by
  have hContinuous : ContinuousOn E (Set.Icc x y) := by
    intro s hs
    exact (hDiff s hs).continuousAt.continuousWithinAt
  have hDifferent : DifferentiableOn ℝ E (Set.Ioo x y) := by
    intro s hs
    exact (hDiff s ⟨hs.1.le, hs.2.le⟩).differentiableWithinAt
  obtain ⟨s, hs, hSlope⟩ :=
    exists_deriv_eq_slope E hxy hContinuous hDifferent
  have hPositive : 0 < y - x := sub_pos.mpr hxy
  have hScaled : deriv E s * (y - x) = E y - E x :=
    (eq_div_iff (ne_of_gt hPositive)).mp hSlope
  refine ⟨s, hs, ?_⟩
  calc
    E y - E x = deriv E s * (y - x) := hScaled.symm
    _ = (y - x) * deriv E s := mul_comm _ _

/-- Every genuine inter-window H³ energy gain OR loss has a physical
mean-value representative of the EXACT signed Navier--Stokes balance.
Unlike the previous positive-slope theorem this records the quantitative
signed secant even when the gap's net gain is negative. -/
theorem h3Critical_physicalH3Gap_exactSignedTransportSecant
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (x y : ℝ) (hx : x ∈ Set.Ioo a T)
    (hy : y ∈ Set.Ioo a T) (hxy : x < y) :
    ∃ s : ℝ, s ∈ Set.Ioo x y ∧
      velocityH3EnergyAt u y - velocityH3EnergyAt u x =
        (y - x) * (-velocityH3TransportDerivativeAt u s -
          2 * velocityH3DissipationAt u s) := by
  have hDiff (r : ℝ) (hr : r ∈ Set.Icc x y) :
      DifferentiableAt ℝ (velocityH3EnergyAt u) r := by
    have hrClass : r ∈ Set.Ioo a T :=
      ⟨lt_of_lt_of_le hx.1 hr.1, lt_of_le_of_lt hr.2 hy.2⟩
    exact h3Critical_actualH3Energy_differentiableAt_onStrict
      hH3 hClass hrClass
  obtain ⟨s, hs, hSecant⟩ :=
    h3Critical_scalar_gapEnergy_exactMeanValueSecant
      (velocityH3EnergyAt u) x y hxy hDiff
  have hsClass : s ∈ Set.Ioo a T :=
    ⟨lt_trans hx.1 hs.1, lt_trans hs.2 hy.2⟩
  have hBalance :=
    deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3 hClass hsClass
  have hSlope : deriv (velocityH3EnergyAt u) s =
      -velocityH3TransportDerivativeAt u s -
        2 * velocityH3DissipationAt u s := by
    linarith only [hBalance]
  refine ⟨s, hs, ?_⟩
  calc
    velocityH3EnergyAt u y - velocityH3EnergyAt u x =
        (y - x) * deriv (velocityH3EnergyAt u) s := hSecant
    _ = (y - x) * (-velocityH3TransportDerivativeAt u s -
          2 * velocityH3DissipationAt u s) := by rw [hSlope]

/-- An aggregate physical drain greater than the initial available energy
requires at least one strictly positive signed-transport contribution among
the measured intervening gaps. This is a FINITE result and has no
hidden terminal-integrability assumption. -/
theorem h3Critical_scalar_cumulativeOverdraft_forces_positiveGapRate
    (m : ℕ) (c width rate : ℕ → ℝ) (Einitial : ℝ)
    (hBudget :
      (∑ k ∈ Finset.range (m + 1), c k) + 1 ≤
        Einitial + ∑ k ∈ Finset.range m, width k * max 0 (rate k))
    (hOverdraft :
      Einitial < (∑ k ∈ Finset.range (m + 1), c k) + 1) :
    ∃ k : ℕ, k < m ∧ 0 < rate k := by
  by_contra hNone
  have hNonpositive (k : ℕ) (hk : k ∈ Finset.range m) :
      rate k ≤ 0 := by
    apply le_of_not_gt
    intro hPos
    exact hNone ⟨k, Finset.mem_range.mp hk, hPos⟩
  have hSumZero :
      (∑ k ∈ Finset.range m, width k * max 0 (rate k)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [max_eq_left (hNonpositive k hk)]
    ring
  rw [hSumZero] at hBudget
  linarith only [hBudget, hOverdraft]

/-- The cofinal SOURCE-EXCESS witnesses of the accepted quintic theorem
have a single real PDE sample in EVERY intervening gap. At each finite
stage, either one of the same physical windows pays the Riccati H³-energy
alternative, or their cumulative enhanced dissipation losses are covered
by the initial energy and positive signed transport generated in the gaps.
In the latter case an energy overdraft forces an actual transport overshoot
on an intervening gap. No terminal-uniform bound is introduced. -/
theorem h3Critical_noL2Trace_cofinalQuintic_cumulativeSignedReplenishment
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
    (hq : ∀ n, 0 < q n) :
    ∃ t w : ℕ → ℝ, ∃ v : ℕ → ℕ,
    ∃ δ gapSample : ℕ → ℝ,
      StrictMono v ∧
      Tendsto (fun k : ℕ => t (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → t (v k) + δ k < t (v l)) ∧
      (∀ k : ℕ,
        0 < δ k ∧
        gapSample k ∈ Set.Ioo (t (v k) + δ k) (t (v (k + 1))) ∧
        velocityH3EnergyAt u (t (v (k + 1))) -
          velocityH3EnergyAt u (t (v k) + δ k) =
          (t (v (k + 1)) - (t (v k) + δ k)) *
            (-velocityH3TransportDerivativeAt u (gapSample k) -
              2 * velocityH3DissipationAt u (gapSample k))) ∧
      (∀ m : ℕ,
        (∃ k : ℕ, k ≤ m ∧
          ∃ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + δ k) ∧
            h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) <
              h3PathSqrtEnergyRiccatiCoefficient *
                Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s) ∨
        (∑ k ∈ Finset.range (m + 1),
          h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) * δ k) + 1 ≤
          velocityH3EnergyAt u (t (v 0)) +
            ∑ k ∈ Finset.range m,
              (t (v (k + 1)) - (t (v k) + δ k)) *
                max 0 (-velocityH3TransportDerivativeAt u (gapSample k) -
                  2 * velocityH3DissipationAt u (gapSample k))) := by
  obtain ⟨t, w, v, _A, _B, _R, δ, hv, hLimit,
      hSeparated, hWindows, _hReplenish, _hCosts, _hGate⟩ :=
    h3Critical_noL2Trace_cofinalQuintic_endpointDrain_or_gapTransport
      hH3 hClass b hb hNoTrace c ρ σ M q hc hcLimit hρ hσ hM hq
  have hSample (k : ℕ) :
      ∃ s : ℝ, s ∈ Set.Ioo (t (v k) + δ k) (t (v (k + 1))) ∧
        velocityH3EnergyAt u (t (v (k + 1))) -
          velocityH3EnergyAt u (t (v k) + δ k) =
          (t (v (k + 1)) - (t (v k) + δ k)) *
            (-velocityH3TransportDerivativeAt u s -
              2 * velocityH3DissipationAt u s) := by
    have hSep : t (v k) + δ k < t (v (k + 1)) :=
      hSeparated k (k + 1) (Nat.lt_succ_self k)
    obtain ⟨hStartK, _hwK, hEndK, _hRK, hδK, hδwK,
        _hWidthK, _hAltK⟩ := hWindows k
    obtain ⟨hStartL, _hwL, _hEndL, _hRL, _hδL, _hδwL,
        _hWidthL, _hAltL⟩ := hWindows (k + 1)
    have hx : t (v k) + δ k ∈ Set.Ioo a T := by
      have hStartA : a < t (v k) :=
        lt_trans hb.1 (lt_trans (hc (v k)).1 hStartK.1)
      have hShort : t (v k) + δ k ≤ t (v k) + w (v k) :=
        add_le_add_right hδwK (t (v k))
      exact ⟨by linarith only [hStartA, hδK],
        lt_of_le_of_lt hShort hEndK⟩
    have hy : t (v (k + 1)) ∈ Set.Ioo a T :=
      ⟨lt_trans hb.1 (lt_trans (hc (v (k + 1))).1 hStartL.1), hStartL.2⟩
    exact h3Critical_physicalH3Gap_exactSignedTransportSecant
      hH3 hClass _ _ hx hy hSep
  choose gapSample hGapInside hGapIdentity using hSample
  let x : ℕ → ℝ := fun k => velocityH3EnergyAt u (t (v k))
  let y : ℕ → ℝ := fun k => velocityH3EnergyAt u (t (v k) + δ k)
  let cost : ℕ → ℝ := fun k =>
    h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) * δ k
  let P : ℕ → Prop := fun k =>
    ∃ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + δ k) ∧
      h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) <
        h3PathSqrtEnergyRiccatiCoefficient *
          Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s
  let supply : ℕ → ℝ := fun k =>
    (t (v (k + 1)) - (t (v k) + δ k)) *
      max 0 (-velocityH3TransportDerivativeAt u (gapSample k) -
        2 * velocityH3DissipationAt u (gapSample k))
  have hStep (k : ℕ) : P k ∨ cost k + y k ≤ x k := by
    obtain ⟨_hStart, _hw, _hEnd, _hR, _hδ, _hδw,
      _hWidth, hAlternative⟩ := hWindows k
    rcases hAlternative with hLarge | hDrain
    · exact Or.inl hLarge
    · right
      dsimp only [cost, y, x]
      linarith only [hDrain]
  have hGapBound (k : ℕ) : x (k + 1) - y k ≤ supply k := by
    change velocityH3EnergyAt u (t (v (k + 1))) -
      velocityH3EnergyAt u (t (v k) + δ k) ≤ supply k
    rw [hGapIdentity k]
    dsimp only [supply]
    have hWidth : 0 ≤ t (v (k + 1)) - (t (v k) + δ k) :=
      (sub_pos.mpr (hSeparated k (k + 1) (Nat.lt_succ_self k))).le
    exact mul_le_mul_of_nonneg_left (le_max_right 0 _) hWidth
  have hFinite := h3Critical_scalar_finiteDrainOrReplenishmentAccounting
    x y cost supply P hStep hGapBound
  refine ⟨t, w, v, δ, gapSample, hv, hLimit, hSeparated, ?_, ?_⟩
  · intro k
    have hδ : 0 < δ k := (hWindows k).2.2.2.2.1
    exact ⟨hδ, hGapInside k, hGapIdentity k⟩
  · intro m
    rcases hFinite m with ⟨k, hk, hp⟩ | hAccounting
    · exact Or.inl ⟨k, hk, hp⟩
    · right
      have hNonnegativeEnergy : 1 ≤ y m := by
        dsimp only [y]
        exact one_le_velocityH3EnergyAt u (t (v m) + δ m)
      have hBound :
          (∑ k ∈ Finset.range (m + 1), cost k) + 1 ≤
            x 0 + ∑ k ∈ Finset.range m, supply k := by
        calc
          (∑ k ∈ Finset.range (m + 1), cost k) + 1 ≤
              (∑ k ∈ Finset.range (m + 1), cost k) + y m :=
            add_le_add_right hNonnegativeEnergy _
          _ ≤ x 0 + ∑ k ∈ Finset.range m, supply k := hAccounting
      exact hBound

end
end PrimeTensor.Bridge.Euclidean
