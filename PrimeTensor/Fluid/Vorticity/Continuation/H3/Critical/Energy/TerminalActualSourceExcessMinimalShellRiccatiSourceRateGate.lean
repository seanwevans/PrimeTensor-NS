import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessMinimalShellRiccatiIntrinsicClock
import Mathlib.Tactic

/-!
# A Riccati-heavy minimal shell forces anchor energy or physical source-rate escape

The preexisting quadratic-sharp clock carries an independent physical
sixth/ninth-rate alternative. In its bounded cubic-charge arm, the time
compression cap at epsilon=1 is incompatible with the intrinsic Riccati
clock unless the ORIGINAL anchor already carries quadratic H3 energy.
Consequently a Riccati-heavy window requires anchor energy, an actual
12th-power physical linear-rate cost, or a 9th-power quadratic-rate cost.

In the complementary unbounded-charge arm, a finite-prefix shift proves
unbounded costs on EVERY later tail. Thus the already accepted signed-gap
accounting theorem forces recurrent Riccati windows assuming ONLY bounded
positive signed-gap replenishment, without adding the charge-divergence
premise again. Both claims retain the original selected PDE windows and
kinetic-shell witnesses. No endpoint dissipation integrability is claimed.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeMinimalSourceGate
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceMinimalSourceGate :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- A Riccati intrinsic terminal clock with R >= 1 excludes the
cubic-frequency time-compression cap at epsilon=1. -/
theorem h3Critical_scalar_intrinsicClock_excludes_cubicTimeCap
    (R d : ℝ) (hR : 1 ≤ R) (hClock : 16 < d * R) :
    ¬ R ^ 3 * (d / 4) ≤ 1 := by
  have hR2 : 1 ≤ R ^ 2 := one_le_pow₀ hR
  have hR2Pos : 0 < R ^ 2 :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hR2
  have hScaled := mul_lt_mul_of_pos_right hClock hR2Pos
  have hFour : (4 : ℝ) ≤ 4 * R ^ 2 := by
    calc
      (4 : ℝ) = 4 * 1 := by ring
      _ ≤ 4 * R ^ 2 :=
        mul_le_mul_of_nonneg_left hR2 (by norm_num : (0 : ℝ) ≤ 4)
  have hLarge : 4 * R ^ 2 < R ^ 3 * (d / 4) := by
    nlinarith only [hScaled]
  intro hCap
  linarith only [hFour, hLarge, hCap]

/-- Genuine physical source-rate obstruction on a selected Riccati-heavy
window. This is the bounded-charge sixth/ninth gate with the time cap
removed by the intrinsic clock. -/
def h3CriticalMinimalShellRiccatiSourceRateTrichotomyAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℕ → ℝ) (N : ℕ → ℕ) (C : ℕ → ℝ)
    (v : ℕ → ℕ) (k : ℕ) : Prop :=
  ((v k : ℝ) + 1) ^ 2 <
      4 * (4 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 + 1) *
        velocityH3EnergyAt u (t (v k)) ∨
  ((v k : ℝ) + 1) ^ 12 ≤
      512 * (2304 * velocityH3EnergyAt u (t (v k)) *
        (C (v k)) ^ 2 * ((N (v k) : ℝ) + 2) ^ 10 + 1) ∨
  ((v k : ℝ) + 1) ^ 9 ≤
      16 * (36 * (C (v k)) ^ 2 *
        (((N (v k) : ℝ) + 2) ^ 8 +
          ((v k : ℝ) + 2) ^ 8) + 1)

/-- A pointwise Riccati anchor/clock alternative together with the
physical epsilon=1 exact-rate alternative forces actual anchor or
linear/quadratic source-rate expenditure. -/
theorem h3Critical_minimalShellRiccatiClock_excludes_compressedRateArm
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ) (t : ℕ → ℝ) (N : ℕ → ℕ) (C : ℕ → ℝ)
    (v : ℕ → ℕ) (k : ℕ)
    (hAnchorClock :
      h3CriticalMinimalShellRiccatiAnchorOrTerminalClockAt u T t v k)
    (hRates :
      ((v k : ℝ) + 1) ^ 3 * ((T - t (v k)) / 4) ≤ 1 ∨
      ((v k : ℝ) + 1) ^ 12 ≤
        512 * (2304 * velocityH3EnergyAt u (t (v k)) *
          (C (v k)) ^ 2 * ((N (v k) : ℝ) + 2) ^ 10 + 1) ∨
      ((v k : ℝ) + 1) ^ 9 ≤
        16 * (36 * (C (v k)) ^ 2 *
          (((N (v k) : ℝ) + 2) ^ 8 +
            ((v k : ℝ) + 2) ^ 8) + 1)) :
    h3CriticalMinimalShellRiccatiSourceRateTrichotomyAt u t N C v k := by
  rcases hAnchorClock with hAnchor | hClock
  · exact Or.inl hAnchor
  · right
    rcases hRates with hCompress | hLinear | hQuadratic
    · have hR : (1 : ℝ) ≤ (v k : ℝ) + 1 := by
        have hNat : (0 : ℝ) ≤ (v k : ℝ) := Nat.cast_nonneg _
        linarith only [hNat]
      exact False.elim
        ((h3Critical_scalar_intrinsicClock_excludes_cubicTimeCap
          ((v k : ℝ) + 1) (T - t (v k)) hR hClock) hCompress)
    · exact Or.inl hLinear
    · exact Or.inr hQuadratic

/-- Unbounded nonnegative finite-prefix charges are unbounded from every
later starting index. The finite-prefix correction is exact and costs no
additional asymptotic hypothesis. -/
theorem h3Critical_scalar_unboundedNonnegativePrefix_forces_everyTail
    (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k)
    (hUnbounded : ∀ M : ℝ, ∃ q : ℕ,
      M < ∑ k ∈ Finset.range q, c k) :
    ∀ b : ℕ, ∀ M : ℝ, ∃ q : ℕ,
      M < ∑ i ∈ Finset.range (q + 1), c (i + b) := by
  intro b M
  let P : ℝ := ∑ k ∈ Finset.range b, c k
  obtain ⟨n, hLarge⟩ := hUnbounded (max (M + P) P)
  have hPrefixLarge : P < ∑ k ∈ Finset.range n, c k :=
    lt_of_le_of_lt (le_max_right _ _) hLarge
  have hbn : b ≤ n := by
    by_contra hNo
    have hnb : n ≤ b := Nat.le_of_lt (Nat.lt_of_not_ge hNo)
    have hTailNonneg : 0 ≤ ∑ i ∈ Finset.range (b - n), c (n + i) :=
      Finset.sum_nonneg (fun i _ => hc (n + i))
    have hSplit : (∑ k ∈ Finset.range b, c k) =
        (∑ k ∈ Finset.range n, c k) +
          ∑ i ∈ Finset.range (b - n), c (n + i) := by
      have hEq : n + (b - n) = b := Nat.add_sub_of_le hnb
      simpa only [hEq] using (Finset.sum_range_add c n (b - n))
    dsimp only [P] at hPrefixLarge
    linarith only [hPrefixLarge, hSplit, hTailNonneg]
  have hSplit : (∑ k ∈ Finset.range n, c k) =
      P + ∑ i ∈ Finset.range (n - b), c (b + i) := by
    have hEq : b + (n - b) = n := Nat.add_sub_of_le hbn
    simpa only [P, hEq] using (Finset.sum_range_add c b (n - b))
  have hM : M + P ≤ max (M + P) P := le_max_left _ _
  have hTailLarge : M < ∑ i ∈ Finset.range (n - b), c (b + i) := by
    linarith only [hLarge, hM, hSplit]
  have hLast : 0 ≤ c (b + (n - b)) := hc _
  have hMore : M < ∑ i ∈ Finset.range ((n - b) + 1), c (b + i) := by
    rw [Finset.sum_range_succ]
    linarith only [hTailLarge, hLast]
  refine ⟨n - b, ?_⟩
  have hSumEq :
      (∑ i ∈ Finset.range ((n - b) + 1), c (i + b)) =
      ∑ i ∈ Finset.range ((n - b) + 1), c (b + i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Nat.add_comm]
  rw [hSumEq]
  exact hMore

/-- The exact quadratic-sharp sixth/ninth alternative splits into:
(1) unbounded actual cubic charges; or (2) an EVENTUAL implication from
an actual Riccati-heavy window to quadratic anchor, twelfth-power linear
PDE rate, or ninth-power quadratic PDE rate. -/
theorem h3Critical_minimalShellPhysicalRates_refine_RiccatiClock
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ) (t : ℕ → ℝ) (N : ℕ → ℕ) (C δ : ℕ → ℝ)
    (v : ℕ → ℕ)
    (hRates : h3CriticalMinimalShellPhysicalSixthNinthAlternative (u := u)
      T t N C δ v)
    (hLocal : ∀ᶠ k : ℕ in atTop,
      h3CriticalMinimalShellRiccatiWindowAt u t δ v k →
        h3CriticalMinimalShellRiccatiAnchorOrTerminalClockAt u T t v k) :
    (∀ M : ℝ, ∃ q : ℕ,
      M < ∑ k ∈ Finset.range q,
        h3CriticalMinimalShellCubicWindowCost δ v k) ∨
    (∀ᶠ k : ℕ in atTop,
      h3CriticalMinimalShellRiccatiWindowAt u t δ v k →
        h3CriticalMinimalShellRiccatiSourceRateTrichotomyAt u t N C v k) := by
  rcases hRates with hDivergent | hQuantified
  · left
    intro M
    obtain ⟨q, hq⟩ := hDivergent M
    exact ⟨q, by
      simpa only [h3CriticalMinimalShellCubicWindowCost] using hq⟩
  · right
    have hOne := hQuantified 1 (by norm_num : (0 : ℝ) < 1)
    filter_upwards [hLocal, hOne] with k hLocalK hGate
    intro hRiccati
    exact h3Critical_minimalShellRiccatiClock_excludes_compressedRateArm
      u T t N C v k (hLocalK hRiccati) (by simpa using hGate)

/-- SAME no-terminal-L2-trace physical first-crossing witnesses: either
unbounded cubic charges (which now AUTOMATICALLY yield every-tail charge
divergence), so bounded positive gap compensation alone forces recurring
Riccati clocks; or every late Riccati-heavy window must pay quadratic anchor
energy or a genuine twelfth/ninth PDE-rate obstruction. -/
theorem h3Critical_noL2Trace_minimalShell_riccatiClock_sourceRateDichotomy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ t : ℕ → ℝ, ∃ N m : ℕ → ℕ, ∃ C δ : ℕ → ℝ,
    ∃ v j : ℕ → ℕ, ∃ k₁ : ℕ,
      StrictMono v ∧
      Tendsto (fun k => t (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → t (v k) + δ (v k) < t (v l)) ∧
      (∀ k : ℕ, h3CriticalMinimalShellEnergyWindow
        hH3 (t (v k)) (v k) (N (v k)) (m (v k))
        (C (v k)) (δ (v k))) ∧
      h3CriticalMinimalShellPhysicalSixthNinthAlternative (u := u)
        T t N C δ v ∧
      (∀ k : ℕ,
        1 < 4 * (velocityH3EnergyAt u (t (v k)) / ((v k : ℝ) + 1)) *
          (((N (v k) : ℝ) + 2) / ((v k : ℝ) + 1)) ^ 2) ∧
      (∀ᶠ k : ℕ in atTop,
        v k ≤ j k ∧ j k < N (v k) ∧
        0 < h3PathActualBandRawKineticMass244
          ((j k : ℝ) + 1) ((j k : ℝ) + 2)
          (h3AuditActualSpectralVelocityTotal hH3 (t (v k)))) ∧
      (∀ k : ℕ, k₁ ≤ k →
        h3CriticalMinimalShellSignedTransportBudgetAt
          hH3 (t (v k)) (v k) (δ (v k))) ∧
      h3CriticalMinimalShellEveryTailSignedAccounting u t δ v k₁ ∧
      (∀ᶠ k : ℕ in atTop,
        h3CriticalMinimalShellRiccatiWindowAt u t δ v k →
          h3CriticalMinimalShellRiccatiAnchorOrTerminalClockAt u T t v k) ∧
      ((h3CriticalMinimalShellEveryTailGapBudget u t δ v k₁ →
          ∀ b : ℕ, ∃ i : ℕ, b ≤ i ∧
            h3CriticalMinimalShellRiccatiAnchorOrTerminalClockAt
              u T t v (i + k₁)) ∨
        (∀ᶠ k : ℕ in atTop,
          h3CriticalMinimalShellRiccatiWindowAt u t δ v k →
            h3CriticalMinimalShellRiccatiSourceRateTrichotomyAt
              u t N C v k)) := by
  obtain ⟨t, N, m, C, δ, v, j, k₁, hv, hLimit, hSeparate,
      hWindow, hRates, hEnergyWidth, hShell, hSigned, hAccounting,
      hLocal, hRecurring⟩ :=
    h3Critical_noL2Trace_minimalShell_cofinalRiccatiAnchorOrTerminalClock
      hH3 hClass hNoTrace
  have hRefined := h3Critical_minimalShellPhysicalRates_refine_RiccatiClock
    u T t N C δ v hRates hLocal
  have hFinal :
      (h3CriticalMinimalShellEveryTailGapBudget u t δ v k₁ →
        ∀ b : ℕ, ∃ i : ℕ, b ≤ i ∧
          h3CriticalMinimalShellRiccatiAnchorOrTerminalClockAt
            u T t v (i + k₁)) ∨
      (∀ᶠ k : ℕ in atTop,
        h3CriticalMinimalShellRiccatiWindowAt u t δ v k →
          h3CriticalMinimalShellRiccatiSourceRateTrichotomyAt
            u t N C v k) := by
    rcases hRefined with hRaw | hStrong
    · left
      have hc (k : ℕ) :
          0 ≤ h3CriticalMinimalShellCubicWindowCost δ v k := by
        have hW := hWindow k
        rcases hW with ⟨_, _, _, _, hδ, _⟩
        dsimp only [h3CriticalMinimalShellCubicWindowCost]
        positivity
      have hAll := h3Critical_scalar_unboundedNonnegativePrefix_forces_everyTail
        (h3CriticalMinimalShellCubicWindowCost δ v) hc hRaw
      have hCharge : h3CriticalMinimalShellEveryTailCubicChargeUnbounded
          δ v k₁ := by
        intro b M
        obtain ⟨q, hq⟩ := hAll (b + k₁) M
        refine ⟨q, ?_⟩
        simpa only [Nat.add_assoc] using hq
      exact hRecurring hCharge
    · exact Or.inr hStrong
  exact ⟨t, N, m, C, δ, v, j, k₁, hv, hLimit, hSeparate,
    hWindow, hRates, hEnergyWidth, hShell, hSigned, hAccounting,
    hLocal, hFinal⟩

end
end PrimeTensor.Bridge.Euclidean
