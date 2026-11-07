import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticGaugeRateRigidity
import Mathlib.Tactic

/-!
# Intermittent terminal-clock concentration and physical kinetic rate necessity

The prior exact kinetic annular clocks have vanishing height-times-width
charges under a finite global extended physical H3 dissipation budget.
An earlier rate-rigidity statement required NONCOMPRESSION EVENTUALLY.
This is stronger than necessary: concentration may recur at arbitrarily
late times while other selected windows are highly compressed.

Here any single fixed positive height-weighted terminal-clock threshold
recurring arbitrarily far along the SAME cofinal physical witness sequence
forces arbitrarily late arbitrarily large normalized kinetic PDE rates.
Conversely, an eventual bound on that normalized rate forces the entire
height-weighted terminal-clock sequence to tend to zero, including cases
with oscillatory intermittent peaks.

The physical theorem transfers both statements to the existing arbitrary-
gauge outer-cutoff witnesses without reselecting the natural outer cutoffs,
shrinking the exact PDE windows, or adding a terminal-H3 trace assumption.
No uniform outer-frequency upper bound is asserted or smuggled in.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- Recurrent noncompression (not eventual noncompression) and vanishing
exact kinetic annular charges force *arbitrarily late* superquadratic
kinetic-rate events. The repeated clock threshold is fixed; the arbitrarily
large normalized-rate comparison K is chosen independently. -/
theorem thirdFull_scalar_recurrentKineticClock_forces_cofinalRateEscape244
    (T : ℝ) (x M Λ δ : ℕ → ℝ)
    (hM : ∀ k, 0 < M k) (hΛ : ∀ k, 0 ≤ Λ k)
    (hWidth : ∀ k, δ k = min ((T - x k) / 4)
      ((M k / 4) / (2 * (Λ k + 1))))
    (hZero : Tendsto (fun k => δ k * (M k / 4))
      atTop (𝓝 (0 : ℝ)))
    (η : ℝ) (hη : 0 < η)
    (hRecurrent : ∀ k₀ : ℕ, ∃ k : ℕ,
      k₀ ≤ k ∧ η ≤ (T - x k) * M k) :
    ∀ K : ℝ, 0 ≤ K → ∀ k₀ : ℕ,
      ∃ k : ℕ, k₀ ≤ k ∧ K * (M k) ^ 2 ≤ Λ k + 1 := by
  intro K hK k₀
  have hK1 : 0 < K + 1 := by linarith only [hK]
  let ε : ℝ := min (η / 32) (1 / (32 * (K + 1)))
  have hε : 0 < ε := by
    dsimp only [ε]
    exact lt_min (by linarith only [hη]) (by positivity)
  have hεTime : ε ≤ η / 32 := by
    dsimp only [ε]
    exact min_le_left _ _
  have hTimeStrict : 16 * ε < η := by
    linarith only [hεTime, hη]
  have hPositiveDen : 0 < 32 * (K + 1) := by positivity
  have hεRate : ε * (32 * (K + 1)) ≤ 1 := by
    calc
      ε * (32 * (K + 1)) ≤
          (1 / (32 * (K + 1))) * (32 * (K + 1)) :=
        mul_le_mul_of_nonneg_right
          (show ε ≤ 1 / (32 * (K + 1)) from min_le_right _ _)
          hPositiveDen.le
      _ = 1 := by field_simp [ne_of_gt hPositiveDen]
  have hNear : ∀ᶠ k : ℕ in atTop,
      δ k * (M k / 4) < ε :=
    hZero.eventually (eventually_lt_nhds hε)
  obtain ⟨kSmall, hkSmall⟩ := Filter.eventually_atTop.mp hNear
  obtain ⟨k, hkLater, hClock⟩ :=
    hRecurrent (max k₀ kSmall)
  have hk₀ : k₀ ≤ k :=
    le_trans (le_max_left k₀ kSmall) hkLater
  have hkSmall' : kSmall ≤ k :=
    le_trans (le_max_right k₀ kSmall) hkLater
  have hCost : δ k * (M k / 4) ≤ ε := (hkSmall k hkSmall').le
  have hFork := thirdFull_scalar_exactKineticWidth_smallCharge_fork244
    T (x k) (M k) (Λ k) (δ k) ε
    (hM k).le (hΛ k) (hWidth k) hCost
  refine ⟨k, hk₀, ?_⟩
  rcases hFork with hShort | hRate
  · have hImpossible : η ≤ 16 * ε := le_trans hClock hShort
    exact False.elim ((not_le_of_gt hTimeStrict) hImpossible)
  · have hScale : 0 ≤ Λ k + 1 := by linarith only [hΛ k]
    have hUpper : (K + 1) * (M k) ^ 2 ≤ Λ k + 1 := by
      calc
        (K + 1) * (M k) ^ 2 ≤
            (K + 1) * (32 * (Λ k + 1) * ε) :=
          mul_le_mul_of_nonneg_left hRate hK1.le
        _ = (Λ k + 1) * (ε * (32 * (K + 1))) := by ring
        _ ≤ (Λ k + 1) * 1 :=
          mul_le_mul_of_nonneg_left hεRate hScale
        _ = Λ k + 1 := by ring
    nlinarith only [hUpper, sq_nonneg (M k)]

/-- An eventual upper bound on the normalized kinetic PDE rate rules out
intermittent positive height-weighted clocks: the ENTIRE sampled clock
converges to zero. The rate cap is an additional explicit hypothesis;
physical kinetic energy does not by itself supply it. -/
theorem thirdFull_scalar_boundedKineticRate_forces_terminalClockCollapse244
    (T : ℝ) (x M Λ δ : ℕ → ℝ)
    (hx : ∀ k, x k < T)
    (hM : ∀ k, 0 < M k) (hΛ : ∀ k, 0 ≤ Λ k)
    (hWidth : ∀ k, δ k = min ((T - x k) / 4)
      ((M k / 4) / (2 * (Λ k + 1))))
    (hZero : Tendsto (fun k => δ k * (M k / 4))
      atTop (𝓝 (0 : ℝ)))
    (K : ℝ) (hK : 0 ≤ K)
    (hRateCap : ∀ᶠ k : ℕ in atTop,
      Λ k + 1 ≤ K * (M k) ^ 2) :
    Tendsto (fun k : ℕ => (T - x k) * M k)
      atTop (𝓝 (0 : ℝ)) := by
  have hClockNonneg (k : ℕ) : 0 ≤ (T - x k) * M k :=
    mul_nonneg (sub_nonneg.mpr (hx k).le) (hM k).le
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hK1 : 0 < K + 1 := by linarith only [hK]
  let B : ℝ := min (ε / 32) (1 / (64 * (K + 1)))
  have hB : 0 < B := by
    dsimp only [B]
    exact lt_min (by linarith only [hε]) (by positivity)
  have hBTime : 16 * B < ε := by
    have hL : B ≤ ε / 32 := min_le_left _ _
    linarith only [hL, hε]
  have hDen : 0 < 64 * (K + 1) := by positivity
  have hBRateUpper : B * (64 * (K + 1)) ≤ 1 := by
    calc
      B * (64 * (K + 1)) ≤
          (1 / (64 * (K + 1))) * (64 * (K + 1)) :=
        mul_le_mul_of_nonneg_right
          (show B ≤ 1 / (64 * (K + 1)) from min_le_right _ _)
          hDen.le
      _ = 1 := by field_simp [ne_of_gt hDen]
  have hKB : 0 ≤ K * B := mul_nonneg hK hB.le
  have hBRate : 32 * K * B < 1 := by
    nlinarith only [hBRateUpper, hB, hKB]
  have hSmall : ∀ᶠ k : ℕ in atTop,
      δ k * (M k / 4) < B :=
    hZero.eventually (eventually_lt_nhds hB)
  have hEventually : ∀ᶠ k : ℕ in atTop,
      (T - x k) * M k < ε := by
    filter_upwards [hRateCap, hSmall] with k hkCap hkSmall
    have hFork := thirdFull_scalar_exactKineticWidth_smallCharge_fork244
      T (x k) (M k) (Λ k) (δ k) B
      (hM k).le (hΛ k) (hWidth k) hkSmall.le
    rcases hFork with hClock | hRate
    · exact lt_of_le_of_lt hClock hBTime
    · have hCompare :
          32 * (Λ k + 1) * B ≤
            32 * (K * (M k) ^ 2) * B := by
        calc
          32 * (Λ k + 1) * B =
              (Λ k + 1) * (32 * B) := by ring
          _ ≤ (K * (M k) ^ 2) * (32 * B) :=
            mul_le_mul_of_nonneg_right hkCap (by positivity)
          _ = 32 * (K * (M k) ^ 2) * B := by ring
      have hBound : (M k) ^ 2 ≤
          32 * (K * (M k) ^ 2) * B :=
        hRate.trans hCompare
      have hM2 : 0 < (M k) ^ 2 := sq_pos_of_pos (hM k)
      have hContrary :
          32 * (K * (M k) ^ 2) * B < (M k) ^ 2 := by
        calc
          32 * (K * (M k) ^ 2) * B =
              (32 * K * B) * (M k) ^ 2 := by ring
          _ < 1 * (M k) ^ 2 :=
            mul_lt_mul_of_pos_right hBRate hM2
          _ = (M k) ^ 2 := by ring
      exact False.elim ((not_lt_of_ge hBound) hContrary)
  obtain ⟨k₀, hk₀⟩ := Filter.eventually_atTop.mp hEventually
  refine ⟨k₀, ?_⟩
  intro k hk
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hClockNonneg k)]
  exact hk₀ k hk

/-- The ORIGINAL arbitrary prescribed-gauge witnesses, their exact natural
cutoffs, and their strictly separated kinetic PDE windows carry BOTH
intermittent concentration alternatives. Finite full physical extended H3
cost makes the charges vanish, but does not prove a normalized rate cap or
exclude recurrent terminal-clock peaks. -/
theorem thirdFullPhysical_noH3Trace_gaugeFiniteBudget_intermittentRateDichotomy244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L))
    (G : ℕ → ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hGlobal :
      (∫⁻ r in Set.Ioo a T,
        ENNReal.ofReal (velocityH3DissipationAt u r) ∂volume) ≤
          ENNReal.ofReal C) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (δ : ℕ → ℝ)
        (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k : ℕ => τ (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      (∀ k : ℕ, k ≤ v k ∧ G (v k) < N (v k)) ∧
      (∀ k : ℕ,
        ThirdFullKineticNaturalAnnularLocalWitness244
          hH3 b (τ (v k)) (v k) (N (v k))
          (thirdFullPhysicalKineticGaugeHeight244
            (velocityH3Energy0At u b) G (v k)) (δ (v k))) ∧
      Summable (fun k => δ (v k) *
        (thirdFullPhysicalKineticGaugeHeight244
          (velocityH3Energy0At u b) G (v k) / 4)) ∧
      Tendsto (fun k => δ (v k) *
        (thirdFullPhysicalKineticGaugeHeight244
          (velocityH3Energy0At u b) G (v k) / 4))
        atTop (𝓝 (0 : ℝ)) ∧
      (∀ η : ℝ, 0 < η →
        (∀ k₀ : ℕ, ∃ k : ℕ, k₀ ≤ k ∧
          η ≤ (T - τ (v k)) *
            thirdFullPhysicalKineticGaugeHeight244
              (velocityH3Energy0At u b) G (v k)) →
        ∀ K : ℝ, 0 ≤ K → ∀ k₀ : ℕ,
          ∃ k : ℕ, k₀ ≤ k ∧
            K * (thirdFullPhysicalKineticGaugeHeight244
                (velocityH3Energy0At u b) G (v k)) ^ 2 ≤
              thirdFullPhysicalKineticLowBandDissipationRate244
                (N (v k)) (velocityH3Energy0At u b) +
              thirdFullPhysicalKineticLowBandDissipationRate244
                (v k) (velocityH3Energy0At u b) + 1) ∧
      (∀ K : ℝ, 0 ≤ K →
        (∀ᶠ k : ℕ in atTop,
          thirdFullPhysicalKineticLowBandDissipationRate244
              (N (v k)) (velocityH3Energy0At u b) +
            thirdFullPhysicalKineticLowBandDissipationRate244
              (v k) (velocityH3Energy0At u b) + 1 ≤
            K * (thirdFullPhysicalKineticGaugeHeight244
              (velocityH3Energy0At u b) G (v k)) ^ 2) →
        Tendsto (fun k : ℕ =>
          (T - τ (v k)) * thirdFullPhysicalKineticGaugeHeight244
            (velocityH3Energy0At u b) G (v k))
          atTop (𝓝 (0 : ℝ))) := by
  let E : ℝ := velocityH3Energy0At u b
  let M : ℕ → ℝ := thirdFullPhysicalKineticGaugeHeight244 E G
  have hE : 0 ≤ E := velocityH3Energy0At_nonneg u b
  have hM (n : ℕ) : 0 < M n :=
    thirdFullPhysicalKineticGaugeHeight_pos244 E hE G n
  obtain ⟨τ, N, δ, v, hv, hCofinal, hSeparated,
      hIndexGauge, hWindows, hSummable, hZero, _hPriorRigidity⟩ :=
    thirdFullPhysical_noH3Trace_gaugeFiniteBudget_rateRigidity244
      hH3 hClass b hb hNoTrace G C hC hGlobal
  let x : ℕ → ℝ := fun k => τ (v k)
  let A : ℕ → ℝ := fun k => M (v k)
  let Λ : ℕ → ℝ := fun k =>
    thirdFullPhysicalKineticLowBandDissipationRate244
      (N (v k)) (velocityH3Energy0At u b) +
    thirdFullPhysicalKineticLowBandDissipationRate244
      (v k) (velocityH3Energy0At u b)
  let w : ℕ → ℝ := fun k => δ (v k)
  have hA (k : ℕ) : 0 < A k := hM (v k)
  have hΛ (k : ℕ) : 0 ≤ Λ k := add_nonneg
    (thirdFullPhysicalKineticLowBandDissipationRate_nonneg244 (N (v k)) _)
    (thirdFullPhysicalKineticLowBandDissipationRate_nonneg244 (v k) _)
  have hx (k : ℕ) : x k < T := by
    rcases hWindows k with ⟨_, hp, _, hend, _, _⟩
    dsimp only [x]
    linarith only [hp, hend]
  have hWidth (k : ℕ) :
      w k = min ((T - x k) / 4)
        ((A k / 4) / (2 * (Λ k + 1))) := by
    rcases hWindows k with ⟨_, _, heq, _, _, _⟩
    simpa only [w, x, A, Λ] using heq
  have hZero' : Tendsto (fun k => w k * (A k / 4))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [w, A, M, E] using hZero
  refine ⟨τ, N, δ, v, hv, hCofinal, hSeparated,
    hIndexGauge, hWindows, hSummable, hZero, ?_, ?_⟩
  · intro η hη hRecurrent K hK k₀
    have hRec : ∀ j₀ : ℕ, ∃ j : ℕ,
        j₀ ≤ j ∧ η ≤ (T - x j) * A j := by
      simpa only [x, A, M, E] using hRecurrent
    have hLate :=
      thirdFull_scalar_recurrentKineticClock_forces_cofinalRateEscape244
        T x A Λ w hA hΛ hWidth hZero' η hη hRec K hK k₀
    simpa only [Λ, A, M, E] using hLate
  · intro K hK hRateCap
    have hCap : ∀ᶠ k : ℕ in atTop,
        Λ k + 1 ≤ K * (A k) ^ 2 := by
      simpa only [Λ, A, M, E] using hRateCap
    have hClock :=
      thirdFull_scalar_boundedKineticRate_forces_terminalClockCollapse244
        T x A Λ w hx hA hΛ hWidth hZero' K hK hCap
    simpa only [x, A, M, E] using hClock

end
end PrimeTensor.FirstMonomialTriad
