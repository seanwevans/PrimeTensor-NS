import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Critical.Normalized.Geometry

/-!
# Derived dissipation and imbalance cascades at critical half-share

At the critical balance share `theta = 1/2`, the normalized geometry gives

* `D / B -> 1/2`, and
* `I / B -> 1`.

Since the canonical balance amplitude already diverges in raw units, physical
terminal-clock units, and after normalization by the full H³ energy, both full
H³ dissipation and absolute balance imbalance inherit those three divergence
modes on the same critical sequence.

This transfer uses only a fixed positive lower fraction of `B`.  It therefore
does not claim the unchanged pointwise cubic polynomial constants for `D` or
`I`; those would require a stronger pointwise comparison than an asymptotic
positive ratio.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

private theorem tendsto_atTop_of_eventually_const_mul_le_criticalDerived
    {f g : ℕ → ℝ}
    {delta : ℝ}
    (hdelta : 0 < delta)
    (hg : Tendsto g atTop atTop)
    (hLower : ∀ᶠ n : ℕ in atTop, delta * g n ≤ f n) :
    Tendsto f atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro M
  let R : ℝ := M / delta
  have hEventuallyG :
      ∀ᶠ n : ℕ in atTop, R ≤ g n :=
    hg.eventually (eventually_ge_atTop R)
  filter_upwards [hEventuallyG, hLower] with n hGn hFn
  have hMLe : M ≤ delta * g n := by
    dsimp only [R] at hGn
    simpa only [mul_comm] using ((div_le_iff₀ hdelta).1 hGn)
  exact le_trans hMLe hFn

private theorem terminalQuantity_clockCascade_of_positive_amplitude_ratio
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T theta c : ℝ}
    {τ : ℕ → ℝ}
    {Q : ℕ → ℝ}
    (hAt : ∀ n : ℕ, τ n < T)
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta)
    (hc : 0 < c)
    (hRatio :
      Tendsto
        (fun n : ℕ =>
          Q n / h3TerminalBalanceAmplitudeAt u (τ n))
        atTop (𝓝 c)) :
    Tendsto Q atTop atTop
      ∧
    Tendsto
      (fun n : ℕ => (T - τ n) * Q n)
      atTop atTop
      ∧
    Tendsto
      (fun n : ℕ => Q n / velocityH3EnergyAt u (τ n))
      atTop atTop := by
  let delta : ℝ := c / 2

  have hdeltaPos : 0 < delta := by
    dsimp only [delta]
    exact div_pos hc (by norm_num)

  have hdeltaLt : delta < c := by
    dsimp only [delta]
    linarith

  have hRatioLower :
      ∀ᶠ n : ℕ in atTop,
        delta < Q n / h3TerminalBalanceAmplitudeAt u (τ n) :=
    hRatio.eventually (Ioi_mem_nhds hdeltaLt)

  have hAmplitudePos :
      ∀ᶠ n : ℕ in atTop,
        0 < h3TerminalBalanceAmplitudeAt u (τ n) :=
    hCluster.1.2.1.eventually
      (eventually_gt_atTop (0 : ℝ))

  have hQuantityLower :
      ∀ᶠ n : ℕ in atTop,
        delta * h3TerminalBalanceAmplitudeAt u (τ n) ≤ Q n := by
    filter_upwards [hRatioLower, hAmplitudePos] with n hRatioN hAmplitudeN
    exact le_of_lt ((lt_div_iff₀ hAmplitudeN).1 hRatioN)

  have hRaw : Tendsto Q atTop atTop :=
    tendsto_atTop_of_eventually_const_mul_le_criticalDerived
      hdeltaPos
      hCluster.1.2.1
      hQuantityLower

  have hClockLower :
      ∀ᶠ n : ℕ in atTop,
        delta *
            ((T - τ n) * h3TerminalBalanceAmplitudeAt u (τ n))
          ≤
        (T - τ n) * Q n := by
    filter_upwards [hQuantityLower] with n hn
    have hTimeNonneg : 0 ≤ T - τ n :=
      sub_nonneg.mpr (hAt n).le
    have hMul :=
      mul_le_mul_of_nonneg_left hn hTimeNonneg
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hMul

  have hClock :
      Tendsto
        (fun n : ℕ => (T - τ n) * Q n)
        atTop atTop :=
    tendsto_atTop_of_eventually_const_mul_le_criticalDerived
      hdeltaPos
      hCluster.1.2.2.1
      hClockLower

  have hNormalizedLower :
      ∀ᶠ n : ℕ in atTop,
        delta *
            (h3TerminalBalanceAmplitudeAt u (τ n) /
              velocityH3EnergyAt u (τ n))
          ≤
        Q n / velocityH3EnergyAt u (τ n) := by
    filter_upwards [hQuantityLower] with n hn
    have hEnergyPos :
        0 < velocityH3EnergyAt u (τ n) := by
      have hOne := one_le_velocityH3EnergyAt u (τ n)
      linarith
    have hDiv :
        (delta * h3TerminalBalanceAmplitudeAt u (τ n)) /
            velocityH3EnergyAt u (τ n)
          ≤
        Q n / velocityH3EnergyAt u (τ n) :=
      (div_le_div_iff_of_pos_right hEnergyPos).2 hn
    simpa only [mul_div_assoc] using hDiv

  have hNormalized :
      Tendsto
        (fun n : ℕ => Q n / velocityH3EnergyAt u (τ n))
        atTop atTop :=
    tendsto_atTop_of_eventually_const_mul_le_criticalDerived
      hdeltaPos
      hCluster.1.2.2.2.1
      hNormalizedLower

  exact ⟨hRaw, hClock, hNormalized⟩

/-- Raw, physical-clock, and energy-normalized divergence of both full H³
+dissipation and absolute balance imbalance on one critical half-share sequence. -/
def H3TerminalBalanceCriticalDissipationImbalanceClockCascadeAlong
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ)
    (τ : ℕ → ℝ) : Prop :=
  Tendsto
      (fun n : ℕ => velocityH3DissipationAt u (τ n))
      atTop atTop
    ∧
  Tendsto
      (fun n : ℕ =>
        (T - τ n) * velocityH3DissipationAt u (τ n))
      atTop atTop
    ∧
  Tendsto
      (fun n : ℕ =>
        velocityH3DissipationAt u (τ n) /
          velocityH3EnergyAt u (τ n))
      atTop atTop
    ∧
  Tendsto
      (fun n : ℕ => h3TerminalBalanceImbalanceAt u (τ n))
      atTop atTop
    ∧
  Tendsto
      (fun n : ℕ =>
        (T - τ n) * h3TerminalBalanceImbalanceAt u (τ n))
      atTop atTop
    ∧
  Tendsto
      (fun n : ℕ =>
        h3TerminalBalanceImbalanceAt u (τ n) /
          velocityH3EnergyAt u (τ n))
      atTop atTop

/-- At critical half-share, dissipation and imbalance inherit all three amplitude
+divergence modes on the same share-cluster sequence. -/
theorem h3TerminalBalanceCriticalDissipationImbalanceClockCascadeAlong_of_shareCluster_eq_half
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a theta : ℝ}
    {τ : ℕ → ℝ}
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta)
    (hTheta : theta = (1 : ℝ) / 2) :
    H3TerminalBalanceCriticalDissipationImbalanceClockCascadeAlong u T τ := by
  have hDissipationRatio :=
    h3TerminalBalanceDissipation_div_amplitude_tendsto_half_of_shareCluster_eq_half
      hCluster hTheta

  have hImbalanceRatio :=
    h3TerminalBalanceImbalance_div_amplitude_tendsto_one_of_shareCluster_eq_half
      hCluster hTheta

  have hDissipation :=
    terminalQuantity_clockCascade_of_positive_amplitude_ratio
      (u := u)
      (T := T)
      (theta := theta)
      (τ := τ)
      (Q := fun n : ℕ => velocityH3DissipationAt u (τ n))
      (c := (1 : ℝ) / 2)
      (fun n => (hAt n).2)
      hCluster
      (by norm_num)
      hDissipationRatio

  have hImbalance :=
    terminalQuantity_clockCascade_of_positive_amplitude_ratio
      (u := u)
      (T := T)
      (theta := theta)
      (τ := τ)
      (Q := fun n : ℕ => h3TerminalBalanceImbalanceAt u (τ n))
      (c := (1 : ℝ))
      (fun n => (hAt n).2)
      hCluster
      (by norm_num)
      hImbalanceRatio

  exact
    ⟨
      hDissipation.1,
      hDissipation.2.1,
      hDissipation.2.2,
      hImbalance.1,
      hImbalance.2.1,
      hImbalance.2.2
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
