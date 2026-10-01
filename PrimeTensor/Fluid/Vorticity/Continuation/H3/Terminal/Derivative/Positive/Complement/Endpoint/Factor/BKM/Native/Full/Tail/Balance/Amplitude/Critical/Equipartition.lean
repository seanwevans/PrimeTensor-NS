import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Critical.Derived.Cascades
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Transport.Shares

/-!
# Critical half-share equipartition

At the critical balance share `theta = 1/2`, the normalized share geometry can
be expressed directly relative to twice the full H³ dissipation.

Along the same critical share-cluster sequence,

* `B / (2 D) -> 1`,
* `I / (2 D) -> 1`, and
* `S / (2 D) -> 0`.

Thus the canonical amplitude and the absolute channel imbalance are
asymptotically equivalent to twice full dissipation, while the subordinate
signed balance channel is lower order on that same scale.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Direct critical equipartition relative to twice full H³ dissipation. -/
def H3TerminalBalanceCriticalEquipartitionAlong
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (τ : ℕ → ℝ) : Prop :=
  Tendsto
      (fun n : ℕ =>
        h3TerminalBalanceAmplitudeAt u (τ n) /
          (2 * velocityH3DissipationAt u (τ n)))
      atTop (𝓝 (1 : ℝ))
    ∧
  Tendsto
      (fun n : ℕ =>
        h3TerminalBalanceImbalanceAt u (τ n) /
          (2 * velocityH3DissipationAt u (τ n)))
      atTop (𝓝 (1 : ℝ))
    ∧
  Tendsto
      (fun n : ℕ =>
        h3TerminalBalanceSubordinateChannelAt u (τ n) /
          (2 * velocityH3DissipationAt u (τ n)))
      atTop (𝓝 (0 : ℝ))

/-- At critical half-share, amplitude and imbalance are both asymptotic to twice
full dissipation, while the subordinate channel is negligible on that scale. -/
theorem h3TerminalBalanceCriticalEquipartitionAlong_of_shareCluster_eq_half
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a theta : ℝ}
    {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta)
    (hTheta : theta = (1 : ℝ) / 2) :
    H3TerminalBalanceCriticalEquipartitionAlong u τ := by
  let B : ℕ → ℝ :=
    fun n => h3TerminalBalanceAmplitudeAt u (τ n)
  let D : ℕ → ℝ :=
    fun n => velocityH3DissipationAt u (τ n)
  let I : ℕ → ℝ :=
    fun n => h3TerminalBalanceImbalanceAt u (τ n)
  let S : ℕ → ℝ :=
    fun n => h3TerminalBalanceSubordinateChannelAt u (τ n)

  have hBPos :
      ∀ᶠ n : ℕ in atTop, 0 < B n := by
    dsimp only [B]
    exact hCluster.1.2.1.eventually (eventually_gt_atTop (0 : ℝ))

  have hCriticalCascade :
      H3TerminalBalanceCriticalDissipationImbalanceClockCascadeAlong u T τ :=
    h3TerminalBalanceCriticalDissipationImbalanceClockCascadeAlong_of_shareCluster_eq_half
      hAt hCluster hTheta

  have hDPos :
      ∀ᶠ n : ℕ in atTop, 0 < D n := by
    dsimp only [D]
    exact hCriticalCascade.1.eventually (eventually_gt_atTop (0 : ℝ))

  have hTwoDPos :
      ∀ᶠ n : ℕ in atTop, 0 < 2 * D n := by
    filter_upwards [hDPos] with n hn
    linarith

  have hBOverB :
      Tendsto (fun n : ℕ => B n / B n) atTop (𝓝 (1 : ℝ)) := by
    have hEq :
        (fun _ : ℕ => (1 : ℝ)) =ᶠ[atTop]
          (fun n : ℕ => B n / B n) := by
      filter_upwards [hBPos] with n hn
      exact (div_self (ne_of_gt hn)).symm
    exact tendsto_const_nhds.congr' hEq

  have hDOverB :
      Tendsto (fun n : ℕ => D n / B n)
        atTop (𝓝 ((1 : ℝ) / 2)) := by
    dsimp only [D, B]
    exact
      h3TerminalBalanceDissipation_div_amplitude_tendsto_half_of_shareCluster_eq_half
        hCluster hTheta

  have hTwoDOverB :
      Tendsto (fun n : ℕ => (2 * D n) / B n)
        atTop (𝓝 (1 : ℝ)) := by
    have hTwice :
        Tendsto (fun n : ℕ => (2 : ℝ) * (D n / B n))
          atTop (𝓝 (2 * ((1 : ℝ) / 2))) :=
      tendsto_const_nhds.mul hDOverB
    have hFunction :
        (fun n : ℕ => (2 : ℝ) * (D n / B n)) =
          (fun n : ℕ => (2 * D n) / B n) := by
      funext n
      ring
    rw [hFunction] at hTwice
    norm_num at hTwice ⊢
    exact hTwice

  have hIOverB :
      Tendsto (fun n : ℕ => I n / B n)
        atTop (𝓝 (1 : ℝ)) := by
    dsimp only [I, B]
    exact
      h3TerminalBalanceImbalance_div_amplitude_tendsto_one_of_shareCluster_eq_half
        hCluster hTheta

  have hSOverB :
      Tendsto (fun n : ℕ => S n / B n)
        atTop (𝓝 (0 : ℝ)) := by
    dsimp only [S, B]
    exact
      h3TerminalBalanceSubordinateRatio_tendsto_zero_of_shareCluster_eq_half
        hH3 hClass hAt hCluster hTheta

  have hBOverTwoD :
      Tendsto (fun n : ℕ => B n / (2 * D n))
        atTop (𝓝 (1 : ℝ)) := by
    have h :=
      ratio_tendsto_of_common_positive_reference
        B
        (fun n : ℕ => 2 * D n)
        B
        (1 : ℝ)
        (1 : ℝ)
        hBPos
        hTwoDPos
        hBOverB
        hTwoDOverB
        (by norm_num)
    norm_num at h ⊢
    exact h

  have hIOverTwoD :
      Tendsto (fun n : ℕ => I n / (2 * D n))
        atTop (𝓝 (1 : ℝ)) := by
    have h :=
      ratio_tendsto_of_common_positive_reference
        I
        (fun n : ℕ => 2 * D n)
        B
        (1 : ℝ)
        (1 : ℝ)
        hBPos
        hTwoDPos
        hIOverB
        hTwoDOverB
        (by norm_num)
    norm_num at h ⊢
    exact h

  have hSOverTwoD :
      Tendsto (fun n : ℕ => S n / (2 * D n))
        atTop (𝓝 (0 : ℝ)) := by
    have h :=
      ratio_tendsto_of_common_positive_reference
        S
        (fun n : ℕ => 2 * D n)
        B
        (0 : ℝ)
        (1 : ℝ)
        hBPos
        hTwoDPos
        hSOverB
        hTwoDOverB
        (by norm_num)
    norm_num at h ⊢
    exact h

  dsimp only [B, D, I, S] at hBOverTwoD hIOverTwoD hSOverTwoD
  exact ⟨hBOverTwoD, hIOverTwoD, hSOverTwoD⟩

end

end Euclidean
end Bridge
end PrimeTensor
