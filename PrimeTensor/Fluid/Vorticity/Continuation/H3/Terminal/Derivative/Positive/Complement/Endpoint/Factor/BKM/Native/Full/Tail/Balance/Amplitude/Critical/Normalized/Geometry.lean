import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Critical.Obstruction

/-!
# Normalized geometry of the critical half-share balance regime

At the critical dissipation share `theta = 1/2`, the exact balance simplex has a
particularly rigid normalized shape.  Along the share-cluster sequence,

* full dissipation occupies one half of the canonical amplitude,
* absolute imbalance occupies asymptotically one full amplitude, and
* after a dominant channel is frozen, the subordinate signed channel is little-o
  of that dominant channel.

Thus the two critical orientations have normalized ordered geometry

`(dominant, subordinate, dissipation, imbalance) / dominant -> (1, 0, 1/2, 1)`.

This is purely a repackaging of the exact balance identities and the already
proved critical share limit; no new PDE estimate is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- At critical half-share, full H³ dissipation is asymptotically one half of
canonical balance amplitude. -/
theorem h3TerminalBalanceDissipation_div_amplitude_tendsto_half_of_shareCluster_eq_half
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T theta : ℝ}
    {τ : ℕ → ℝ}
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta)
    (hTheta : theta = (1 : ℝ) / 2) :
    Tendsto
      (fun n : ℕ =>
        velocityH3DissipationAt u (τ n) /
          h3TerminalBalanceAmplitudeAt u (τ n))
      atTop
      (𝓝 ((1 : ℝ) / 2)) := by
  simpa [h3TerminalBalanceDissipationShareAt, hTheta] using hCluster.2.1

/-- At critical half-share, the absolute channel imbalance is asymptotically one
full canonical balance amplitude. -/
theorem h3TerminalBalanceImbalance_div_amplitude_tendsto_one_of_shareCluster_eq_half
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T theta : ℝ}
    {τ : ℕ → ℝ}
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta)
    (hTheta : theta = (1 : ℝ) / 2) :
    Tendsto
      (fun n : ℕ =>
        h3TerminalBalanceImbalanceAt u (τ n) /
          h3TerminalBalanceAmplitudeAt u (τ n))
      atTop
      (𝓝 (1 : ℝ)) := by
  have hTwice :
      Tendsto
        (fun n : ℕ =>
          (2 : ℝ) * h3TerminalBalanceImbalanceHalfShareAt u (τ n))
        atTop
        (𝓝 (2 * (1 - theta))) :=
    tendsto_const_nhds.mul hCluster.2.2

  have hBPos :
      ∀ᶠ n : ℕ in atTop,
        0 < h3TerminalBalanceAmplitudeAt u (τ n) :=
    hCluster.1.2.1.eventually
      (eventually_gt_atTop (0 : ℝ))

  have hEq :
      ∀ᶠ n : ℕ in atTop,
        (2 : ℝ) * h3TerminalBalanceImbalanceHalfShareAt u (τ n)
          =
        h3TerminalBalanceImbalanceAt u (τ n) /
          h3TerminalBalanceAmplitudeAt u (τ n) := by
    filter_upwards [hBPos] with n hn
    have hBNe : h3TerminalBalanceAmplitudeAt u (τ n) ≠ 0 :=
      ne_of_gt hn
    unfold h3TerminalBalanceImbalanceHalfShareAt
    field_simp [hBNe]

  have hRatio := hTwice.congr' hEq
  have hLimitValue : (2 : ℝ) * (1 - theta) = 1 := by
    rw [hTheta]
    norm_num
  simpa only [hLimitValue] using hRatio

/-- Critical decay-dominant normalized geometry: transport is subordinate to
energy decay, while dissipation and imbalance occupy the fixed half/full shares. -/
def H3TerminalBalanceCriticalDecayDominantNormalizedGeometryAlong
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (τ : ℕ → ℝ) : Prop :=
  Tendsto
      (fun n : ℕ =>
        (- velocityH3TransportDerivativeAt u (τ n)) /
          (- deriv (velocityH3EnergyAt u) (τ n)))
      atTop (𝓝 (0 : ℝ))
    ∧
  Tendsto
      (fun n : ℕ =>
        velocityH3DissipationAt u (τ n) /
          (- deriv (velocityH3EnergyAt u) (τ n)))
      atTop (𝓝 ((1 : ℝ) / 2))
    ∧
  Tendsto
      (fun n : ℕ =>
        h3TerminalBalanceImbalanceAt u (τ n) /
          (- deriv (velocityH3EnergyAt u) (τ n)))
      atTop (𝓝 (1 : ℝ))

/-- Critical transport-dominant normalized geometry: energy decay is subordinate
to adverse transport, while dissipation and imbalance occupy the fixed half/full
shares. -/
def H3TerminalBalanceCriticalTransportDominantNormalizedGeometryAlong
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (τ : ℕ → ℝ) : Prop :=
  Tendsto
      (fun n : ℕ =>
        (- deriv (velocityH3EnergyAt u) (τ n)) /
          (- velocityH3TransportDerivativeAt u (τ n)))
      atTop (𝓝 (0 : ℝ))
    ∧
  Tendsto
      (fun n : ℕ =>
        velocityH3DissipationAt u (τ n) /
          (- velocityH3TransportDerivativeAt u (τ n)))
      atTop (𝓝 ((1 : ℝ) / 2))
    ∧
  Tendsto
      (fun n : ℕ =>
        h3TerminalBalanceImbalanceAt u (τ n) /
          (- velocityH3TransportDerivativeAt u (τ n)))
      atTop (𝓝 (1 : ℝ))

/-- A resolved critical decay-dominant cascade has the exact normalized critical
geometry `(subordinate, dissipation, imbalance) -> (0, 1/2, 1)` relative to its
dominant channel. -/
theorem h3TerminalBalanceCriticalDecayDominantNormalizedGeometryAlong_of_resolved
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T theta : ℝ}
    {τ : ℕ → ℝ}
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta)
    (hTheta : theta = (1 : ℝ) / 2)
    (hResolved :
      H3TerminalBalanceCriticalDecayDominantClockCascadeAlong u T τ) :
    H3TerminalBalanceCriticalDecayDominantNormalizedGeometryAlong u τ := by
  rcases hResolved with
    ⟨hIdentities, _hRaw, _hClock, _hNormalized, hSubordinateZero⟩

  have hDissipation :=
    h3TerminalBalanceDissipation_div_amplitude_tendsto_half_of_shareCluster_eq_half
      hCluster hTheta

  have hImbalance :=
    h3TerminalBalanceImbalance_div_amplitude_tendsto_one_of_shareCluster_eq_half
      hCluster hTheta

  have hSubordinate :
      Tendsto
        (fun n : ℕ =>
          (- velocityH3TransportDerivativeAt u (τ n)) /
            (- deriv (velocityH3EnergyAt u) (τ n)))
        atTop (𝓝 (0 : ℝ)) := by
    have hEq :
        (fun n : ℕ =>
          h3TerminalBalanceSubordinateChannelAt u (τ n) /
            h3TerminalBalanceAmplitudeAt u (τ n))
          =
        (fun n : ℕ =>
          (- velocityH3TransportDerivativeAt u (τ n)) /
            (- deriv (velocityH3EnergyAt u) (τ n))) := by
      funext n
      rw [(hIdentities n).2, (hIdentities n).1]
    rw [hEq] at hSubordinateZero
    exact hSubordinateZero

  have hDissipation' :
      Tendsto
        (fun n : ℕ =>
          velocityH3DissipationAt u (τ n) /
            (- deriv (velocityH3EnergyAt u) (τ n)))
        atTop (𝓝 ((1 : ℝ) / 2)) := by
    have hEq :
        (fun n : ℕ =>
          velocityH3DissipationAt u (τ n) /
            h3TerminalBalanceAmplitudeAt u (τ n))
          =
        (fun n : ℕ =>
          velocityH3DissipationAt u (τ n) /
            (- deriv (velocityH3EnergyAt u) (τ n))) := by
      funext n
      rw [(hIdentities n).1]
    rw [hEq] at hDissipation
    exact hDissipation

  have hImbalance' :
      Tendsto
        (fun n : ℕ =>
          h3TerminalBalanceImbalanceAt u (τ n) /
            (- deriv (velocityH3EnergyAt u) (τ n)))
        atTop (𝓝 (1 : ℝ)) := by
    have hEq :
        (fun n : ℕ =>
          h3TerminalBalanceImbalanceAt u (τ n) /
            h3TerminalBalanceAmplitudeAt u (τ n))
          =
        (fun n : ℕ =>
          h3TerminalBalanceImbalanceAt u (τ n) /
            (- deriv (velocityH3EnergyAt u) (τ n))) := by
      funext n
      rw [(hIdentities n).1]
    rw [hEq] at hImbalance
    exact hImbalance

  exact ⟨hSubordinate, hDissipation', hImbalance'⟩

/-- A resolved critical transport-dominant cascade has the exact normalized
critical geometry `(subordinate, dissipation, imbalance) -> (0, 1/2, 1)` relative
to its dominant channel. -/
theorem h3TerminalBalanceCriticalTransportDominantNormalizedGeometryAlong_of_resolved
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T theta : ℝ}
    {τ : ℕ → ℝ}
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta)
    (hTheta : theta = (1 : ℝ) / 2)
    (hResolved :
      H3TerminalBalanceCriticalTransportDominantClockCascadeAlong u T τ) :
    H3TerminalBalanceCriticalTransportDominantNormalizedGeometryAlong u τ := by
  rcases hResolved with
    ⟨hIdentities, _hRaw, _hClock, _hNormalized, hSubordinateZero⟩

  have hDissipation :=
    h3TerminalBalanceDissipation_div_amplitude_tendsto_half_of_shareCluster_eq_half
      hCluster hTheta

  have hImbalance :=
    h3TerminalBalanceImbalance_div_amplitude_tendsto_one_of_shareCluster_eq_half
      hCluster hTheta

  have hSubordinate :
      Tendsto
        (fun n : ℕ =>
          (- deriv (velocityH3EnergyAt u) (τ n)) /
            (- velocityH3TransportDerivativeAt u (τ n)))
        atTop (𝓝 (0 : ℝ)) := by
    have hEq :
        (fun n : ℕ =>
          h3TerminalBalanceSubordinateChannelAt u (τ n) /
            h3TerminalBalanceAmplitudeAt u (τ n))
          =
        (fun n : ℕ =>
          (- deriv (velocityH3EnergyAt u) (τ n)) /
            (- velocityH3TransportDerivativeAt u (τ n))) := by
      funext n
      rw [(hIdentities n).2, (hIdentities n).1]
    rw [hEq] at hSubordinateZero
    exact hSubordinateZero

  have hDissipation' :
      Tendsto
        (fun n : ℕ =>
          velocityH3DissipationAt u (τ n) /
            (- velocityH3TransportDerivativeAt u (τ n)))
        atTop (𝓝 ((1 : ℝ) / 2)) := by
    have hEq :
        (fun n : ℕ =>
          velocityH3DissipationAt u (τ n) /
            h3TerminalBalanceAmplitudeAt u (τ n))
          =
        (fun n : ℕ =>
          velocityH3DissipationAt u (τ n) /
            (- velocityH3TransportDerivativeAt u (τ n))) := by
      funext n
      rw [(hIdentities n).1]
    rw [hEq] at hDissipation
    exact hDissipation

  have hImbalance' :
      Tendsto
        (fun n : ℕ =>
          h3TerminalBalanceImbalanceAt u (τ n) /
            (- velocityH3TransportDerivativeAt u (τ n)))
        atTop (𝓝 (1 : ℝ)) := by
    have hEq :
        (fun n : ℕ =>
          h3TerminalBalanceImbalanceAt u (τ n) /
            h3TerminalBalanceAmplitudeAt u (τ n))
          =
        (fun n : ℕ =>
          h3TerminalBalanceImbalanceAt u (τ n) /
            (- velocityH3TransportDerivativeAt u (τ n))) := by
      funext n
      rw [(hIdentities n).1]
    rw [hEq] at hImbalance
    exact hImbalance

  exact ⟨hSubordinate, hDissipation', hImbalance'⟩

/-- Every fully resolved critical half-share witness has one of the two exact
normalized one-channel geometries. -/
theorem h3TerminalBalanceCriticalResolved_normalizedGeometry
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T theta : ℝ}
    {τ : ℕ → ℝ}
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta)
    (hTheta : theta = (1 : ℝ) / 2)
    (hResolved : H3TerminalBalanceCriticalResolvedClockCascadeAlong u T τ) :
    H3TerminalBalanceCriticalDecayDominantNormalizedGeometryAlong u τ
      ∨
    H3TerminalBalanceCriticalTransportDominantNormalizedGeometryAlong u τ := by
  rcases hResolved with hDecay | hTransport
  · exact
      Or.inl
        (h3TerminalBalanceCriticalDecayDominantNormalizedGeometryAlong_of_resolved
          hCluster hTheta hDecay)
  · exact
      Or.inr
        (h3TerminalBalanceCriticalTransportDominantNormalizedGeometryAlong_of_resolved
          hCluster hTheta hTransport)

end

end Euclidean
end Bridge
end PrimeTensor
