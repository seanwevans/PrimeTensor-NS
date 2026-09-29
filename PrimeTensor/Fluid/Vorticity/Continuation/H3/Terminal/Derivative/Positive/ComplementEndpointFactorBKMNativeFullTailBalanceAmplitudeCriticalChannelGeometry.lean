import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeCriticalEquipartition

/-!
# Critical half-share channel geometry relative to dissipation

The critical equipartition theorem is branch-free:

* `B / (2 D) -> 1`,
* `I / (2 D) -> 1`, and
* `S / (2 D) -> 0`.

After the critical dominant orientation is frozen, `B` is exactly one of the
two signed H³ balance channels and `S` is exactly the other.  Hence the critical
boundary has one of two asymptotic channel geometries:

* decay-dominant: `(-E') / (2D) -> 1` and `(-T_H3) / (2D) -> 0`;
* transport-dominant: `(-E') / (2D) -> 0` and `(-T_H3) / (2D) -> 1`.

In either orientation the absolute channel imbalance still satisfies
`I / (2D) -> 1`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Critical decay-dominant channel geometry relative to twice full H³
+dissipation. -/
def H3TerminalBalanceCriticalDecayDissipationGeometryAlong
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (τ : ℕ → ℝ) : Prop :=
  Tendsto
      (fun n : ℕ =>
        (- deriv (velocityH3EnergyAt u) (τ n)) /
          (2 * velocityH3DissipationAt u (τ n)))
      atTop (𝓝 (1 : ℝ))
    ∧
  Tendsto
      (fun n : ℕ =>
        (- velocityH3TransportDerivativeAt u (τ n)) /
          (2 * velocityH3DissipationAt u (τ n)))
      atTop (𝓝 (0 : ℝ))
    ∧
  Tendsto
      (fun n : ℕ =>
        h3TerminalBalanceImbalanceAt u (τ n) /
          (2 * velocityH3DissipationAt u (τ n)))
      atTop (𝓝 (1 : ℝ))

/-- Critical transport-dominant channel geometry relative to twice full H³
+dissipation. -/
def H3TerminalBalanceCriticalTransportDissipationGeometryAlong
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (τ : ℕ → ℝ) : Prop :=
  Tendsto
      (fun n : ℕ =>
        (- deriv (velocityH3EnergyAt u) (τ n)) /
          (2 * velocityH3DissipationAt u (τ n)))
      atTop (𝓝 (0 : ℝ))
    ∧
  Tendsto
      (fun n : ℕ =>
        (- velocityH3TransportDerivativeAt u (τ n)) /
          (2 * velocityH3DissipationAt u (τ n)))
      atTop (𝓝 (1 : ℝ))
    ∧
  Tendsto
      (fun n : ℕ =>
        h3TerminalBalanceImbalanceAt u (τ n) /
          (2 * velocityH3DissipationAt u (τ n)))
      atTop (𝓝 (1 : ℝ))

/-- A resolved critical decay-dominant witness has normalized signed-channel
+geometry `((-E')/(2D), (-T_H3)/(2D), I/(2D)) -> (1,0,1)`. -/
theorem h3TerminalBalanceCriticalDecayDissipationGeometryAlong_of_resolved
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a theta : ℝ}
    {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta)
    (hTheta : theta = (1 : ℝ) / 2)
    (hResolved :
      H3TerminalBalanceCriticalDecayDominantClockCascadeAlong u T τ) :
    H3TerminalBalanceCriticalDecayDissipationGeometryAlong u τ := by
  rcases hResolved with
    ⟨hIdentities, _hRaw, _hClock, _hNormalized, _hSubordinateZero⟩

  have hEquip : H3TerminalBalanceCriticalEquipartitionAlong u τ :=
    h3TerminalBalanceCriticalEquipartitionAlong_of_shareCluster_eq_half
      hH3 hClass hAt hCluster hTheta

  have hDominant := hEquip.1
  have hImbalance := hEquip.2.1
  have hSubordinate := hEquip.2.2

  have hDominantEq :
      (fun n : ℕ =>
        h3TerminalBalanceAmplitudeAt u (τ n) /
          (2 * velocityH3DissipationAt u (τ n)))
        =
      (fun n : ℕ =>
        (- deriv (velocityH3EnergyAt u) (τ n)) /
          (2 * velocityH3DissipationAt u (τ n))) := by
    funext n
    rw [(hIdentities n).1]

  have hSubordinateEq :
      (fun n : ℕ =>
        h3TerminalBalanceSubordinateChannelAt u (τ n) /
          (2 * velocityH3DissipationAt u (τ n)))
        =
      (fun n : ℕ =>
        (- velocityH3TransportDerivativeAt u (τ n)) /
          (2 * velocityH3DissipationAt u (τ n))) := by
    funext n
    rw [(hIdentities n).2]

  rw [hDominantEq] at hDominant
  rw [hSubordinateEq] at hSubordinate

  exact ⟨hDominant, hSubordinate, hImbalance⟩

/-- A resolved critical transport-dominant witness has normalized signed-channel
+geometry `((-E')/(2D), (-T_H3)/(2D), I/(2D)) -> (0,1,1)`. -/
theorem h3TerminalBalanceCriticalTransportDissipationGeometryAlong_of_resolved
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a theta : ℝ}
    {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta)
    (hTheta : theta = (1 : ℝ) / 2)
    (hResolved :
      H3TerminalBalanceCriticalTransportDominantClockCascadeAlong u T τ) :
    H3TerminalBalanceCriticalTransportDissipationGeometryAlong u τ := by
  rcases hResolved with
    ⟨hIdentities, _hRaw, _hClock, _hNormalized, _hSubordinateZero⟩

  have hEquip : H3TerminalBalanceCriticalEquipartitionAlong u τ :=
    h3TerminalBalanceCriticalEquipartitionAlong_of_shareCluster_eq_half
      hH3 hClass hAt hCluster hTheta

  have hDominant := hEquip.1
  have hImbalance := hEquip.2.1
  have hSubordinate := hEquip.2.2

  have hDominantEq :
      (fun n : ℕ =>
        h3TerminalBalanceAmplitudeAt u (τ n) /
          (2 * velocityH3DissipationAt u (τ n)))
        =
      (fun n : ℕ =>
        (- velocityH3TransportDerivativeAt u (τ n)) /
          (2 * velocityH3DissipationAt u (τ n))) := by
    funext n
    rw [(hIdentities n).1]

  have hSubordinateEq :
      (fun n : ℕ =>
        h3TerminalBalanceSubordinateChannelAt u (τ n) /
          (2 * velocityH3DissipationAt u (τ n)))
        =
      (fun n : ℕ =>
        (- deriv (velocityH3EnergyAt u) (τ n)) /
          (2 * velocityH3DissipationAt u (τ n))) := by
    funext n
    rw [(hIdentities n).2]

  rw [hDominantEq] at hDominant
  rw [hSubordinateEq] at hSubordinate

  exact ⟨hSubordinate, hDominant, hImbalance⟩

/-- Every fully resolved critical half-share witness has one of the two exact
+signed-channel geometries relative to twice full dissipation. -/
theorem h3TerminalBalanceCriticalResolved_dissipationGeometry
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a theta : ℝ}
    {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta)
    (hTheta : theta = (1 : ℝ) / 2)
    (hResolved : H3TerminalBalanceCriticalResolvedClockCascadeAlong u T τ) :
    H3TerminalBalanceCriticalDecayDissipationGeometryAlong u τ
      ∨
    H3TerminalBalanceCriticalTransportDissipationGeometryAlong u τ := by
  rcases hResolved with hDecay | hTransport
  · exact
      Or.inl
        (h3TerminalBalanceCriticalDecayDissipationGeometryAlong_of_resolved
          hH3 hClass hAt hCluster hTheta hDecay)
  · exact
      Or.inr
        (h3TerminalBalanceCriticalTransportDissipationGeometryAlong_of_resolved
          hH3 hClass hAt hCluster hTheta hTransport)

end

end Euclidean
end Bridge
end PrimeTensor
