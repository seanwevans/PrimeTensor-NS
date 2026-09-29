import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeEnergyClockFullDissipationClock
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Third.Rate.Dissipation.TransportDichotomy

/-!
# Physical-clock balance-channel dichotomy on the synchronized H³ witness

The synchronized physical-energy witness already carries

* `(T - σ n) * D₃(σ n) -> +∞`, and
* `(T - σ n) * D(σ n) -> +∞`.

Exact H³ balance gives the pointwise neutral alternative

`E'(t) ≤ -D₃(t)`  or  `D₃(t) ≤ -T_H3(t)`.

Multiplying by the positive terminal distance preserves the alternative.  Thus,
for every threshold `M`, all sufficiently late members of the same physical-
clock sequence satisfy

`M ≤ (T - σ n) * (-E'(σ n))`

or

`M ≤ (T - σ n) * (-T_H3(σ n))`.

No branch is selected here.  This records the exact balance obstruction without
assuming that the energy derivative has either sign.  It remains a necessary
consequence conditional on hypothetical nonextension.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- On the same divergent physical-energy-clock sequence, every sufficiently
large physical top-dissipation threshold is paid either by negative H³ energy
derivative or by adverse H³ transport. -/
theorem exists_h3EnergyPhysicalClock_with_balanceChannelPhysicalClockDichotomySequence_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∃ σ : ℕ → ℝ, ∃ C : ℝ,
      0 ≤ C ∧
      (∀ n : ℕ,
        σ n ∈ Set.Ioo a T ∧
        σ n ∈ Set.Ioo
          (T - (1 : ℝ) / ((n : ℝ) + 1)) T ∧
        (n : ℝ) <
          (T - σ n) * velocityH3EnergyAt u (σ n) ∧
        (n : ℝ) * ((n : ℝ) + 1) <
          velocityH3EnergyAt u (σ n)) ∧
      Tendsto σ atTop (𝓝 T) ∧
      Tendsto
        (fun n : ℕ =>
          (T - σ n) * velocityH3Energy3At u (σ n))
        atTop atTop ∧
      Tendsto
        (fun n : ℕ =>
          (T - σ n) * velocityH3Dissipation3At u (σ n))
        atTop atTop ∧
      Tendsto
        (fun n : ℕ =>
          (T - σ n) * velocityH3DissipationAt u (σ n))
        atTop atTop ∧
      (∀ M : ℝ,
        ∀ᶠ n : ℕ in atTop,
          M ≤
              (T - σ n) *
                (- deriv (velocityH3EnergyAt u) (σ n))
            ∨
          M ≤
              (T - σ n) *
                (- velocityH3TransportDerivativeAt u (σ n))) := by
  obtain
    ⟨
      σ,
      C,
      hCNonneg,
      hσ,
      hSigmaTendsto,
      _hIndexedE3,
      _hPhysicalE3Rate,
      hPhysicalE3Top,
      _hD3RatioTop,
      hPhysicalD3Top,
      _hFullRatioTop,
      hPhysicalDTop
    ⟩ :=
    exists_h3EnergyPhysicalClock_with_fullDissipationClockSequence_of_noH3PathExtension
      hH3 hNoExtension hClass

  have hBalanceClock :
      ∀ M : ℝ,
        ∀ᶠ n : ℕ in atTop,
          M ≤
              (T - σ n) *
                (- deriv (velocityH3EnergyAt u) (σ n))
            ∨
          M ≤
              (T - σ n) *
                (- velocityH3TransportDerivativeAt u (σ n)) := by
    intro M

    have hD3ClockEventually :
        ∀ᶠ n : ℕ in atTop,
          M ≤
            (T - σ n) * velocityH3Dissipation3At u (σ n) :=
      hPhysicalD3Top.eventually
        (eventually_ge_atTop M)

    filter_upwards [hD3ClockEventually] with n hn

    have hClassN : σ n ∈ Set.Ioo a T :=
      (hσ n).1

    have hGapNonneg : 0 ≤ T - σ n := by
      linarith [hClassN.2]

    rcases
      deriv_energy_le_neg_dissipation3_or_dissipation3_le_neg_transport
        hH3
        hClass
        hClassN
      with hDecay | hTransport

    · left

      have hDom :
          velocityH3Dissipation3At u (σ n) ≤
            - deriv (velocityH3EnergyAt u) (σ n) := by
        linarith

      have hScaled :
          (T - σ n) * velocityH3Dissipation3At u (σ n) ≤
            (T - σ n) *
              (- deriv (velocityH3EnergyAt u) (σ n)) :=
        mul_le_mul_of_nonneg_left
          hDom
          hGapNonneg

      exact le_trans hn hScaled

    · right

      have hScaled :
          (T - σ n) * velocityH3Dissipation3At u (σ n) ≤
            (T - σ n) *
              (- velocityH3TransportDerivativeAt u (σ n)) :=
        mul_le_mul_of_nonneg_left
          hTransport
          hGapNonneg

      exact le_trans hn hScaled

  exact
    ⟨
      σ,
      C,
      hCNonneg,
      hσ,
      hSigmaTendsto,
      hPhysicalE3Top,
      hPhysicalD3Top,
      hPhysicalDTop,
      hBalanceClock
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
