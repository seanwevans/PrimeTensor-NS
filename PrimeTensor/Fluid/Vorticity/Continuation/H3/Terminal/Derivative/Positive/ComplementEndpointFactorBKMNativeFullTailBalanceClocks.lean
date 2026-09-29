import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailPhysicalClocks
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.NormalizedBalanceGap

/-!
# Full-tail H³ balance-channel clocks

The full-tail physical-clock theorem proves, under hypothetical nonextension,

`(T - t) * D(t) -> +∞`.

The full-energy normalized cascade also gives

`D(t) / E(t) -> +∞`.

Exact H³ balance is

`E'(t) + 2 D(t) = -T_H3(t)`.

Hence at every strict energy-class time the larger of the two balance channels

* `-E'(t)` (rapid energy decay),
* `-T_H3(t)` (adverse transport)

dominates one full copy of `D(t)`.  No branch needs to be selected: the maximum
itself is canonical.  Consequently hypothetical nonextension forces both

`max ((T-t)(-E')) ((T-t)(-T_H3)) -> +∞`

and

`max ((-E')/E) ((-T_H3)/E) -> +∞`

throughout the entire left terminal neighborhood.

This is neutral about which channel is larger at any individual time and allows
arbitrary switching between the two mechanisms.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Exact balance forces the larger raw balance channel to dominate the full
H³ dissipation at every strict energy-class time. -/
theorem velocityH3DissipationAt_le_max_negativeEnergyDerivative_negativeTransport
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    velocityH3DissipationAt u t ≤
      max
        (- deriv (velocityH3EnergyAt u) t)
        (- velocityH3TransportDerivativeAt u t) := by
  have hBalance :=
    deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3 hClass ht

  have hLeft :
      - deriv (velocityH3EnergyAt u) t ≤
        max
          (- deriv (velocityH3EnergyAt u) t)
          (- velocityH3TransportDerivativeAt u t) :=
    le_max_left _ _

  have hRight :
      - velocityH3TransportDerivativeAt u t ≤
        max
          (- deriv (velocityH3EnergyAt u) t)
          (- velocityH3TransportDerivativeAt u t) :=
    le_max_right _ _

  linarith

/-- Under hypothetical nonextension, the maximum of the two physical exact-
balance clocks diverges on the entire left terminal neighborhood. -/
theorem max_h3PhysicalBalanceClock_tendsto_atTop_nhdsLT_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    Tendsto
      (fun t : ℝ =>
        max
          ((T - t) * (- deriv (velocityH3EnergyAt u) t))
          ((T - t) * (- velocityH3TransportDerivativeAt u t)))
      (𝓝[<] T)
      atTop := by
  have hDClock :=
    velocityH3DissipationPhysicalClock_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass

  refine tendsto_atTop.2 ?_
  intro M

  have hEventually :
      ∀ᶠ t : ℝ in 𝓝[<] T,
        M ≤ (T - t) * velocityH3DissipationAt u t :=
    hDClock.eventually
      (eventually_ge_atTop M)

  have hTail :
      Set.Ioo a T ∈ 𝓝[<] T :=
    Ioo_mem_nhdsLT hClass.terminal_start.2

  filter_upwards [hEventually, hTail] with t hM ht

  have hBalance :=
    deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3 hClass ht

  let x : ℝ :=
    (T - t) * (- deriv (velocityH3EnergyAt u) t)

  let y : ℝ :=
    (T - t) * (- velocityH3TransportDerivativeAt u t)

  let d : ℝ :=
    (T - t) * velocityH3DissipationAt u t

  have hSum : x + y = 2 * d := by
    dsimp only [x, y, d]
    rw [← hBalance]
    ring

  have hLeft : x ≤ max x y :=
    le_max_left _ _

  have hRight : y ≤ max x y :=
    le_max_right _ _

  have hDLeMax : d ≤ max x y := by
    linarith

  exact
    le_trans
      hM
      (by simpa only [x, y, d] using hDLeMax)

/-- Under hypothetical nonextension, the maximum of the two exact-balance
channels normalized by full H³ energy diverges on the entire left terminal
neighborhood. -/
theorem max_h3NormalizedBalanceRate_tendsto_atTop_nhdsLT_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    Tendsto
      (fun t : ℝ =>
        max
          ((- deriv (velocityH3EnergyAt u) t) /
            velocityH3EnergyAt u t)
          ((- velocityH3TransportDerivativeAt u t) /
            velocityH3EnergyAt u t))
      (𝓝[<] T)
      atTop := by
  have hRatio :=
    velocityH3DissipationAt_div_energyAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass

  refine tendsto_atTop.2 ?_
  intro M

  have hEventually :
      ∀ᶠ t : ℝ in 𝓝[<] T,
        M ≤
          velocityH3DissipationAt u t /
            velocityH3EnergyAt u t :=
    hRatio.eventually
      (eventually_ge_atTop M)

  have hTail :
      Set.Ioo a T ∈ 𝓝[<] T :=
    Ioo_mem_nhdsLT hClass.terminal_start.2

  filter_upwards [hEventually, hTail] with t hM ht

  have hNormalizedBalance :=
    normalized_negativeTransport_sub_deriv_eq_two_mul_dissipation_div_energy
      hH3 hClass ht

  let x : ℝ :=
    (- deriv (velocityH3EnergyAt u) t) /
      velocityH3EnergyAt u t

  let y : ℝ :=
    (- velocityH3TransportDerivativeAt u t) /
      velocityH3EnergyAt u t

  let d : ℝ :=
    velocityH3DissipationAt u t /
      velocityH3EnergyAt u t

  have hSum : x + y = 2 * d := by
    dsimp only [x, y, d]
    calc
      (- deriv (velocityH3EnergyAt u) t) /
            velocityH3EnergyAt u t
          +
        (- velocityH3TransportDerivativeAt u t) /
            velocityH3EnergyAt u t
          =
        ((- velocityH3TransportDerivativeAt u t) -
            deriv (velocityH3EnergyAt u) t) /
          velocityH3EnergyAt u t := by
            ring
      _ =
        2 *
          (velocityH3DissipationAt u t /
            velocityH3EnergyAt u t) :=
        hNormalizedBalance

  have hLeft : x ≤ max x y :=
    le_max_left _ _

  have hRight : y ≤ max x y :=
    le_max_right _ _

  have hDLeMax : d ≤ max x y := by
    linarith

  exact
    le_trans
      hM
      (by simpa only [x, y, d] using hDLeMax)

/-- Neutral full-tail package: either smooth continuation exists, or the
physical and normalized maxima of the two exact-balance channels both diverge
throughout the entire left terminal neighborhood. -/
theorem smoothContinuationExtension_or_fullTailBalanceChannelMaxima
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
    )
      ∨
    (
      Tendsto
        (fun t : ℝ =>
          max
            ((T - t) * (- deriv (velocityH3EnergyAt u) t))
            ((T - t) * (- velocityH3TransportDerivativeAt u t)))
        (𝓝[<] T)
        atTop
      ∧
      Tendsto
        (fun t : ℝ =>
          max
            ((- deriv (velocityH3EnergyAt u) t) /
              velocityH3EnergyAt u t)
            ((- velocityH3TransportDerivativeAt u t) /
              velocityH3EnergyAt u t))
        (𝓝[<] T)
        atTop
    ) := by
  classical

  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact Or.inl hExtension

  · exact
      Or.inr
        ⟨
          max_h3PhysicalBalanceClock_tendsto_atTop_nhdsLT_of_noH3PathExtension
            hH3 hExtension hClass,
          max_h3NormalizedBalanceRate_tendsto_atTop_nhdsLT_of_noH3PathExtension
            hH3 hExtension hClass
        ⟩

end

end Euclidean
end Bridge
end PrimeTensor
