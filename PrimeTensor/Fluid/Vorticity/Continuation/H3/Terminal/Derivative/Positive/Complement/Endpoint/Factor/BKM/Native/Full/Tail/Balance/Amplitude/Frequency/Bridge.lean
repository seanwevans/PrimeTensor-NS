import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Continuation
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Characteristic.Frequency.Rate

/-!
# Canonical balance amplitude and the intrinsic top-frequency scale

The canonical branch-free terminal balance amplitude is

`B(t) = max (-E'(t)) (-T_H3(t))`.

Exact balance gives `D(t) ≤ B(t)`, while the top-order dissipation satisfies
`D₃(t) ≤ D(t)`.  Hence, at every strict H³ energy-class time,

`Λ₃(t)^2 = D₃(t) / E₃(t) ≤ B(t) / E₃(t)`.

This identifies the canonical balance amplitude as a direct carrier of the
intrinsic top-frequency cascade, without introducing a kinetic-anchor
comparison between full and top-order energy.

Under hypothetical nonextension, the existing characteristic-frequency rate

`1 ≤ 3 K² (E₀(b)+1) (T-t)² Λ₃(t)^6`

therefore upgrades to the branch-free cubic rate

`1 ≤ 3 K² (E₀(b)+1) (T-t)² (B(t)/E₃(t))^3`

on a full terminal tail.  In particular `B/E₃ -> +∞` on the entire left
terminal neighborhood.

All statements remain necessary consequences conditional on hypothetical
nonextension.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The top-order H³ dissipation is bounded by the canonical branch-free
balance amplitude at every strict energy-class time. -/
theorem velocityH3Dissipation3At_le_h3TerminalBalanceAmplitudeAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    velocityH3Dissipation3At u t ≤
      h3TerminalBalanceAmplitudeAt u t := by
  exact
    le_trans
      (velocityH3Dissipation3At_le_dissipationAt u t)
      (velocityH3DissipationAt_le_h3TerminalBalanceAmplitudeAt
        hH3 hClass ht)

/-- The intrinsic squared top characteristic frequency is bounded pointwise by
canonical balance amplitude normalized by the top H³ energy block. -/
theorem h3TopCharacteristicFrequencyAt_sq_le_balanceAmplitude_div_energy3
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3TopCharacteristicFrequencyAt u t ^ 2 ≤
      h3TerminalBalanceAmplitudeAt u t /
        velocityH3Energy3At u t := by
  rw [h3TopCharacteristicFrequencyAt_sq]

  have hDom :
      velocityH3Dissipation3At u t ≤
        h3TerminalBalanceAmplitudeAt u t :=
    velocityH3Dissipation3At_le_h3TerminalBalanceAmplitudeAt
      hH3 hClass ht

  have hE3Nonneg :
      0 ≤ velocityH3Energy3At u t :=
    velocityH3Energy3At_nonneg u t

  exact
    div_le_div_of_nonneg_right
      hDom
      hE3Nonneg

/-- Under hypothetical nonextension, canonical balance amplitude normalized by
`E₃` diverges throughout the entire left terminal neighborhood. -/
theorem h3TerminalBalanceAmplitude_div_energy3_tendsto_atTop_nhdsLT_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    Tendsto
      (fun t : ℝ =>
        h3TerminalBalanceAmplitudeAt u t /
          velocityH3Energy3At u t)
      (𝓝[<] T)
      atTop := by
  have hTopRatio :=
    velocityH3Dissipation3At_div_energy3At_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass

  refine tendsto_atTop.2 ?_
  intro M

  have hEventually :
      ∀ᶠ t : ℝ in 𝓝[<] T,
        M ≤
          velocityH3Dissipation3At u t /
            velocityH3Energy3At u t :=
    hTopRatio.eventually
      (eventually_ge_atTop M)

  have hTail :
      Set.Ioo a T ∈ 𝓝[<] T :=
    Ioo_mem_nhdsLT hClass.terminal_start.2

  filter_upwards [hEventually, hTail] with t hM ht

  have hDom :
      velocityH3Dissipation3At u t ≤
        h3TerminalBalanceAmplitudeAt u t :=
    velocityH3Dissipation3At_le_h3TerminalBalanceAmplitudeAt
      hH3 hClass ht

  have hE3Nonneg :
      0 ≤ velocityH3Energy3At u t :=
    velocityH3Energy3At_nonneg u t

  have hRatioDom :
      velocityH3Dissipation3At u t /
          velocityH3Energy3At u t ≤
        h3TerminalBalanceAmplitudeAt u t /
          velocityH3Energy3At u t :=
    div_le_div_of_nonneg_right
      hDom
      hE3Nonneg

  exact le_trans hM hRatioDom

/-- On a sufficiently late terminal interval, hypothetical nonextension forces
an intrinsic cubic rate for canonical balance amplitude normalized by `E₃`:

`1 ≤ 3 K² (E₀(b)+1) (T-t)² (B(t)/E₃(t))^3`.
-/
theorem exists_terminalTail_balanceAmplitude_div_energy3_cubicRate_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    ∃ c : ℝ,
      c ∈ Set.Ioo b T
        ∧
      ∀ t : ℝ,
        t ∈ Set.Ioo c T →
        1 ≤
          3
            * h3PathSqrtEnergyRiccatiCoefficient ^ 2
            * (velocityH3Energy0At u b + 1)
            * (T - t) ^ 2
            *
              (h3TerminalBalanceAmplitudeAt u t /
                velocityH3Energy3At u t) ^ 3 := by
  obtain ⟨c, hc, hFrequencyRate⟩ :=
    exists_terminalTail_characteristicFrequency_pow_six_rate_of_noH3PathExtension
      hH3 hNoExtension hClass hb

  refine ⟨c, hc, ?_⟩
  intro t ht

  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 (lt_trans hc.1 ht.1), ht.2⟩

  have hBridge :
      h3TopCharacteristicFrequencyAt u t ^ 2 ≤
        h3TerminalBalanceAmplitudeAt u t /
          velocityH3Energy3At u t :=
    h3TopCharacteristicFrequencyAt_sq_le_balanceAmplitude_div_energy3
      hH3 hClass htClass

  have hFrequencySqNonneg :
      0 ≤ h3TopCharacteristicFrequencyAt u t ^ 2 :=
    sq_nonneg _

  have hCube :
      (h3TopCharacteristicFrequencyAt u t ^ 2) ^ 3 ≤
        (h3TerminalBalanceAmplitudeAt u t /
          velocityH3Energy3At u t) ^ 3 :=
    pow_le_pow_left₀
      hFrequencySqNonneg
      hBridge
      3

  have hPrefactorNonneg :
      0 ≤
        3
          * h3PathSqrtEnergyRiccatiCoefficient ^ 2
          * (velocityH3Energy0At u b + 1)
          * (T - t) ^ 2 := by
    have hE0 : 0 ≤ velocityH3Energy0At u b :=
      velocityH3Energy0At_nonneg u b
    positivity

  have hScaled :
      3
          * h3PathSqrtEnergyRiccatiCoefficient ^ 2
          * (velocityH3Energy0At u b + 1)
          * (T - t) ^ 2
          * (h3TopCharacteristicFrequencyAt u t ^ 2) ^ 3
        ≤
      3
          * h3PathSqrtEnergyRiccatiCoefficient ^ 2
          * (velocityH3Energy0At u b + 1)
          * (T - t) ^ 2
          *
            (h3TerminalBalanceAmplitudeAt u t /
              velocityH3Energy3At u t) ^ 3 :=
    mul_le_mul_of_nonneg_left
      hCube
      hPrefactorNonneg

  calc
    1 ≤
        3
          * h3PathSqrtEnergyRiccatiCoefficient ^ 2
          * (velocityH3Energy0At u b + 1)
          * (T - t) ^ 2
          * h3TopCharacteristicFrequencyAt u t ^ 6 :=
      hFrequencyRate t ht
    _ =
        3
          * h3PathSqrtEnergyRiccatiCoefficient ^ 2
          * (velocityH3Energy0At u b + 1)
          * (T - t) ^ 2
          * (h3TopCharacteristicFrequencyAt u t ^ 2) ^ 3 := by
      ring
    _ ≤
        3
          * h3PathSqrtEnergyRiccatiCoefficient ^ 2
          * (velocityH3Energy0At u b + 1)
          * (T - t) ^ 2
          *
            (h3TerminalBalanceAmplitudeAt u t /
              velocityH3Energy3At u t) ^ 3 :=
      hScaled

/-- Canonical midpoint specialization of the intrinsic cubic balance-amplitude
rate. -/
theorem exists_terminalTail_balanceAmplitude_div_energy3_cubicRate_midpoint_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∃ c : ℝ,
      c ∈ Set.Ioo (h3BKMKineticTailMidpoint a T) T
        ∧
      ∀ t : ℝ,
        t ∈ Set.Ioo c T →
        1 ≤
          3
            * h3PathSqrtEnergyRiccatiCoefficient ^ 2
            *
              (velocityH3Energy0At
                  u
                  (h3BKMKineticTailMidpoint a T)
                + 1)
            * (T - t) ^ 2
            *
              (h3TerminalBalanceAmplitudeAt u t /
                velocityH3Energy3At u t) ^ 3 := by
  exact
    exists_terminalTail_balanceAmplitude_div_energy3_cubicRate_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      (h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2)

end

end Euclidean
end Bridge
end PrimeTensor
