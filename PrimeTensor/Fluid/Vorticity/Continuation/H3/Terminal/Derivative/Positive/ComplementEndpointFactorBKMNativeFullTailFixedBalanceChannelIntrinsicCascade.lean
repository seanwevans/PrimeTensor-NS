import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailFixedBalanceChannelDivergenceSequence
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.CharacteristicFrequencyFullLimit
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.FullEnergyNormalizedCascade

/-!
# Synchronizing a fixed balance mechanism with the full intrinsic H³ cascade

The fixed-channel sequence constructed previously already carries one fixed
balance mechanism -- rapid H³ energy decay or adverse H³ transport -- together
with its raw, physical-clock, and normalized divergences.

Independently, hypothetical nonextension forces a branch-free intrinsic cascade
on the entire physical left terminal tail.  Therefore the same fixed-channel
sequence automatically inherits that full-tail information.  No further
subsequence extraction is needed.

This file packages the simultaneous terminal behavior of

* top and full H³ energy;
* top/full dissipation ratios;
* top and full dissipation;
* characteristic frequency and characteristic length;
* top/full energy physical clocks; and
* top/full dissipation physical clocks.

The result remains neutral between the two exact H³ balance mechanisms.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The branch-free intrinsic H³ terminal cascade evaluated along one explicit
physical-time sequence. -/
def H3TerminalIntrinsicCascadeAlong
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ)
    (τ : ℕ → ℝ) : Prop :=
  Tendsto τ atTop (𝓝 T)
    ∧
  Tendsto
    (fun n : ℕ => velocityH3Energy3At u (τ n))
    atTop atTop
    ∧
  Tendsto
    (fun n : ℕ => velocityH3EnergyAt u (τ n))
    atTop atTop
    ∧
  Tendsto
    (fun n : ℕ =>
      velocityH3Dissipation3At u (τ n) /
        velocityH3Energy3At u (τ n))
    atTop atTop
    ∧
  Tendsto
    (fun n : ℕ =>
      velocityH3DissipationAt u (τ n) /
        velocityH3Energy3At u (τ n))
    atTop atTop
    ∧
  Tendsto
    (fun n : ℕ =>
      velocityH3Dissipation3At u (τ n) /
        velocityH3EnergyAt u (τ n))
    atTop atTop
    ∧
  Tendsto
    (fun n : ℕ =>
      velocityH3DissipationAt u (τ n) /
        velocityH3EnergyAt u (τ n))
    atTop atTop
    ∧
  Tendsto
    (fun n : ℕ => velocityH3Dissipation3At u (τ n))
    atTop atTop
    ∧
  Tendsto
    (fun n : ℕ => velocityH3DissipationAt u (τ n))
    atTop atTop
    ∧
  Tendsto
    (fun n : ℕ => h3TopCharacteristicFrequencyAt u (τ n))
    atTop atTop
    ∧
  Tendsto
    (fun n : ℕ => h3TopCharacteristicLengthAt u (τ n))
    atTop (𝓝 0)
    ∧
  Tendsto
    (fun n : ℕ =>
      (T - τ n) * velocityH3Energy3At u (τ n))
    atTop atTop
    ∧
  Tendsto
    (fun n : ℕ =>
      (T - τ n) * velocityH3EnergyAt u (τ n))
    atTop atTop
    ∧
  Tendsto
    (fun n : ℕ =>
      (T - τ n) * velocityH3Dissipation3At u (τ n))
    atTop atTop
    ∧
  Tendsto
    (fun n : ℕ =>
      (T - τ n) * velocityH3DissipationAt u (τ n))
    atTop atTop

/-- Any explicit sequence converging to `T` from below inherits the entire
branch-free intrinsic H³ cascade under hypothetical nonextension. -/
theorem h3TerminalIntrinsicCascadeAlong_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hTau : Tendsto τ atTop (𝓝 T))
    (hBelow : ∀ n : ℕ, τ n < T) :
    H3TerminalIntrinsicCascadeAlong u T τ := by

  have hTauLT :
      Tendsto τ atTop (𝓝[<] T) := by
    exact
      tendsto_nhdsWithin_iff.mpr
        ⟨
          hTau,
          Eventually.of_forall hBelow
        ⟩

  have hE3 :
      Tendsto
        (fun n : ℕ => velocityH3Energy3At u (τ n))
        atTop atTop :=
    (velocityH3Energy3At_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass).comp hTauLT

  have hE :
      Tendsto
        (fun n : ℕ => velocityH3EnergyAt u (τ n))
        atTop atTop :=
    (velocityH3EnergyAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass).comp hTauLT

  have hD3E3 :
      Tendsto
        (fun n : ℕ =>
          velocityH3Dissipation3At u (τ n) /
            velocityH3Energy3At u (τ n))
        atTop atTop :=
    (velocityH3Dissipation3At_div_energy3At_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass).comp hTauLT

  have hDE3 :
      Tendsto
        (fun n : ℕ =>
          velocityH3DissipationAt u (τ n) /
            velocityH3Energy3At u (τ n))
        atTop atTop :=
    (velocityH3DissipationAt_div_energy3At_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass).comp hTauLT

  have hD3E :
      Tendsto
        (fun n : ℕ =>
          velocityH3Dissipation3At u (τ n) /
            velocityH3EnergyAt u (τ n))
        atTop atTop :=
    (velocityH3Dissipation3At_div_energyAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass).comp hTauLT

  have hDE :
      Tendsto
        (fun n : ℕ =>
          velocityH3DissipationAt u (τ n) /
            velocityH3EnergyAt u (τ n))
        atTop atTop :=
    (velocityH3DissipationAt_div_energyAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass).comp hTauLT

  have hD3 :
      Tendsto
        (fun n : ℕ => velocityH3Dissipation3At u (τ n))
        atTop atTop :=
    (velocityH3Dissipation3At_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass).comp hTauLT

  have hD :
      Tendsto
        (fun n : ℕ => velocityH3DissipationAt u (τ n))
        atTop atTop :=
    (velocityH3DissipationAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass).comp hTauLT

  have hFrequency :
      Tendsto
        (fun n : ℕ => h3TopCharacteristicFrequencyAt u (τ n))
        atTop atTop :=
    (h3TopCharacteristicFrequencyAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass).comp hTauLT

  have hLength :
      Tendsto
        (fun n : ℕ => h3TopCharacteristicLengthAt u (τ n))
        atTop (𝓝 0) :=
    (h3TopCharacteristicLengthAt_tendsto_zero_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass).comp hTauLT

  have hE3Clock :
      Tendsto
        (fun n : ℕ =>
          (T - τ n) * velocityH3Energy3At u (τ n))
        atTop atTop :=
    (velocityH3Energy3PhysicalClock_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass).comp hTauLT

  have hEClock :
      Tendsto
        (fun n : ℕ =>
          (T - τ n) * velocityH3EnergyAt u (τ n))
        atTop atTop :=
    (velocityH3EnergyPhysicalClock_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass).comp hTauLT

  have hD3Clock :
      Tendsto
        (fun n : ℕ =>
          (T - τ n) * velocityH3Dissipation3At u (τ n))
        atTop atTop :=
    (velocityH3Dissipation3PhysicalClock_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass).comp hTauLT

  have hDClock :
      Tendsto
        (fun n : ℕ =>
          (T - τ n) * velocityH3DissipationAt u (τ n))
        atTop atTop :=
    (velocityH3DissipationPhysicalClock_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass).comp hTauLT

  exact
    ⟨
      hTau,
      hE3,
      hE,
      hD3E3,
      hDE3,
      hD3E,
      hDE,
      hD3,
      hD,
      hFrequency,
      hLength,
      hE3Clock,
      hEClock,
      hD3Clock,
      hDClock
    ⟩

/-- Under hypothetical nonextension, one fixed exact H³ balance mechanism and
the entire branch-free intrinsic cascade occur on the same explicit terminal
sequence. -/
theorem exists_fixedBalanceChannel_with_intrinsicCascade_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    (
      ∃ τ : ℕ → ℝ,
        (∀ n : ℕ,
          τ n ∈ Set.Ioo b T
            ∧
          τ n ∈
            Set.Ioo
              (T - (1 : ℝ) / ((n : ℝ) + 1))
              T
            ∧
          H3TerminalDecayPolynomialRatesAt u T b (τ n))
          ∧
        Tendsto
          (fun n : ℕ => - deriv (velocityH3EnergyAt u) (τ n))
          atTop atTop
          ∧
        Tendsto
          (fun n : ℕ =>
            (T - τ n) * (- deriv (velocityH3EnergyAt u) (τ n)))
          atTop atTop
          ∧
        Tendsto
          (fun n : ℕ =>
            (- deriv (velocityH3EnergyAt u) (τ n)) /
              velocityH3EnergyAt u (τ n))
          atTop atTop
          ∧
        H3TerminalIntrinsicCascadeAlong u T τ
    )
      ∨
    (
      ∃ τ : ℕ → ℝ,
        (∀ n : ℕ,
          τ n ∈ Set.Ioo b T
            ∧
          τ n ∈
            Set.Ioo
              (T - (1 : ℝ) / ((n : ℝ) + 1))
              T
            ∧
          H3TerminalTransportPolynomialRatesAt u T b (τ n))
          ∧
        Tendsto
          (fun n : ℕ => - velocityH3TransportDerivativeAt u (τ n))
          atTop atTop
          ∧
        Tendsto
          (fun n : ℕ =>
            (T - τ n) * (- velocityH3TransportDerivativeAt u (τ n)))
          atTop atTop
          ∧
        Tendsto
          (fun n : ℕ =>
            (- velocityH3TransportDerivativeAt u (τ n)) /
              velocityH3EnergyAt u (τ n))
          atTop atTop
          ∧
        H3TerminalIntrinsicCascadeAlong u T τ
    ) := by

  rcases
    exists_fixedBalanceChannel_polynomialAndDivergenceSequence_of_noH3PathExtension
      hH3 hNoExtension hClass hb
    with hDecay | hTransport

  · rcases hDecay with
      ⟨τ, hData, hTau, hRaw, hPhysical, hNormalized⟩

    have hIntrinsic :
        H3TerminalIntrinsicCascadeAlong u T τ :=
      h3TerminalIntrinsicCascadeAlong_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
        hTau
        (fun n => (hData n).1.2)

    exact
      Or.inl
        ⟨
          τ,
          hData,
          hRaw,
          hPhysical,
          hNormalized,
          hIntrinsic
        ⟩

  · rcases hTransport with
      ⟨τ, hData, hTau, hRaw, hPhysical, hNormalized⟩

    have hIntrinsic :
        H3TerminalIntrinsicCascadeAlong u T τ :=
      h3TerminalIntrinsicCascadeAlong_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
        hTau
        (fun n => (hData n).1.2)

    exact
      Or.inr
        ⟨
          τ,
          hData,
          hRaw,
          hPhysical,
          hNormalized,
          hIntrinsic
        ⟩

/-- Neutral positive form: either smooth continuation exists, or one fixed
balance mechanism is synchronized with the entire intrinsic terminal cascade on
one explicit physical-time sequence. -/
theorem smoothContinuationExtension_or_exists_fixedBalanceChannel_with_intrinsicCascade
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    (
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
    )
      ∨
    (
      (
        ∃ τ : ℕ → ℝ,
          (∀ n : ℕ,
            τ n ∈ Set.Ioo b T
              ∧
            τ n ∈
              Set.Ioo
                (T - (1 : ℝ) / ((n : ℝ) + 1))
                T
              ∧
            H3TerminalDecayPolynomialRatesAt u T b (τ n))
            ∧
          Tendsto
            (fun n : ℕ => - deriv (velocityH3EnergyAt u) (τ n))
            atTop atTop
            ∧
          Tendsto
            (fun n : ℕ =>
              (T - τ n) * (- deriv (velocityH3EnergyAt u) (τ n)))
            atTop atTop
            ∧
          Tendsto
            (fun n : ℕ =>
              (- deriv (velocityH3EnergyAt u) (τ n)) /
                velocityH3EnergyAt u (τ n))
            atTop atTop
            ∧
          H3TerminalIntrinsicCascadeAlong u T τ
      )
        ∨
      (
        ∃ τ : ℕ → ℝ,
          (∀ n : ℕ,
            τ n ∈ Set.Ioo b T
              ∧
            τ n ∈
              Set.Ioo
                (T - (1 : ℝ) / ((n : ℝ) + 1))
                T
              ∧
            H3TerminalTransportPolynomialRatesAt u T b (τ n))
            ∧
          Tendsto
            (fun n : ℕ => - velocityH3TransportDerivativeAt u (τ n))
            atTop atTop
            ∧
          Tendsto
            (fun n : ℕ =>
              (T - τ n) * (- velocityH3TransportDerivativeAt u (τ n)))
            atTop atTop
            ∧
          Tendsto
            (fun n : ℕ =>
              (- velocityH3TransportDerivativeAt u (τ n)) /
                velocityH3EnergyAt u (τ n))
            atTop atTop
            ∧
          H3TerminalIntrinsicCascadeAlong u T τ
      )
    ) := by
  classical

  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact Or.inl hExtension

  · exact
      Or.inr
        (exists_fixedBalanceChannel_with_intrinsicCascade_of_noH3PathExtension
          hH3 hExtension hClass hb)

/-- Canonical midpoint-anchor specialization of the fixed balance mechanism
synchronized with the entire intrinsic H³ cascade. -/
theorem exists_fixedBalanceChannel_with_intrinsicCascade_midpoint_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (
      ∃ τ : ℕ → ℝ,
        (∀ n : ℕ,
          τ n ∈ Set.Ioo (h3BKMKineticTailMidpoint a T) T
            ∧
          τ n ∈
            Set.Ioo
              (T - (1 : ℝ) / ((n : ℝ) + 1))
              T
            ∧
          H3TerminalDecayPolynomialRatesAt
            u T (h3BKMKineticTailMidpoint a T) (τ n))
          ∧
        Tendsto
          (fun n : ℕ => - deriv (velocityH3EnergyAt u) (τ n))
          atTop atTop
          ∧
        Tendsto
          (fun n : ℕ =>
            (T - τ n) * (- deriv (velocityH3EnergyAt u) (τ n)))
          atTop atTop
          ∧
        Tendsto
          (fun n : ℕ =>
            (- deriv (velocityH3EnergyAt u) (τ n)) /
              velocityH3EnergyAt u (τ n))
          atTop atTop
          ∧
        H3TerminalIntrinsicCascadeAlong u T τ
    )
      ∨
    (
      ∃ τ : ℕ → ℝ,
        (∀ n : ℕ,
          τ n ∈ Set.Ioo (h3BKMKineticTailMidpoint a T) T
            ∧
          τ n ∈
            Set.Ioo
              (T - (1 : ℝ) / ((n : ℝ) + 1))
              T
            ∧
          H3TerminalTransportPolynomialRatesAt
            u T (h3BKMKineticTailMidpoint a T) (τ n))
          ∧
        Tendsto
          (fun n : ℕ => - velocityH3TransportDerivativeAt u (τ n))
          atTop atTop
          ∧
        Tendsto
          (fun n : ℕ =>
            (T - τ n) * (- velocityH3TransportDerivativeAt u (τ n)))
          atTop atTop
          ∧
        Tendsto
          (fun n : ℕ =>
            (- velocityH3TransportDerivativeAt u (τ n)) /
              velocityH3EnergyAt u (τ n))
          atTop atTop
          ∧
        H3TerminalIntrinsicCascadeAlong u T τ
    ) := by
  exact
    exists_fixedBalanceChannel_with_intrinsicCascade_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      (h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2)

end

end Euclidean
end Bridge
end PrimeTensor
