import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.Closure

/-!
# Close the terminal second-q forcing derivative obstruction

The second-q branch has now been reduced through the complete finite chain

    derivative escape
      -> fixed order-three radial product channel
      -> Young state-mass envelope
      -> one fixed primitive mass
      -> energy or extended higher-radial escape.

This file only composes those already-proved reductions.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

theorem h3TerminalSecondQForcingDerivative_escape_energy_or_fixedExtendedHigherRadial
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hTauTendsto : Tendsto τ atTop (𝓝 T))
    (hDerivTop :
      Tendsto
        (fun n : ℕ =>
          ‖deriv
            (h3TerminalPhysicalTopDissipationForcingSecondQFourierL2Path
              hH3 hClass j)
            (τ n)‖)
        atTop atTop) :
    (
      ∃ s : ℕ → ℕ,
        (∀ n : ℕ, n ≤ s n) ∧
        Tendsto s atTop atTop ∧
        Tendsto (fun n : ℕ => τ (s n)) atTop (𝓝 T) ∧
        Tendsto
          (fun n : ℕ =>
            velocityH3EnergyAt u (τ (s n)))
          atTop atTop
    )
      ∨
    (
      ∃ m : ℕ,
        m ≠ 0 ∧
        ∃ s : ℕ → ℕ,
          (∀ n : ℕ, n ≤ s n) ∧
          Tendsto s atTop atTop ∧
          Tendsto (fun n : ℕ => τ (s n)) atTop (𝓝 T) ∧
          Tendsto
            (fun n : ℕ =>
              h3TerminalPhysicalExtendedHigherRadialMomentAt
                hH3 hClass m
                (τ (s n))
                (hτ (s n)))
            atTop (𝓝 ∞)
    ) := by

  obtain
    ⟨o, k, l, s, hs, hsTop, hTauSub, hProductTop⟩ :=
    exists_fixed_orientation_pair_subsequence_of_h3TerminalSecondQForcingDerivative_tendstoAtTop
      hH3 hClass j τ hτ hTauTendsto hDerivTop

  have hEnvelopeTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalSecondQForcingDerivativeStateMassEnvelopeAt
            hH3 hClass (hτ (s n)) j o k l)
        atTop atTop :=
    h3TerminalSecondQForcingDerivativeStateMassEnvelopeAt_tendstoAtTop_of_productNorm_tendstoAtTop
      hH3 hClass j o k l
      (fun n : ℕ => τ (s n))
      (fun n : ℕ => hτ (s n))
      hProductTop

  obtain
    ⟨q, v, hv, hvTop, hTauPrimitive, hPrimitiveTop⟩ :=
    exists_fixed_h3TerminalSecondQForcingDerivativePrimitiveFactor_subsequence_of_stateMassEnvelope_tendstoAtTop
      hH3 hClass j o k l
      (fun n : ℕ => τ (s n))
      (fun n : ℕ => hτ (s n))
      hTauSub
      hEnvelopeTop

  rcases
    h3TerminalSecondQForcingDerivativePrimitiveFactor_escape_energy_or_fixedExtendedHigherRadial
      hH3 hClass j o k l q
      (fun n : ℕ => τ (s (v n)))
      (fun n : ℕ => hτ (s (v n)))
      hTauPrimitive
      hPrimitiveTop
  with hEnergy | hHigher

  · rcases hEnergy with
      ⟨w, hw, hwTop, hTauFinal, hEnergyTop⟩

    have hComp :
        ∀ n : ℕ,
          n ≤ s (v (w n)) := by
      intro n
      exact
        le_trans
          (hw n)
          (le_trans
            (hv (w n))
            (hs (v (w n))))

    have hCompTop :
        Tendsto
          (fun n : ℕ => s (v (w n)))
          atTop atTop :=
      hsTop.comp
        (hvTop.comp hwTop)

    exact
      Or.inl
        ⟨
          (fun n : ℕ => s (v (w n))),
          hComp,
          hCompTop,
          hTauFinal,
          hEnergyTop
        ⟩

  · rcases hHigher with
      ⟨m, hm, w, hw, hwTop, hTauFinal, hHigherTop⟩

    have hComp :
        ∀ n : ℕ,
          n ≤ s (v (w n)) := by
      intro n
      exact
        le_trans
          (hw n)
          (le_trans
            (hv (w n))
            (hs (v (w n))))

    have hCompTop :
        Tendsto
          (fun n : ℕ => s (v (w n)))
          atTop atTop :=
      hsTop.comp
        (hvTop.comp hwTop)

    exact
      Or.inr
        ⟨
          m,
          hm,
          (fun n : ℕ => s (v (w n))),
          hComp,
          hCompTop,
          hTauFinal,
          hHigherTop
        ⟩

end

end Euclidean
end Bridge
end PrimeTensor
