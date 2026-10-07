import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing.Pointwise.Component.Representative.Adjacent.Envelope.Pair.StateMass.Primitive.Rate.Classify.Radial.Second
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing.Pointwise.Component.Representative.Adjacent.Envelope.Pair.StateMass.Primitive.Rate.Classify.Radial.Second.Moment10.Radial.Resolve

/-!
# Quantitative second-q moment-six resolution

The second-q derivative moment-six rate first resolves into raw-L1 or derivative
moment-ten.  Raw-L1 already forces physical H3-energy escape.  The derivative
moment-ten branch is now quantitatively resolved into either the same terminal
energy outcome or one fixed order-fourteen/order-sixteen radial-square channel.

Thus the only non-energy outcome retains the reciprocal-width lower rate on a
fixed higher-radial channel.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

theorem h3TerminalSecondQVelocityMoment6_rate_resolves_energy_or_fixedHigherRadial
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (τ : ℕ → ℝ)
    (hτ :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo a T)
    (hTauTendsto :
      Tendsto τ atTop (𝓝 T))
    (rate : ℕ → ℝ)
    (K : ℝ)
    (hK0 : 0 ≤ K)
    (hRate :
      ∀ n : ℕ,
        rate n
          <
        K
          *
        (
          h3TerminalSecondQForcingDerivativeVelocityMoment6MassAt
            hH3 hClass (hτ n) i
        ) ^ 4)
    (hMomentTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalSecondQForcingDerivativeVelocityMoment6MassAt
              hH3 hClass (hτ n) i
        )
        atTop
        atTop) :
    (
      ∃ s : ℕ → ℕ,
        StrictMono s
          ∧
        Tendsto
          (fun n : ℕ => τ (s n))
          atTop
          (𝓝 T)
          ∧
        Tendsto
          (
            fun n : ℕ =>
              velocityH3EnergyAt u (τ (s n))
          )
          atTop
          atTop
    )
      ∨
    (
      ∃ q : Fin 2,
        ∃ s : ℕ → ℕ,
          StrictMono s
            ∧
          Tendsto
            (fun n : ℕ => τ (s n))
            atTop
            (𝓝 T)
            ∧
          (
            ∀ n : ℕ,
              rate (s n)
                <
              (K * 256)
                *
              (
                h3StandardInverseBesselWeightL2Factor
                  *
                (
                  2
                    *
                  Real.sqrt
                    (
                      h3TerminalForcingThirdQMoment14RadialSquareChannelAt
                        hH3 hClass (hτ (s n)) i q
                    )
                )
              ) ^ 4
          )
            ∧
          Tendsto
            (
              fun n : ℕ =>
                h3TerminalForcingThirdQMoment14RadialSquareChannelAt
                  hH3 hClass (hτ (s n)) i q
            )
            atTop
            atTop
            ∧
          Tendsto
            (
              fun n : ℕ =>
                h3TerminalPhysicalExtendedHigherRadialMomentAt
                  hH3 hClass
                  (h3TerminalForcingThirdQHigherRadialShift q)
                  (τ (s n))
                  (hτ (s n))
            )
            atTop
            (𝓝 ∞)
    ) := by

  rcases
    h3TerminalSecondQVelocityMoment6_rate_split_rawL1_or_velocityMoment10
      hH3 hClass i τ hτ hTauTendsto rate K hK0 hRate hMomentTop with
    hEnergy | hMoment10

  · obtain
      ⟨s, hMono, hTauSub, _hRateL1, _hL1Top, hEnergyTop⟩ :=
      hEnergy

    exact
      Or.inl
        ⟨
          s,
          hMono,
          hTauSub,
          hEnergyTop
        ⟩

  · obtain
      ⟨s, hMono, hTauSub, hRate10, hMoment10Top⟩ :=
      hMoment10

    have hK16 :
        0 ≤ K * (16 : ℝ) :=
      mul_nonneg
        hK0
        (by norm_num)

    have hRate10Scaled :
        ∀ n : ℕ,
          rate (s n)
            <
          (K * 16)
            *
          (
            h3TerminalFourthQForcingDerivativeVelocityMoment10MassAt
              hH3 hClass (hτ (s n)) i
          ) ^ 4 := by

      intro n

      have hRaw :=
        hRate10 n

      convert hRaw using 1 <;>
        ring

    rcases
      h3TerminalFourthQForcingDerivativeVelocityMoment10_rate_resolves_energy_or_fixedHigherRadial
        hH3
        hClass
        i
        (fun n : ℕ => τ (s n))
        (fun n : ℕ => hτ (s n))
        hTauSub
        (fun n : ℕ => rate (s n))
        (K * 16)
        hK16
        hRate10Scaled
        hMoment10Top with
      hEnergyFinal | hRadialFinal

    · obtain
        ⟨v, hvMono, hTauFinal, _hRateL1, _hL1Top, hEnergyTop⟩ :=
        hEnergyFinal

      exact
        Or.inl
          ⟨
            (fun n : ℕ => s (v n)),
            hMono.comp hvMono,
            hTauFinal,
            hEnergyTop
          ⟩

    · obtain
        ⟨q, v, hvMono, hTauFinal, hRateFinal, hSquareTop, hHigherTop⟩ :=
        hRadialFinal

      have hRateFinal' :
          ∀ n : ℕ,
            rate (s (v n))
              <
            (K * 256)
              *
            (
              h3StandardInverseBesselWeightL2Factor
                *
              (
                2
                  *
                Real.sqrt
                  (
                    h3TerminalForcingThirdQMoment14RadialSquareChannelAt
                      hH3 hClass (hτ (s (v n))) i q
                  )
              )
            ) ^ 4 := by

        intro n

        have hRaw :=
          hRateFinal n

        convert hRaw using 1 <;>
          ring

      exact
        Or.inr
          ⟨
            q,
            (fun n : ℕ => s (v n)),
            hMono.comp hvMono,
            hTauFinal,
            hRateFinal',
            hSquareTop,
            hHigherTop
          ⟩

end

end Euclidean
end Bridge
end PrimeTensor
