import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing.Pointwise.Component.Representative.Adjacent.Envelope.Pair.StateMass.Primitive.Rate.Classify.Radial.Second.Moment10.Radial

/-!
# Quantitative derivative moment-ten resolution

The derivative velocity moment-ten rate split has two outcomes.  The raw-L1
branch already forces physical H3-energy escape.  In the moment-fourteen branch,
the quantitative order-fourteen radial reduction freezes one neighboring radial
square channel and lifts it to a fixed extended higher-radial channel.

Thus the derivative moment-ten rate resolves quantitatively into either the
energy branch or one fixed higher-radial branch.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

theorem h3TerminalFourthQForcingDerivativeVelocityMoment10_rate_resolves_energy_or_fixedHigherRadial
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
          h3TerminalFourthQForcingDerivativeVelocityMoment10MassAt
            hH3 hClass (hτ n) i
        ) ^ 4)
    (hMomentTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalFourthQForcingDerivativeVelocityMoment10MassAt
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
        (
          ∀ n : ℕ,
            rate (s n)
              <
            K
              *
            (
              2
                *
              h3TerminalForcingThirdQRawL1MassAt
                hH3 hClass (hτ (s n)) i
            ) ^ 4
        )
          ∧
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalForcingThirdQRawL1MassAt
                hH3 hClass (hτ (s n)) i
          )
          atTop
          atTop
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
              (K * 16)
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
    h3TerminalFourthQForcingDerivativeVelocityMoment10_rate_split_rawL1_or_moment14
      hH3 hClass i τ hτ hTauTendsto rate K hK0 hRate hMomentTop with
    hEnergy | hMoment14

  · exact Or.inl hEnergy

  · obtain
      ⟨s, hMono, hTauSub, hRate14, hMoment14Top⟩ :=
      hMoment14

    have hK16 :
        0 ≤ K * (16 : ℝ) :=
      mul_nonneg
        hK0
        (by norm_num)

    have hRate14Scaled :
        ∀ n : ℕ,
          rate (s n)
            <
          (K * 16)
            *
          (
            h3TerminalForcingThirdQMoment14MassAt
              hH3 hClass (hτ (s n)) i
          ) ^ 4 := by

      intro n

      have hRaw :=
        hRate14 n

      convert hRaw using 1 <;>
        ring

    obtain
      ⟨q, v, hvMono, hTauFinal, hRateFinal, hSquareTop, hHigherTop⟩ :=
      exists_fixed_h3TerminalForcingThirdQMoment14RadialSquareChannel_rate_subsequence
        hH3
        hClass
        i
        (fun n : ℕ => τ (s n))
        (fun n : ℕ => hτ (s n))
        hTauSub
        (fun n : ℕ => rate (s n))
        (K * 16)
        hK16
        hRate14Scaled
        hMoment14Top

    have hCompMono :
        StrictMono
          (fun n : ℕ => s (v n)) :=
      hMono.comp
        hvMono

    exact
      Or.inr
        ⟨
          q,
          (fun n : ℕ => s (v n)),
          hCompMono,
          hTauFinal,
          hRateFinal,
          hSquareTop,
          hHigherTop
        ⟩

end

end Euclidean
end Bridge
end PrimeTensor
