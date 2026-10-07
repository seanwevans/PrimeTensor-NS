import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing.Pointwise.Component.Representative.Adjacent.Envelope.Pair.StateMass.Primitive.Rate.Classify.Radial.Resolve.Package.NoExtension.Higher.Rate.Branch.Higher.Direct.Branch.Scale.Width.InverseSqrt.Package.Normalized.Package.PhysicalClock.NoExtension

/-! Neutral continuation alternative with the physical-left-clock floor.
The obstruction still permits H3 energy escape or either radial branch. -/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

/--
Neutral endpoint alternative: either a smooth continuation exists, or the
positive physical-left-clock normalized higher-radial floor and universal
higher-radial cascade occur on one common terminal parent sequence.
-/
theorem smoothContinuationExtension_or_physicalLeftClockPositiveFloor_and_higherRadialUniversalEscape_after_resolvedPDEClosure
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    {ε : ℝ}
    (hε : 0 < ε) :
    (
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
    )
      ∨
    (
      ∃ k : ℕ → ℕ,
        StrictMono k
          ∧
        Tendsto
          (
            fun n : ℕ =>
              (1 : ℝ) / (((k n : ℕ) : ℝ) + 1)
          )
          atTop
          (𝓝 0)
          ∧
        ∃ σ : ℕ → ℝ,
          ∃ hσ :
            ∀ n : ℕ,
              σ n ∈ Set.Ioo a T,
            Tendsto σ atTop (𝓝 T)
              ∧
            (
              ∀ n : ℕ,
                ENNReal.ofReal (ε ^ 2 / 64)
                  <
                16 *
                  h3TerminalPhysicalDissipationBadConeHighRadialMass
                    hH3
                    i
                    ((1 : ℝ) / (((k n : ℕ) : ℝ) + 1))
                    1
                    (σ n)
                    ⟨
                      lt_trans hClass.terminal_start.1
                        (hσ n).1,
                      (hσ n).2
                    ⟩
            )
              ∧
            H3TerminalPhysicalTopDissipationResolvedCanonicalForcingPhysicalLeftClockPositiveFloorEscapeSubsequenceOf
              hH3 hClass σ
              ∧
            H3TerminalPhysicalExtendedHigherRadialMomentUniversalEscapeSubsequenceOf
              hH3 hClass σ
    ) := by

  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact
      Or.inl
        hExtension

  · exact
      Or.inr
        (
          exists_fixed_terminalSequence_with_physicalLeftClockPositiveFloor_and_higherRadialUniversalEscape_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
            hH3
            hClass
            hPhysical
            hCauchy
            hExtension
            hε
        )

end

end Euclidean
end Bridge
end PrimeTensor
