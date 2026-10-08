import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Clock.QuantitativeNoExtension

/-! Neutral continuation alternative with quantitative sampled thresholds.
No additional analytic hypotheses are imposed. -/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

/-- Neutral endpoint alternative with positive finite sampled thresholds,
energy escape, or the synchronized critical-width witness. -/
theorem smoothContinuationExtension_or_quantitativeCriticalAlternative_and_higherRadialUniversalEscape_after_resolvedPDEClosure
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
            H3TerminalPhysicalTopDissipationResolvedCanonicalForcingQuantitativeCriticalAlternativeEscapeSubsequenceOf
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
          exists_fixed_terminalSequence_with_quantitativeCriticalAlternative_and_higherRadialUniversalEscape_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
