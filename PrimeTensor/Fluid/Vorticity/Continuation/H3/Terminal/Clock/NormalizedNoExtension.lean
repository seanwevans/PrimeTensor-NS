import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Clock.InverseSqrtNoExtension
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Clock.NormalizedPackage

/-!
# Critical-width normalized floor under nonextension

Preserve the terminal parent sequence, shrinking bad cone, and universal
higher-radial escape while replacing the inverse-square-root profile package
by its positive normalized floor alternative. Energy escape remains allowed.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

theorem exists_fixed_terminalSequence_with_sqrtWidthPositiveFloor_and_higherRadialUniversalEscape_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
          SmoothContinuationExtension u v T)
    {ε : ℝ}
    (hε : 0 < ε) :
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
          H3TerminalPhysicalTopDissipationResolvedCanonicalForcingSqrtWidthPositiveFloorEscapeSubsequenceOf
            hH3 hClass σ
            ∧
          H3TerminalPhysicalExtendedHigherRadialMomentUniversalEscapeSubsequenceOf
            hH3 hClass σ := by

  obtain
    ⟨
      k,
      hKMono,
      hAperture,
      σ,
      hσ,
      hSigma,
      hLocal,
      hWidth,
      hHigher
    ⟩ :=
    exists_fixed_terminalSequence_with_inverseSqrtWidthHigherScale_and_higherRadialUniversalEscape_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3
      hClass
      hPhysical
      hCauchy
      hNoExtension
      hε

  have hInverse :
      H3TerminalPhysicalTopDissipationResolvedCanonicalForcingSqrtWidthPositiveFloorEscapeSubsequenceOf
        hH3 hClass σ :=
    resolvedCanonicalForcingSqrtWidthPositiveFloorEscapeSubsequenceOf_of_inverseSqrtWidthEscapeSubsequenceOf
      hH3
      hClass
      σ
      hWidth

  exact
    ⟨
      k,
      hKMono,
      hAperture,
      σ,
      hσ,
      hSigma,
      hLocal,
      hInverse,
      hHigher
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
