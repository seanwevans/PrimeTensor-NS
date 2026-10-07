import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing.Pointwise.Component.Representative.Adjacent.Envelope.Pair.StateMass.Primitive.Rate.Classify.Radial.Resolve.Package.NoExtension
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Higher

/-!
# Synchronize resolved forcing rate with the higher-radial cascade

The resolved canonical forcing-rate theorem and the canonical higher-radial
cascade are both consequences of the same single-time bad-cone witness.

This file keeps the canonical terminal sequence `σ` fixed and packages both
conclusions on that same parent sequence:

* the resolved energy-or-fixed-radial forcing-rate obstruction;
* universal escape of every nonzero extended higher radial moment on a
  subsequence of `σ`.

No fresh parent terminal sequence is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

theorem exists_fixed_terminalSequence_with_resolvedCanonicalForcingRate_and_higherRadialUniversalEscape_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
          H3TerminalPhysicalTopDissipationResolvedCanonicalForcingRateEscapeSubsequenceOf
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
      hResolved
    ⟩ :=
    exists_fixed_terminalSequence_with_resolvedCanonicalForcingRateEscape_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3
      hClass
      hPhysical
      hCauchy
      hNoExtension
      hε

  let κ : ℕ → ℝ :=
    fun n =>
      (1 : ℝ) / (((k n : ℕ) : ℝ) + 1)

  have hκPos :
      ∀ n : ℕ,
        0 < κ n := by

    intro n
    dsimp only [κ]
    positivity

  have hKappa :
      Tendsto κ atTop (𝓝 0) := by

    simpa only [κ] using
      hAperture

  have hEscape :
      H3TerminalPhysicalDissipationRadialEscapeSubsequenceOf
        hH3 hClass σ :=
    physicalDissipationRadialEscapeSubsequenceOf_of_singleTimeBadConeMass_of_velocityRawFourierL2Cauchy
      hH3
      hClass
      hCauchy
      i
      σ
      hσ
      hSigma
      κ
      hκPos
      hKappa
      hε
      (by
        intro n
        dsimp only [κ]
        exact hLocal n)

  have hHigher :
      H3TerminalPhysicalExtendedHigherRadialMomentUniversalEscapeSubsequenceOf
        hH3 hClass σ :=
    extendedHigherRadialMomentUniversalEscapeSubsequenceOf_of_physicalDissipationRadialEscapeSubsequenceOf
      hH3
      hClass
      σ
      hEscape

  exact
    ⟨
      k,
      hKMono,
      hAperture,
      σ,
      hσ,
      hSigma,
      hLocal,
      hResolved,
      hHigher
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
