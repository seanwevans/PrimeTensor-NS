import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing.Pointwise.Component.Representative.Adjacent.Envelope.Pair.StateMass.Primitive.Rate.Classify.Radial.Resolve.Package.NoExtension.Higher.Rate.Branch.Package
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing.Pointwise.Component.Representative.Adjacent.Envelope.Pair.StateMass.Primitive.Rate.Classify.Radial.Resolve.Package.NoExtension.Higher.Rate.Branch.Higher.Package

/-!
# Package higher domination into the divergent resolved forcing geometry

The local divergent-rate branch now carries the exact same-time domination of
its selected radial-square mass by the corresponding extended higher-radial
moment.

This file changes only the terminal branch predicate.  Every canonical witness,
subsequence map, interval endpoint, and selected forcing time is preserved.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

def H3TerminalPhysicalTopDissipationResolvedCanonicalForcingDivergentRateHigherDominatedEscapeSubsequenceOf
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (σ : ℕ → ℝ) : Prop :=
  ∃ δ : ℝ,
    0 < δ
      ∧
    ∃ j₀ : Fin 3,
      ∃ m q φ ψ : ℕ → ℕ,
        Tendsto m atTop atTop
          ∧
        Tendsto q atTop atTop
          ∧
        StrictMono φ
          ∧
        StrictMono ψ
          ∧
        ∃ s r : ℕ → ℝ,
          ∃ hs :
            ∀ n : ℕ,
              s n ∈ Set.Ioo a T,
            ∃ hσ :
              ∀ n : ℕ,
                σ n ∈ Set.Ioo a T,
              ∃ hr :
                ∀ n : ℕ,
                  r (φ (ψ n)) ∈ Set.Ioo a T,
                Tendsto (fun n : ℕ => s (φ (ψ n))) atTop (𝓝 T)
                  ∧
                Tendsto
                  (fun n : ℕ => σ (m (q (φ (ψ n)))))
                  atTop
                  (𝓝 T)
                  ∧
                (∀ n : ℕ,
                  s (φ (ψ n)) < σ (m (q (φ (ψ n)))))
                  ∧
                (∀ n : ℕ,
                  r (φ (ψ n)) ∈
                    Set.Icc
                      (s (φ (ψ n)))
                      (σ (m (q (φ (ψ n))))))
                  ∧
                Tendsto (fun n : ℕ => r (φ (ψ n))) atTop (𝓝 T)
                  ∧
                ∃ χ ω : ℕ → ℕ,
                  StrictMono χ
                    ∧
                  StrictMono ω
                    ∧
                  Tendsto
                    (fun n : ℕ => s (φ (ψ (χ (ω n)))))
                    atTop
                    (𝓝 T)
                    ∧
                  Tendsto
                    (fun n : ℕ => σ (m (q (φ (ψ (χ (ω n)))))))
                    atTop
                    (𝓝 T)
                    ∧
                  Tendsto
                    (fun n : ℕ => r (φ (ψ (χ (ω n)))))
                    atTop
                    (𝓝 T)
                    ∧
                  let τ : ℕ → ℝ :=
                    fun n : ℕ => r (φ (ψ (χ (ω n))))
                  let hτ :
                      ∀ n : ℕ,
                        τ n ∈ Set.Ioo a T :=
                    fun n : ℕ => hr (χ (ω n))
                  let rate : ℕ → ℝ :=
                    fun n : ℕ =>
                      δ
                        /
                      (
                        12
                          *
                        (
                          σ (m (q (φ (ψ (χ (ω n))))))
                            -
                          s (φ (ψ (χ (ω n))))
                        )
                      )
                  H3TerminalResolvedCanonicalForcingDivergentRateHigherDominatedBranch
                    hH3 hClass τ hτ rate

theorem resolvedCanonicalForcingDivergentRateHigherDominatedEscapeSubsequenceOf_of_divergentRateEscapeSubsequenceOf
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (σ : ℕ → ℝ)
    (hDivergent :
      H3TerminalPhysicalTopDissipationResolvedCanonicalForcingDivergentRateEscapeSubsequenceOf
        hH3 hClass σ) :
    H3TerminalPhysicalTopDissipationResolvedCanonicalForcingDivergentRateHigherDominatedEscapeSubsequenceOf
      hH3 hClass σ := by

  obtain
    ⟨
      δ,
      hδ,
      j₀,
      m,
      q,
      φ,
      ψ,
      hmTop,
      hqTop,
      hPhiMono,
      hPsiMono,
      s,
      r,
      hs,
      hσ,
      hr,
      hsTendsto,
      hSigmaTendsto,
      hForward,
      hPoint,
      hrTendsto,
      χ,
      ω,
      hChiMono,
      hOmegaMono,
      hsFinal,
      hSigmaFinal,
      hrFinal,
      hBranch
    ⟩ :=
    hDivergent

  refine
    ⟨
      δ,
      hδ,
      j₀,
      m,
      q,
      φ,
      ψ,
      hmTop,
      hqTop,
      hPhiMono,
      hPsiMono,
      s,
      r,
      hs,
      hσ,
      hr,
      hsTendsto,
      hSigmaTendsto,
      hForward,
      hPoint,
      hrTendsto,
      χ,
      ω,
      hChiMono,
      hOmegaMono,
      hsFinal,
      hSigmaFinal,
      hrFinal,
      ?_
    ⟩

  let τ : ℕ → ℝ :=
    fun n : ℕ =>
      r (φ (ψ (χ (ω n))))

  let hτ :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo a T :=
    fun n : ℕ =>
      hr (χ (ω n))

  let rate : ℕ → ℝ :=
    fun n : ℕ =>
      δ
        /
      (
        12
          *
        (
          σ (m (q (φ (ψ (χ (ω n))))))
            -
          s (φ (ψ (χ (ω n))))
        )
      )

  have hHigher :
      H3TerminalResolvedCanonicalForcingDivergentRateHigherDominatedBranch
        hH3 hClass τ hτ rate :=
    resolvedCanonicalForcingDivergentRateHigherDominatedBranch_of_divergentRateBranch
      hH3
      hClass
      τ
      hτ
      rate
      (by
        simpa only [τ, hτ, rate] using hBranch)

  dsimp only

  simpa only [τ, hτ, rate] using
    hHigher

end

end Euclidean
end Bridge
end PrimeTensor
