import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing.Pointwise.Component.Representative.Adjacent.Envelope.Pair.StateMass.Primitive.Rate.Classify.Radial.Resolve.Package
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing.Pointwise.Component.Representative.Adjacent.Envelope.Pair.StateMass.Primitive.Rate.Classify.Radial.Resolve.Package.NoExtension.Higher.Rate.Branch

/-!
# Package the divergent resolved canonical forcing rate

The resolved package already reduces the canonical forcing obstruction to
energy escape or one of two fixed higher-radial channels.  The branch sharpener
adds the missing quantitative fact that the inherited reciprocal-width rate
itself tends to `+∞`.

A named branch predicate keeps that strengthened conclusion reusable without
duplicating the full terminal geometry in every downstream theorem.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

def H3TerminalResolvedCanonicalForcingDivergentRateBranch
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (rate : ℕ → ℝ) : Prop :=
  (
    ∃ v : ℕ → ℕ,
      StrictMono v
        ∧
      Tendsto (fun n : ℕ => τ (v n)) atTop (𝓝 T)
        ∧
      Tendsto
        (fun n : ℕ => velocityH3EnergyAt u (τ (v n)))
        atTop
        atTop
  )
    ∨
  (
    ∃ j : Fin 3,
      ∃ qRadial : Fin 2,
        ∃ v : ℕ → ℕ,
          StrictMono v
            ∧
          Tendsto (fun n : ℕ => τ (v n)) atTop (𝓝 T)
            ∧
          Tendsto (fun n : ℕ => rate (v n)) atTop atTop
            ∧
          (
            ∀ n : ℕ,
              rate (v n)
                <
              (
                (
                  (h3TerminalForcingSecondQFixedPairCoefficient : ℝ) ^ 2
                    *
                  (2 * h3FourierMomentSplitCoefficient (6 : ℝ))
                )
                  *
                256
              )
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
                        hH3 hClass (hτ (v n)) j qRadial
                    )
                )
              ) ^ 4
          )
            ∧
          Tendsto
            (
              fun n : ℕ =>
                h3TerminalForcingThirdQMoment14RadialSquareChannelAt
                  hH3 hClass (hτ (v n)) j qRadial
            )
            atTop
            atTop
            ∧
          Tendsto
            (
              fun n : ℕ =>
                h3TerminalPhysicalExtendedHigherRadialMomentAt
                  hH3 hClass
                  (h3TerminalForcingThirdQHigherRadialShift qRadial)
                  (τ (v n))
                  (hτ (v n))
            )
            atTop
            (𝓝 ∞)
  )
    ∨
  (
    ∃ j : Fin 3,
      ∃ qRadial : Fin 2,
        ∃ v : ℕ → ℕ,
          StrictMono v
            ∧
          Tendsto (fun n : ℕ => τ (v n)) atTop (𝓝 T)
            ∧
          Tendsto (fun n : ℕ => rate (v n)) atTop atTop
            ∧
          (
            ∀ n : ℕ,
              rate (v n)
                <
              (
                (h3TerminalForcingFourthQFixedPairCoefficient : ℝ) ^ 2
                  *
                (2 * h3FourierMomentSplitCoefficient (10 : ℝ))
              )
                *
              (
                h3StandardInverseBesselWeightL2Factor
                  *
                (
                  2
                    *
                  Real.sqrt
                    (
                      h3TerminalForcingFourthQMoment10RadialSquareChannelAt
                        hH3 hClass (hτ (v n)) j qRadial
                    )
                )
              ) ^ 4
          )
            ∧
          Tendsto
            (
              fun n : ℕ =>
                h3TerminalForcingFourthQMoment10RadialSquareChannelAt
                  hH3 hClass (hτ (v n)) j qRadial
            )
            atTop
            atTop
            ∧
          Tendsto
            (
              fun n : ℕ =>
                h3TerminalPhysicalExtendedHigherRadialMomentAt
                  hH3 hClass
                  (h3TerminalForcingFourthQHigherRadialShift qRadial)
                  (τ (v n))
                  (hτ (v n))
            )
            atTop
            (𝓝 ∞)
  )

def H3TerminalPhysicalTopDissipationResolvedCanonicalForcingDivergentRateEscapeSubsequenceOf
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
                  H3TerminalResolvedCanonicalForcingDivergentRateBranch
                    hH3 hClass τ hτ rate

theorem resolvedCanonicalForcingDivergentRateEscapeSubsequenceOf_of_resolvedCanonicalForcingRateEscapeSubsequenceOf
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (σ : ℕ → ℝ)
    (hResolved :
      H3TerminalPhysicalTopDissipationResolvedCanonicalForcingRateEscapeSubsequenceOf
        hH3 hClass σ) :
    H3TerminalPhysicalTopDissipationResolvedCanonicalForcingDivergentRateEscapeSubsequenceOf
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
    hResolved

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

  let sFinal : ℕ → ℝ :=
    fun n : ℕ =>
      s (φ (ψ (χ (ω n))))

  let tFinal : ℕ → ℝ :=
    fun n : ℕ =>
      σ (m (q (φ (ψ (χ (ω n))))))

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
          tFinal n
            -
          sFinal n
        )
      )

  have htUpper :
      ∀ n : ℕ,
        tFinal n < T := by

    intro n

    dsimp only [tFinal]

    exact
      (hσ (m (q (φ (ψ (χ (ω n))))))).2

  have hForwardFinal :
      ∀ n : ℕ,
        sFinal n < tFinal n := by

    intro n

    dsimp only [sFinal, tFinal]

    exact
      hForward (χ (ω n))

  have hRateEq :
      ∀ n : ℕ,
        rate n
          =
        δ
          /
        (
          12
            *
          (
            tFinal n
              -
            sFinal n
          )
        ) := by

    intro n
    rfl

  have hSharpRaw :=
    h3TerminalResolvedCanonicalForcingRateBranch_adds_rate_tendstoAtTop
      hH3
      hClass
      hδ
      sFinal
      tFinal
      τ
      rate
      hτ
      (by
        simpa only [sFinal] using hsFinal)
      htUpper
      hForwardFinal
      hRateEq
      (by
        simpa only [τ, hτ, rate, sFinal, tFinal] using hBranch)

  have hSharp :
      H3TerminalResolvedCanonicalForcingDivergentRateBranch
        hH3 hClass τ hτ rate := by

    simpa only [
      H3TerminalResolvedCanonicalForcingDivergentRateBranch
    ] using
      hSharpRaw

  dsimp only

  simpa only [
    τ,
    hτ,
    rate,
    sFinal,
    tFinal
  ] using
    hSharp

end

end Euclidean
end Bridge
end PrimeTensor
