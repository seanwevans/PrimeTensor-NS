import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing.Pointwise.Component.Representative.Adjacent.Envelope.Pair.StateMass.Primitive.Rate.Classify.Radial.Resolve.Package.NoExtension.Higher.Rate.Branch.Higher.Direct.Branch.Scale.Width.InverseSqrt.Package.Normalized

/-!
# Terminal package for the critical square-root-width floor

Retain the canonical forward-time geometry and its selected parent sequence.
On the radial alternatives, the higher moment normalized by `sqrt gap` has
an eventual fixed positive lower bound and cannot converge to zero.
The energy-escape alternative is preserved.

The conversion uses the existing forward separation to prove positive width;
it introduces no additional extraction or analytic assumptions.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

def H3TerminalResolvedCanonicalForcingSqrtWidthPositiveFloorBranch
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (δ : ℝ) (gap : ℕ → ℝ) : Prop :=
    (∃ v : ℕ → ℕ,
      StrictMono v ∧
      Tendsto (fun n : ℕ => τ (v n)) atTop (𝓝 T) ∧
      Tendsto (fun n : ℕ => velocityH3EnergyAt u (τ (v n))) atTop atTop) ∨
    (∃ qRadial : Fin 2,
      H3TerminalHigherRadialSqrtWidthPositiveFloor
        hH3 hClass τ hτ gap
        (h3TerminalForcingThirdQHigherRadialShift qRadial)
        (h3TerminalForcingSecondQInverseSqrtWidthHigherCoefficient δ qRadial)) ∨
    (∃ qRadial : Fin 2,
      H3TerminalHigherRadialSqrtWidthPositiveFloor
        hH3 hClass τ hτ gap
        (h3TerminalForcingFourthQHigherRadialShift qRadial)
        (h3TerminalForcingFourthQInverseSqrtWidthHigherCoefficient δ qRadial))

def H3TerminalPhysicalTopDissipationResolvedCanonicalForcingSqrtWidthPositiveFloorEscapeSubsequenceOf
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
                    fun n : ℕ =>
                      r (φ (ψ (χ (ω n))))
                  let hτ :
                      ∀ n : ℕ,
                        τ n ∈ Set.Ioo a T :=
                    fun n : ℕ =>
                      hr (χ (ω n))
                  let gap : ℕ → ℝ :=
                    fun n : ℕ =>
                      σ (m (q (φ (ψ (χ (ω n))))))
                        -
                      s (φ (ψ (χ (ω n))))
                  H3TerminalResolvedCanonicalForcingSqrtWidthPositiveFloorBranch
                    hH3 hClass τ hτ δ gap

theorem resolvedCanonicalForcingSqrtWidthPositiveFloorEscapeSubsequenceOf_of_inverseSqrtWidthEscapeSubsequenceOf
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (σ : ℕ → ℝ)
    (hWidth :
      H3TerminalPhysicalTopDissipationResolvedCanonicalForcingDivergentInverseSqrtWidthHigherScaleEscapeSubsequenceOf
        hH3 hClass σ) :
    H3TerminalPhysicalTopDissipationResolvedCanonicalForcingSqrtWidthPositiveFloorEscapeSubsequenceOf
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
    hWidth

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

  let gap : ℕ → ℝ :=
    fun n : ℕ =>
      σ (m (q (φ (ψ (χ (ω n))))))
        -
      s (φ (ψ (χ (ω n))))

  have hGap :
      ∀ n : ℕ,
        0 < gap n := by

    intro n

    dsimp only [gap]

    exact
      sub_pos.mpr
        (hForward (χ (ω n)))

  have hWidthBranch :
      H3TerminalResolvedCanonicalForcingDivergentInverseSqrtWidthHigherScaleBranch
        hH3 hClass τ hτ δ gap := by

    simpa only [τ, hτ, gap] using
      hBranch

  have hInverseBranch :
      H3TerminalResolvedCanonicalForcingSqrtWidthPositiveFloorBranch
        hH3 hClass τ hτ δ gap :=
    resolvedCanonicalForcing_energy_or_sqrtWidthPositiveFloor
      hH3
      hClass
      τ
      hτ
      δ
      gap
      hδ
      hGap
      hWidthBranch

  dsimp only

  simpa only [τ, hτ, gap] using
    hInverseBranch

end

end Euclidean
end Bridge
end PrimeTensor
