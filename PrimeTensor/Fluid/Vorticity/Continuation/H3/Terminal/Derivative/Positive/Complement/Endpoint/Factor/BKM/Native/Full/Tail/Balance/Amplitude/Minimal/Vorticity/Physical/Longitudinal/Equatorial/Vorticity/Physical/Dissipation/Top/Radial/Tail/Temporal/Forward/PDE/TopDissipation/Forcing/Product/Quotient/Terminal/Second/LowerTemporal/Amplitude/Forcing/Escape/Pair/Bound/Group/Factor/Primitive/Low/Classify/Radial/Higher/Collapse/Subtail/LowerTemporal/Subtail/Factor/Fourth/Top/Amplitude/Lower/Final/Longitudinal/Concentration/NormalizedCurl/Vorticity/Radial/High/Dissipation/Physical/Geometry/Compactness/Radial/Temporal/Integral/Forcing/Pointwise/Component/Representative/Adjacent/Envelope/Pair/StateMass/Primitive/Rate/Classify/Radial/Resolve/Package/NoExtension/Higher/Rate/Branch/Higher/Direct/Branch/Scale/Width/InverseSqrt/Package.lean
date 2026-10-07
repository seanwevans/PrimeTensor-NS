import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing.Pointwise.Component.Representative.Adjacent.Envelope.Pair.StateMass.Primitive.Rate.Classify.Radial.Resolve.Package.NoExtension.Higher.Rate.Branch.Higher.Direct.Branch.Scale.Width.Package
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing.Pointwise.Component.Representative.Adjacent.Envelope.Pair.StateMass.Primitive.Rate.Classify.Radial.Resolve.Package.NoExtension.Higher.Rate.Branch.Higher.Direct.Branch.Scale.Width.InverseSqrt

/-!
# Package the canonical inverse-square-root width obstruction

For positive canonical width, the preceding algebraic checkpoint rewrites the
direct higher-radial profile

    scale * sqrt (δ / (12 * K * gap))

as the exact profile

    C / sqrt gap,

with `C > 0` fixed on the selected radial branch.

This file first records that normalized local branch and then lifts it through
the full canonical terminal geometry.  In the outer package,

    gap n =
      σ (m (q (φ (ψ (χ (ω n)))))) -
      s (φ (ψ (χ (ω n)))),

and positivity follows directly from the retained forward-time separation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

def H3TerminalResolvedCanonicalForcingDivergentInverseSqrtWidthHigherScaleBranch
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (δ : ℝ)
    (gap : ℕ → ℝ) : Prop :=
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
          Tendsto
            (fun n : ℕ =>
              δ / (12 * gap (v n)))
            atTop
            atTop
            ∧
          Tendsto
            (
              fun n : ℕ =>
                h3TerminalForcingSecondQInverseSqrtWidthHigherCoefficient
                    δ qRadial
                  /
                Real.sqrt (gap (v n))
            )
            atTop
            atTop
            ∧
          Tendsto
            (
              fun n : ℕ =>
                ENNReal.ofReal
                  (
                    h3TerminalForcingSecondQInverseSqrtWidthHigherCoefficient
                        δ qRadial
                      /
                    Real.sqrt (gap (v n))
                  )
            )
            atTop
            (𝓝 ∞)
            ∧
          (
            ∀ᶠ n : ℕ in atTop,
              ENNReal.ofReal
                  (
                    h3TerminalForcingSecondQInverseSqrtWidthHigherCoefficient
                        δ qRadial
                      /
                    Real.sqrt (gap (v n))
                  )
                ≤
              h3TerminalPhysicalExtendedHigherRadialMomentAt
                hH3 hClass
                (h3TerminalForcingThirdQHigherRadialShift qRadial)
                (τ (v n))
                (hτ (v n))
          )
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
          Tendsto
            (fun n : ℕ =>
              δ / (12 * gap (v n)))
            atTop
            atTop
            ∧
          Tendsto
            (
              fun n : ℕ =>
                h3TerminalForcingFourthQInverseSqrtWidthHigherCoefficient
                    δ qRadial
                  /
                Real.sqrt (gap (v n))
            )
            atTop
            atTop
            ∧
          Tendsto
            (
              fun n : ℕ =>
                ENNReal.ofReal
                  (
                    h3TerminalForcingFourthQInverseSqrtWidthHigherCoefficient
                        δ qRadial
                      /
                    Real.sqrt (gap (v n))
                  )
            )
            atTop
            (𝓝 ∞)
            ∧
          (
            ∀ᶠ n : ℕ in atTop,
              ENNReal.ofReal
                  (
                    h3TerminalForcingFourthQInverseSqrtWidthHigherCoefficient
                        δ qRadial
                      /
                    Real.sqrt (gap (v n))
                  )
                ≤
              h3TerminalPhysicalExtendedHigherRadialMomentAt
                hH3 hClass
                (h3TerminalForcingFourthQHigherRadialShift qRadial)
                (τ (v n))
                (hτ (v n))
          )
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

theorem resolvedCanonicalForcingDivergentInverseSqrtWidthHigherScaleBranch_of_widthBranch
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (δ : ℝ)
    (gap : ℕ → ℝ)
    (hδ : 0 < δ)
    (hGap : ∀ n : ℕ, 0 < gap n)
    (hBranch :
      H3TerminalResolvedCanonicalForcingDivergentWidthDirectHigherScaleBranch
        hH3 hClass τ hτ δ gap) :
    H3TerminalResolvedCanonicalForcingDivergentInverseSqrtWidthHigherScaleBranch
      hH3 hClass τ hτ δ gap := by

  rcases hBranch with hEnergy | hSecond | hFourth

  · exact
      Or.inl
        hEnergy

  · obtain
      ⟨
        j,
        qRadial,
        v,
        hMono,
        hTauSub,
        hRateTop,
        hScaleTop,
        _hOfRealScaleTop,
        hDirect,
        hHigherTop
      ⟩ :=
      hSecond

    have hProfileEq :
        ∀ n : ℕ,
          h3TerminalForcingThirdQMoment14RadialSquareHigherScale qRadial
              *
            Real.sqrt
              (
                δ
                  /
                (
                  12
                    *
                  h3TerminalForcingSecondQResolvedHigherRadialRateCoefficient
                    *
                  gap (v n)
                )
              )
            =
          h3TerminalForcingSecondQInverseSqrtWidthHigherCoefficient
              δ qRadial
            /
          Real.sqrt (gap (v n)) := by

      intro n

      exact
        h3TerminalForcingThirdQHigherScale_sqrt_reciprocalWidth_eq_inverseSqrt
          hδ.le
          (hGap (v n))
          qRadial

    have hScaleFun :
        (
          fun n : ℕ =>
            h3TerminalForcingThirdQMoment14RadialSquareHigherScale qRadial
              *
            Real.sqrt
              (
                δ
                  /
                (
                  12
                    *
                  h3TerminalForcingSecondQResolvedHigherRadialRateCoefficient
                    *
                  gap (v n)
                )
              )
        )
          =
        (
          fun n : ℕ =>
            h3TerminalForcingSecondQInverseSqrtWidthHigherCoefficient
                δ qRadial
              /
            Real.sqrt (gap (v n))
        ) := by

      funext n

      exact
        hProfileEq n

    have hInverseScaleTop :
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalForcingSecondQInverseSqrtWidthHigherCoefficient
                  δ qRadial
                /
              Real.sqrt (gap (v n))
          )
          atTop
          atTop := by

      rw [← hScaleFun]

      exact
        hScaleTop

    have hOfRealInverseScaleTop :
        Tendsto
          (
            fun n : ℕ =>
              ENNReal.ofReal
                (
                  h3TerminalForcingSecondQInverseSqrtWidthHigherCoefficient
                      δ qRadial
                    /
                  Real.sqrt (gap (v n))
                )
          )
          atTop
          (𝓝 ∞) :=

      ENNReal.tendsto_ofReal_atTop.comp
        hInverseScaleTop

    have hDirectInverse :
        ∀ᶠ n : ℕ in atTop,
          ENNReal.ofReal
              (
                h3TerminalForcingSecondQInverseSqrtWidthHigherCoefficient
                    δ qRadial
                  /
                Real.sqrt (gap (v n))
              )
            ≤
          h3TerminalPhysicalExtendedHigherRadialMomentAt
            hH3 hClass
            (h3TerminalForcingThirdQHigherRadialShift qRadial)
            (τ (v n))
            (hτ (v n)) := by

      filter_upwards [hDirect] with n hn

      rw [← hProfileEq n]

      exact
        hn

    exact
      Or.inr
        (Or.inl
          ⟨
            j,
            qRadial,
            v,
            hMono,
            hTauSub,
            hRateTop,
            hInverseScaleTop,
            hOfRealInverseScaleTop,
            hDirectInverse,
            hHigherTop
          ⟩)

  · obtain
      ⟨
        j,
        qRadial,
        v,
        hMono,
        hTauSub,
        hRateTop,
        hScaleTop,
        _hOfRealScaleTop,
        hDirect,
        hHigherTop
      ⟩ :=
      hFourth

    have hProfileEq :
        ∀ n : ℕ,
          h3TerminalForcingFourthQMoment10RadialSquareHigherScale qRadial
              *
            Real.sqrt
              (
                δ
                  /
                (
                  12
                    *
                  h3TerminalForcingFourthQResolvedHigherRadialRateCoefficient
                    *
                  gap (v n)
                )
              )
            =
          h3TerminalForcingFourthQInverseSqrtWidthHigherCoefficient
              δ qRadial
            /
          Real.sqrt (gap (v n)) := by

      intro n

      exact
        h3TerminalForcingFourthQHigherScale_sqrt_reciprocalWidth_eq_inverseSqrt
          hδ.le
          (hGap (v n))
          qRadial

    have hScaleFun :
        (
          fun n : ℕ =>
            h3TerminalForcingFourthQMoment10RadialSquareHigherScale qRadial
              *
            Real.sqrt
              (
                δ
                  /
                (
                  12
                    *
                  h3TerminalForcingFourthQResolvedHigherRadialRateCoefficient
                    *
                  gap (v n)
                )
              )
        )
          =
        (
          fun n : ℕ =>
            h3TerminalForcingFourthQInverseSqrtWidthHigherCoefficient
                δ qRadial
              /
            Real.sqrt (gap (v n))
        ) := by

      funext n

      exact
        hProfileEq n

    have hInverseScaleTop :
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalForcingFourthQInverseSqrtWidthHigherCoefficient
                  δ qRadial
                /
              Real.sqrt (gap (v n))
          )
          atTop
          atTop := by

      rw [← hScaleFun]

      exact
        hScaleTop

    have hOfRealInverseScaleTop :
        Tendsto
          (
            fun n : ℕ =>
              ENNReal.ofReal
                (
                  h3TerminalForcingFourthQInverseSqrtWidthHigherCoefficient
                      δ qRadial
                    /
                  Real.sqrt (gap (v n))
                )
          )
          atTop
          (𝓝 ∞) :=

      ENNReal.tendsto_ofReal_atTop.comp
        hInverseScaleTop

    have hDirectInverse :
        ∀ᶠ n : ℕ in atTop,
          ENNReal.ofReal
              (
                h3TerminalForcingFourthQInverseSqrtWidthHigherCoefficient
                    δ qRadial
                  /
                Real.sqrt (gap (v n))
              )
            ≤
          h3TerminalPhysicalExtendedHigherRadialMomentAt
            hH3 hClass
            (h3TerminalForcingFourthQHigherRadialShift qRadial)
            (τ (v n))
            (hτ (v n)) := by

      filter_upwards [hDirect] with n hn

      rw [← hProfileEq n]

      exact
        hn

    exact
      Or.inr
        (Or.inr
          ⟨
            j,
            qRadial,
            v,
            hMono,
            hTauSub,
            hRateTop,
            hInverseScaleTop,
            hOfRealInverseScaleTop,
            hDirectInverse,
            hHigherTop
          ⟩)

def H3TerminalPhysicalTopDissipationResolvedCanonicalForcingDivergentInverseSqrtWidthHigherScaleEscapeSubsequenceOf
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
                  H3TerminalResolvedCanonicalForcingDivergentInverseSqrtWidthHigherScaleBranch
                    hH3 hClass τ hτ δ gap

theorem resolvedCanonicalForcingDivergentInverseSqrtWidthHigherScaleEscapeSubsequenceOf_of_widthEscapeSubsequenceOf
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (σ : ℕ → ℝ)
    (hWidth :
      H3TerminalPhysicalTopDissipationResolvedCanonicalForcingDivergentWidthDirectHigherScaleEscapeSubsequenceOf
        hH3 hClass σ) :
    H3TerminalPhysicalTopDissipationResolvedCanonicalForcingDivergentInverseSqrtWidthHigherScaleEscapeSubsequenceOf
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
      H3TerminalResolvedCanonicalForcingDivergentWidthDirectHigherScaleBranch
        hH3 hClass τ hτ δ gap := by

    simpa only [τ, hτ, gap] using
      hBranch

  have hInverseBranch :
      H3TerminalResolvedCanonicalForcingDivergentInverseSqrtWidthHigherScaleBranch
        hH3 hClass τ hτ δ gap :=
    resolvedCanonicalForcingDivergentInverseSqrtWidthHigherScaleBranch_of_widthBranch
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
