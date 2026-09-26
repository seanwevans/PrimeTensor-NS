import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualBoundedExclusiveFactorDichotomy

/-!
# Positive synchronized gap from two distinct native residual clusters

The bounded residual branch is now split exactly into:

* one full canonical native factor; or
* two distinct finite native cluster factors on cofinal refinements.

This file turns the second alternative into a quantitative asymptotic
statement.

If the two cluster factors are `q₁ ≠ q₂`, then the residual logarithms along
their synchronized cofinal refinements converge to the distinct real values

    logValue q₁,  logValue q₂.

Consequently their mutual distance converges to the strictly positive gap

    dist (logValue q₁) (logValue q₂),

and therefore is eventually bounded below by one fixed positive constant.

This provides a concrete PDE target for eliminating the two-cluster branch:
it is enough to prove that every pair of cofinal residual refinements on the
same terminal sequence must have synchronized logarithmic distance tending to
zero.

No such PDE estimate is assumed here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Quantitative two-cluster package -/

/--
Two distinct finite residual cluster factors together with the positive
synchronized logarithmic gap forced between their cofinal refinements.
-/
def H3TerminalNativeComplementHasPositiveClusterGap
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3) : Prop :=
  ∃ q₁ q₂ : MulReal,
    q₁ ≠ q₂
      ∧
    ∃ k₁ k₂ : ℕ → ℕ,
      Tendsto k₁ atTop atTop
        ∧
      Tendsto k₂ atTop atTop
        ∧
      H3TerminalNativeComplementProportionalityFactor
        u p
        (fun j : ℕ => τ (k₁ j))
        (fun j : ℕ => x (k₁ j))
        q₁
        ∧
      H3TerminalNativeComplementProportionalityFactor
        u p
        (fun j : ℕ => τ (k₂ j))
        (fun j : ℕ => x (k₂ j))
        q₂
        ∧
      Tendsto
        (
          fun j : ℕ =>
            dist
              (
                h3TerminalNativeComplementResidualLogSequence
                  u p τ x (k₁ j)
              )
              (
                h3TerminalNativeComplementResidualLogSequence
                  u p τ x (k₂ j)
              )
        )
        atTop
        (
          𝓝
            (
              dist
                (PrimeTensor.Bridge.MulReal.logValue q₁)
                (PrimeTensor.Bridge.MulReal.logValue q₂)
            )
        )
        ∧
      ∃ δ : ℝ,
        0 < δ
          ∧
        ∀ᶠ j : ℕ in atTop,
          δ
            ≤
          dist
            (
              h3TerminalNativeComplementResidualLogSequence
                u p τ x (k₁ j)
            )
            (
              h3TerminalNativeComplementResidualLogSequence
                u p τ x (k₂ j)
            )

/--
Two distinct finite native cluster factors force a positive synchronized
residual-log gap.
-/
theorem nativeComplementHasPositiveClusterGap_of_twoDistinctClusterFactors
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    (hTwo :
      H3TerminalNativeComplementHasTwoDistinctClusterFactors
        u p τ x) :
    H3TerminalNativeComplementHasPositiveClusterGap
      u p τ x := by

  obtain
    ⟨
      q₁,
      q₂,
      hqNe,
      k₁,
      k₂,
      hk₁Top,
      hk₂Top,
      hFactor₁,
      hFactor₂
    ⟩ :=
    hTwo

  have hNative₁ :
      H3TerminalNativeNatConvergesTo
        (
          fun j : ℕ =>
            PrimeTensor.MulReal.ratio
              (
                h3TerminalNativeGradientForPair
                  u p
                  (τ (k₁ j))
                  (x (k₁ j))
              )
              (
                h3TerminalSelectedSignedNativeCurlForPair
                  u p
                  (τ (k₁ j))
                  (x (k₁ j))
              )
        )
        q₁ := by

    exact hFactor₁

  have hNative₂ :
      H3TerminalNativeNatConvergesTo
        (
          fun j : ℕ =>
            PrimeTensor.MulReal.ratio
              (
                h3TerminalNativeGradientForPair
                  u p
                  (τ (k₂ j))
                  (x (k₂ j))
              )
              (
                h3TerminalSelectedSignedNativeCurlForPair
                  u p
                  (τ (k₂ j))
                  (x (k₂ j))
              )
        )
        q₂ := by

    exact hFactor₂

  have hLog₁ :
      Tendsto
        (
          fun j : ℕ =>
            h3TerminalNativeComplementResidualLogSequence
              u p τ x (k₁ j)
        )
        atTop
        (
          𝓝
            (
              PrimeTensor.Bridge.MulReal.logValue q₁
            )
        ) := by

    have h :=
      (
        terminalNativeNatConvergesTo_iff_logValue_tendsto
          (
            fun j : ℕ =>
              PrimeTensor.MulReal.ratio
                (
                  h3TerminalNativeGradientForPair
                    u p
                    (τ (k₁ j))
                    (x (k₁ j))
                )
                (
                  h3TerminalSelectedSignedNativeCurlForPair
                    u p
                    (τ (k₁ j))
                    (x (k₁ j))
                )
          )
          q₁
      ).1 hNative₁

    simpa [
      h3TerminalNativeComplementResidualLogSequence
    ] using h

  have hLog₂ :
      Tendsto
        (
          fun j : ℕ =>
            h3TerminalNativeComplementResidualLogSequence
              u p τ x (k₂ j)
        )
        atTop
        (
          𝓝
            (
              PrimeTensor.Bridge.MulReal.logValue q₂
            )
        ) := by

    have h :=
      (
        terminalNativeNatConvergesTo_iff_logValue_tendsto
          (
            fun j : ℕ =>
              PrimeTensor.MulReal.ratio
                (
                  h3TerminalNativeGradientForPair
                    u p
                    (τ (k₂ j))
                    (x (k₂ j))
                )
                (
                  h3TerminalSelectedSignedNativeCurlForPair
                    u p
                    (τ (k₂ j))
                    (x (k₂ j))
                )
          )
          q₂
      ).1 hNative₂

    simpa [
      h3TerminalNativeComplementResidualLogSequence
    ] using h

  have hDistance :
      Tendsto
        (
          fun j : ℕ =>
            dist
              (
                h3TerminalNativeComplementResidualLogSequence
                  u p τ x (k₁ j)
              )
              (
                h3TerminalNativeComplementResidualLogSequence
                  u p τ x (k₂ j)
              )
        )
        atTop
        (
          𝓝
            (
              dist
                (PrimeTensor.Bridge.MulReal.logValue q₁)
                (PrimeTensor.Bridge.MulReal.logValue q₂)
            )
        ) :=
    hLog₁.dist
      hLog₂

  have hLogNe :
      PrimeTensor.Bridge.MulReal.logValue q₁
        ≠
      PrimeTensor.Bridge.MulReal.logValue q₂ := by

    intro hEq

    apply hqNe

    exact
      PrimeTensor.Bridge.MulReal.logValue_injective
        hEq

  have hGapPos :
      0
        <
      dist
        (PrimeTensor.Bridge.MulReal.logValue q₁)
        (PrimeTensor.Bridge.MulReal.logValue q₂) :=
    dist_pos.mpr
      hLogNe

  let δ : ℝ :=
    dist
      (PrimeTensor.Bridge.MulReal.logValue q₁)
      (PrimeTensor.Bridge.MulReal.logValue q₂)
      / 2

  have hδPos :
      0 < δ := by

    dsimp only [δ]

    exact
      half_pos
        hGapPos

  have hδLtGap :
      δ
        <
      dist
        (PrimeTensor.Bridge.MulReal.logValue q₁)
        (PrimeTensor.Bridge.MulReal.logValue q₂) := by

    dsimp only [δ]

    exact
      half_lt_self
        hGapPos

  have hEventuallyStrict :
      ∀ᶠ j : ℕ in atTop,
        δ
          <
        dist
          (
            h3TerminalNativeComplementResidualLogSequence
              u p τ x (k₁ j)
          )
          (
            h3TerminalNativeComplementResidualLogSequence
              u p τ x (k₂ j)
          ) := by

    exact
      tendsto_const_nhds.eventually_lt
        hDistance
        hδLtGap

  have hEventually :
      ∀ᶠ j : ℕ in atTop,
        δ
          ≤
        dist
          (
            h3TerminalNativeComplementResidualLogSequence
              u p τ x (k₁ j)
          )
          (
            h3TerminalNativeComplementResidualLogSequence
              u p τ x (k₂ j)
          ) :=
    hEventuallyStrict.mono
      (fun _ h => le_of_lt h)

  exact
    ⟨
      q₁,
      q₂,
      hqNe,
      k₁,
      k₂,
      hk₁Top,
      hk₂Top,
      hFactor₁,
      hFactor₂,
      hDistance,
      δ,
      hδPos,
      hEventually
    ⟩

/-! ## Direct complementary-gradient formulation -/

/--
The positive synchronized gap can equivalently be read directly on the
complementary native gradient logarithms.
-/
theorem nativeComplement_twoDistinctClusterFactors_force_eventual_complementLogGap
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    (hTwo :
      H3TerminalNativeComplementHasTwoDistinctClusterFactors
        u p τ x) :
    ∃ k₁ k₂ : ℕ → ℕ,
      Tendsto k₁ atTop atTop
        ∧
      Tendsto k₂ atTop atTop
        ∧
      ∃ δ : ℝ,
        0 < δ
          ∧
        ∀ᶠ j : ℕ in atTop,
          δ
            ≤
          dist
            (
              PrimeTensor.Bridge.MulReal.logValue
                (
                  h3TerminalNativeComplementGradientForPair
                    u p
                    (τ (k₁ j))
                    (x (k₁ j))
                )
            )
            (
              PrimeTensor.Bridge.MulReal.logValue
                (
                  h3TerminalNativeComplementGradientForPair
                    u p
                    (τ (k₂ j))
                    (x (k₂ j))
                )
            ) := by

  obtain
    ⟨
      _q₁,
      _q₂,
      _hqNe,
      k₁,
      k₂,
      hk₁Top,
      hk₂Top,
      _hFactor₁,
      _hFactor₂,
      _hDistance,
      δ,
      hδPos,
      hEventually
    ⟩ :=
    nativeComplementHasPositiveClusterGap_of_twoDistinctClusterFactors
      hTwo

  refine
    ⟨
      k₁,
      k₂,
      hk₁Top,
      hk₂Top,
      δ,
      hδPos,
      ?_
    ⟩

  simpa [
    h3TerminalNativeComplementResidualLogSequence,
    ← h3TerminalNativeComplementGradientForPair_eq_residualRatio
  ] using hEventually

/-! ## Both cluster refinements remain terminal -/

/--
If the original selected times converge to the terminal time, both cofinal
cluster refinements also converge to that same terminal time.
-/
theorem nativeComplement_twoDistinctClusterFactors_refinedTimes_tendsto_terminal
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    {T : ℝ}
    (hTau :
      Tendsto τ atTop (𝓝 T))
    (hTwo :
      H3TerminalNativeComplementHasTwoDistinctClusterFactors
        u p τ x) :
    ∃ k₁ k₂ : ℕ → ℕ,
      Tendsto k₁ atTop atTop
        ∧
      Tendsto k₂ atTop atTop
        ∧
      Tendsto
        (fun j : ℕ => τ (k₁ j))
        atTop
        (𝓝 T)
        ∧
      Tendsto
        (fun j : ℕ => τ (k₂ j))
        atTop
        (𝓝 T) := by

  obtain
    ⟨
      _q₁,
      _q₂,
      _hqNe,
      k₁,
      k₂,
      hk₁Top,
      hk₂Top,
      _hFactor₁,
      _hFactor₂
    ⟩ :=
    hTwo

  exact
    ⟨
      k₁,
      k₂,
      hk₁Top,
      hk₂Top,
      hTau.comp hk₁Top,
      hTau.comp hk₂Top
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
