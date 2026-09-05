import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.First.Frechet.Fresh.Rescaled
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Forcing.Heat.First.Derivative.Endpoint
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Forcing.First.Difference.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Forcing.Inverse.Fourier.Gradient.Difference.Bound
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Assembly

/-!
# Classicalization: first-Fréchet fresh-tail endpoint continuity

The fresh first-Fréchet right quotient has already been rescaled to the fixed
unit interval.  Its pointwise integrand is

    D_a H_{h(1-u)}
      N(W(t+hu), W(t+hu))(x).

Two parameters therefore approach the endpoint simultaneously:

* the heat lag `h(1-u)` tends to zero;
* the selected state time `t+hu` tends to `t`.

The fixed-state zero-lag limit was closed in
`SelectedForcingHeatFirstDerivativeEndpoint`.

This file controls the moving-state term uniformly in the heat lag.  For every
positive lag `τ`, heat contractivity gives

    ‖D_a H_τ(N(W(r),W(r)) - N(W(s),W(s)))‖
      ≤
    C₁ ‖e_a‖
      ∫ ‖ξ‖ ‖N̂(W(r),W(r)) - N̂(W(s),W(s))‖.

Crucially, no `τ⁻¹/²` factor occurs.  The selected forcing difference first
mass already tends to zero as `r → s`, so this bound can be combined with the
fixed-state heat endpoint to prove the joint rescaled-integrand limit.

The upcoming integral checkpoint only has to supply a unit-interval dominator.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelFirstFrechetFreshContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- At a positive heat lag, changing the selected forcing inputs is controlled
by the *unheated* first weighted Fourier mass of the forcing difference.  Heat
contractivity makes the estimate uniform as the lag tends to zero. -/
theorem norm_h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_selectedRestart_sub_le_differenceFirstMass
    {ν A r s τ : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hr : 0 < r)
    (hrR : r ≤ h3FinHeatLerayRestartRadius ν A)
    (hs : 0 < s)
    (hsR : s ≤ h3FinHeatLerayRestartRadius ν A)
    (hτ : 0 < τ)
    (i a : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let ea : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 a)
    ‖h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
          ν τ (W r) (W r) i a x
        -
      h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
          ν τ (W s) (W s) i a x‖
      ≤
    (h3FourierFirstDerivativeL1Coefficient *
      (∫ ξ : H3FourierPoint3,
        ‖ξ‖ *
          ‖h3RawFinLerayOuterProductDivergence
                (W r) (W r) i ξ
              -
            h3RawFinLerayOuterProductDivergence
                (W s) (W s) i ξ‖)) *
      ‖ea‖ := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let ea : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 a)

  let Fr : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence
      (W r) (W r) i

  let Fs : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence
      (W s) (W s) i

  let fr : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergenceHeatRepresentative
      ν τ (W r) (W r) i

  let fs : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergenceHeatRepresentative
      ν τ (W s) (W s) i

  have hFr0 :
      Integrable Fr
        (volume : Measure H3FourierPoint3) := by
    dsimp only [Fr]
    exact
      h3RawFinLerayOuterProductDivergence_integrable
        (W r) (W r) i

  have hFs0 :
      Integrable Fs
        (volume : Measure H3FourierPoint3) := by
    dsimp only [Fs]
    exact
      h3RawFinLerayOuterProductDivergence_integrable
        (W s) (W s) i

  have hFr1 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ * ‖Fr ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [Fr, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_firstMoment_integrable
        hν U₀ hA hU₀ hr hrR i

  have hFs1 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ * ‖Fs ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [Fs, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_firstMoment_integrable
        hν U₀ hA hU₀ hs hsR i

  have hRawDiff0 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          Fr ξ - Fs ξ)
        (volume : Measure H3FourierPoint3) :=
    hFr0.sub hFs0

  have hRawMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ * ‖Fr ξ‖ +
            ‖ξ‖ * ‖Fs ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hFr1.add hFs1

  have hRawDiffMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ * ‖Fr ξ - Fs ξ‖)
        (volume : Measure H3FourierPoint3) :=
    continuous_norm.aestronglyMeasurable.mul
      hRawDiff0.aestronglyMeasurable.norm

  have hRawDiffPoint :
      ∀ ξ : H3FourierPoint3,
        ‖ξ‖ * ‖Fr ξ - Fs ξ‖
          ≤
        ‖ξ‖ * ‖Fr ξ‖ +
          ‖ξ‖ * ‖Fs ξ‖ := by
    intro ξ
    calc
      ‖ξ‖ * ‖Fr ξ - Fs ξ‖
          ≤
        ‖ξ‖ * (‖Fr ξ‖ + ‖Fs ξ‖) :=
      mul_le_mul_of_nonneg_left
        (norm_sub_le (Fr ξ) (Fs ξ))
        (norm_nonneg ξ)
      _ =
        ‖ξ‖ * ‖Fr ξ‖ +
          ‖ξ‖ * ‖Fs ξ‖ := by
        ring

  have hRawDiff1 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ * ‖Fr ξ - Fs ξ‖)
        (volume : Measure H3FourierPoint3) := by
    refine hRawMajor.mono' hRawDiffMeas ?_
    filter_upwards with ξ
    have hLeft0 :
        0 ≤ ‖ξ‖ * ‖Fr ξ - Fs ξ‖ := by
      positivity
    have hRight0 :
        0 ≤
          ‖ξ‖ * ‖Fr ξ‖ +
            ‖ξ‖ * ‖Fs ξ‖ := by
      positivity
    simpa only [
      Real.norm_eq_abs,
      abs_of_nonneg hLeft0,
      abs_of_nonneg hRight0
    ] using hRawDiffPoint ξ

  have hfr0 :
      Integrable fr
        (volume : Measure H3FourierPoint3) := by
    dsimp only [fr]
    exact
      h3RawFinLerayOuterProductDivergenceHeatRepresentative_integrable
        hν hτ (W r) (W r) i

  have hfs0 :
      Integrable fs
        (volume : Measure H3FourierPoint3) := by
    dsimp only [fs]
    exact
      h3RawFinLerayOuterProductDivergenceHeatRepresentative_integrable
        hν hτ (W s) (W s) i

  have hfr1 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ * ‖fr ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [fr]
    simpa using
      (h3RawFinLerayOuterProductDivergenceHeatRepresentative_moment_integrable
        hν hτ (W r) (W r) i 1 (by norm_num))

  have hfs1 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ * ‖fs ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [fs]
    simpa using
      (h3RawFinLerayOuterProductDivergenceHeatRepresentative_moment_integrable
        hν hτ (W s) (W s) i 1 (by norm_num))

  have hHeatDiff0 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          fr ξ - fs ξ)
        (volume : Measure H3FourierPoint3) :=
    hfr0.sub hfs0

  have hHeatDiffMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ * ‖fr ξ - fs ξ‖)
        (volume : Measure H3FourierPoint3) :=
    continuous_norm.aestronglyMeasurable.mul
      hHeatDiff0.aestronglyMeasurable.norm

  have hHeatDiffPoint :
      ∀ ξ : H3FourierPoint3,
        ‖ξ‖ * ‖fr ξ - fs ξ‖
          ≤
        ‖ξ‖ * ‖Fr ξ - Fs ξ‖ := by
    intro ξ

    have hHeat :
        ‖h3HeatFourierSymbol ν τ ξ‖ ≤ 1 :=
      norm_h3HeatFourierSymbol_le_one hν.le hτ.le ξ

    have hEq :
        fr ξ - fs ξ
          =
        h3HeatFourierSymbol ν τ ξ *
          (Fr ξ - Fs ξ) := by
      dsimp only [fr, fs, Fr, Fs]
      unfold
        h3RawFinLerayOuterProductDivergenceHeatRepresentative
      ring

    rw [hEq, norm_mul]

    calc
      ‖ξ‖ *
          (‖h3HeatFourierSymbol ν τ ξ‖ *
            ‖Fr ξ - Fs ξ‖)
          ≤
        ‖ξ‖ *
          (1 * ‖Fr ξ - Fs ξ‖) := by
            exact
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right
                  hHeat
                  (norm_nonneg _))
                (norm_nonneg ξ)
      _ =
        ‖ξ‖ * ‖Fr ξ - Fs ξ‖ := by
          rw [one_mul]

  have hHeatDiff1 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ * ‖fr ξ - fs ξ‖)
        (volume : Measure H3FourierPoint3) := by
    refine hRawDiff1.mono' hHeatDiffMeas ?_
    filter_upwards with ξ
    have hLeft0 :
        0 ≤ ‖ξ‖ * ‖fr ξ - fs ξ‖ := by
      positivity
    have hRight0 :
        0 ≤ ‖ξ‖ * ‖Fr ξ - Fs ξ‖ := by
      positivity
    simpa only [
      Real.norm_eq_abs,
      abs_of_nonneg hLeft0,
      abs_of_nonneg hRight0
    ] using hHeatDiffPoint ξ

  have hMassLe :
      (∫ ξ : H3FourierPoint3,
        ‖ξ‖ * ‖fr ξ - fs ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ * ‖Fr ξ - Fs ξ‖ := by
    exact
      integral_mono_ae
        hHeatDiff1
        hRawDiff1
        (Filter.Eventually.of_forall hHeatDiffPoint)

  have hBase :=
    norm_fderiv_fourierInv_sub_le_firstMass
      fr fs
      hfr0 hfs0
      hfr1 hfs1
      hHeatDiff1
      x

  have hCoeff0 :
      0 ≤ h3FourierFirstDerivativeL1Coefficient :=
    h3FourierFirstDerivativeL1Coefficient_nonneg

  have hBaseRaw :
      ‖fderiv ℝ (FourierTransformInv.fourierInv fr) x -
          fderiv ℝ (FourierTransformInv.fourierInv fs) x‖
        ≤
      h3FourierFirstDerivativeL1Coefficient *
        (∫ ξ : H3FourierPoint3,
          ‖ξ‖ * ‖Fr ξ - Fs ξ‖) :=
    hBase.trans
      (mul_le_mul_of_nonneg_left hMassLe hCoeff0)

  have hRepR :=
    h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRepresentative_eq_fderiv
      hν hτ (W r) (W r) i x

  have hRepS :=
    h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRepresentative_eq_fderiv
      hν hτ (W s) (W s) i x

  have hEval :
      h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
            ν τ (W r) (W r) i a x
          -
        h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
            ν τ (W s) (W s) i a x
        =
      (fderiv ℝ
          (h3RawFinLerayOuterProductDivergenceHeatC3Representative
            ν τ (W r) (W r) i)
          x
        -
        fderiv ℝ
          (h3RawFinLerayOuterProductDivergenceHeatC3Representative
            ν τ (W s) (W s) i)
          x) ea := by
    rw [← hRepR, ← hRepS]
    simp only [sub_apply]
    unfold
      h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRepresentative
    rw [
      h3AssembleCoordinateDerivative_axis,
      h3AssembleCoordinateDerivative_axis
    ]

  have hBaseC3 :
      ‖fderiv ℝ
          (h3RawFinLerayOuterProductDivergenceHeatC3Representative
            ν τ (W r) (W r) i)
          x
        -
        fderiv ℝ
          (h3RawFinLerayOuterProductDivergenceHeatC3Representative
            ν τ (W s) (W s) i)
          x‖
        ≤
      h3FourierFirstDerivativeL1Coefficient *
        (∫ ξ : H3FourierPoint3,
          ‖ξ‖ * ‖Fr ξ - Fs ξ‖) := by
    dsimp only [fr, fs] at hBaseRaw
    unfold
      h3RawFinLerayOuterProductDivergenceHeatC3Representative
    exact hBaseRaw

  rw [hEval]

  have hOp :
      ‖(fderiv ℝ
          (h3RawFinLerayOuterProductDivergenceHeatC3Representative
            ν τ (W r) (W r) i)
          x
        -
        fderiv ℝ
          (h3RawFinLerayOuterProductDivergenceHeatC3Representative
            ν τ (W s) (W s) i)
          x) ea‖
        ≤
      ‖fderiv ℝ
          (h3RawFinLerayOuterProductDivergenceHeatC3Representative
            ν τ (W r) (W r) i)
          x
        -
        fderiv ℝ
          (h3RawFinLerayOuterProductDivergenceHeatC3Representative
            ν τ (W s) (W s) i)
          x‖ * ‖ea‖ := by
    exact
      ContinuousLinearMap.le_opNorm
        (fderiv ℝ
          (h3RawFinLerayOuterProductDivergenceHeatC3Representative
            ν τ (W r) (W r) i)
          x
        -
        fderiv ℝ
          (h3RawFinLerayOuterProductDivergenceHeatC3Representative
            ν τ (W s) (W s) i)
          x)
        ea

  exact
    hOp.trans
      (mul_le_mul_of_nonneg_right
        hBaseC3
        (norm_nonneg ea))

/-- For every interior unit parameter, the rescaled first-Fréchet fresh
integrand tends jointly in vanishing heat lag and moving selected state to the
instantaneous forcing derivative. -/
theorem tendsto_h3RawFinLerayOuterProductDivergenceHeatFreshFirstFrechetRescaledIntegrand_selectedRestart_zero_right
    {ν A t u : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (hu : u ∈ Set.Ioo (0 : ℝ) 1)
    (i a : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    Tendsto
      (fun h : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatFreshFirstFrechetRescaledIntegrand
          ν t h W i a x u)
      (𝓝[Set.Ici (0 : ℝ)] 0)
      (𝓝
        ((fderiv ℝ
            (h3RawFinLerayOuterProductDivergenceC0Representative
              (W t) (W t) i)
            x)
          (h3FourierAxisDirection (h3AxisOfFin3 a)))) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let ea : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 a)

  let E : ℂ :=
    (fderiv ℝ
        (h3RawFinLerayOuterProductDivergenceC0Representative
          (W t) (W t) i)
        x) ea

  let M : ℝ → ℝ :=
    fun r =>
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ *
          ‖h3RawFinLerayOuterProductDivergence
                (W r) (W r) i ξ
              -
            h3RawFinLerayOuterProductDivergence
                (W t) (W t) i ξ‖

  let T : ℝ → ℂ :=
    fun h =>
      h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
        ν (h * (1 - u)) (W t) (W t) i a x

  let g : ℝ → ℝ :=
    fun h =>
      (h3FourierFirstDerivativeL1Coefficient * M (t + h * u)) *
          ‖ea‖
        +
      ‖T h - E‖

  have hhZero :
      Tendsto
        (fun h : ℝ => h)
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds

  have hArg :
      Tendsto
        (fun h : ℝ => t + h * u)
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝 t) := by
    simpa only [zero_mul, add_zero] using
      tendsto_const_nhds.add (hhZero.mul_const u)

  have hMassBase :
      Tendsto
        M
        (𝓝 t)
        (𝓝 0) := by
    dsimp only [M, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_differenceFirstMass_tendsto_zero
        hν U₀ hA hU₀ ht htR i

  have hMass :
      Tendsto
        (fun h : ℝ => M (t + h * u))
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝 0) :=
    hMassBase.comp hArg

  have hCoeff :
      Tendsto
        (fun _h : ℝ =>
          h3FourierFirstDerivativeL1Coefficient)
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝 h3FourierFirstDerivativeL1Coefficient) :=
    tendsto_const_nhds

  have hEa :
      Tendsto
        (fun _h : ℝ => ‖ea‖)
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝 ‖ea‖) :=
    tendsto_const_nhds

  have hMovingUpperTend :
      Tendsto
        (fun h : ℝ =>
          (h3FourierFirstDerivativeL1Coefficient *
            M (t + h * u)) * ‖ea‖)
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝 0) := by
    simpa using ((hCoeff.mul hMass).mul hEa)

  have hLagFull :
      Tendsto
        (fun h : ℝ => h * (1 - u))
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝 0) := by
    simpa only [zero_mul] using
      hhZero.mul_const (1 - u)

  have hOneMinus :
      0 ≤ 1 - u := by
    linarith [hu.2]

  have hLagMaps :
      MapsTo
        (fun h : ℝ => h * (1 - u))
        (Set.Ici (0 : ℝ))
        (Set.Ici (0 : ℝ)) := by
    intro h hh
    exact mul_nonneg hh hOneMinus

  have hLag :
      Tendsto
        (fun h : ℝ => h * (1 - u))
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝[Set.Ici (0 : ℝ)] 0) := by
    exact
      tendsto_inf.2
        ⟨hLagFull,
          tendsto_principal.2 <|
            mem_inf_of_right <|
              mem_principal.2 hLagMaps⟩

  have hFrozen :
      Tendsto
        T
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝 E) := by
    have h0 :=
      (tendsto_h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_selectedRestart_zero_right
        hν U₀ hA hU₀ ht htR.le i a x).comp hLag
    dsimp only [T, E, W, ea]
    exact h0

  have hFrozenDiff :
      Tendsto
        (fun h : ℝ => ‖T h - E‖)
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝 0) := by
    have hEConst :
        Tendsto
          (fun _h : ℝ => E)
          (𝓝[Set.Ici (0 : ℝ)] 0)
          (𝓝 E) :=
      tendsto_const_nhds
    simpa using (hFrozen.sub hEConst).norm

  have hgZero :
      Tendsto
        g
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝 0) := by
    dsimp only [g]
    simpa only [zero_add] using
      hMovingUpperTend.add hFrozenDiff

  have hInterior :
      Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν A)
        ∈ 𝓝 t :=
    Ioo_mem_nhds ht htR

  have hArgInterior :
      ∀ᶠ h : ℝ in (𝓝[Set.Ici (0 : ℝ)] 0),
        t + h * u ∈
          Set.Ioo
            (0 : ℝ)
            (h3FinHeatLerayRestartRadius ν A) :=
    hArg.eventually hInterior

  have hUpper :
      ∀ᶠ h : ℝ in (𝓝[Set.Ici (0 : ℝ)] 0),
        ‖h3RawFinLerayOuterProductDivergenceHeatFreshFirstFrechetRescaledIntegrand
              ν t h W i a x u
            -
          E‖
          ≤
        g h := by
    filter_upwards
      [self_mem_nhdsWithin, hArgInterior]
      with h hh hri

    by_cases hh0 : h = 0

    · subst h
      dsimp only [g, T, E, M]
      unfold
        h3RawFinLerayOuterProductDivergenceHeatFreshFirstFrechetRescaledIntegrand
      rw [
        h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRetardedPath_axis
      ]
      unfold
        h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
      simp only [zero_mul, add_zero, sub_self, norm_zero, zero_add]
      rw [
        h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_zero_eq_selectedRestart_fderiv_apply
          hν U₀ hA hU₀ ht htR.le i a x
      ]
      dsimp only [W, ea]
      simp

    · have hhpos :
          0 < h :=
        lt_of_le_of_ne hh (Ne.symm hh0)

      have hu1 :
          0 < 1 - u := by
        linarith [hu.2]

      have hlag :
          0 < h * (1 - u) :=
        mul_pos hhpos hu1

      have hLagEq :
          (t + h) - (t + h * u)
            =
          h * (1 - u) := by
        ring

      let R : ℂ :=
        h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
          ν (h * (1 - u))
          (W (t + h * u))
          (W (t + h * u))
          i a x

      have hFreshEq :
          h3RawFinLerayOuterProductDivergenceHeatFreshFirstFrechetRescaledIntegrand
              ν t h W i a x u
            =
          R := by
        rw [
          h3RawFinLerayOuterProductDivergenceHeatFreshFirstFrechetRescaledIntegrand_eq_firstDerivativeRetardedPath
        ]
        unfold
          h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
        rw [hLagEq]

      have hMove :
          ‖R - T h‖
            ≤
          (h3FourierFirstDerivativeL1Coefficient *
            M (t + h * u)) * ‖ea‖ := by
        dsimp only [R, T, M, ea, W]
        exact
          norm_h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_selectedRestart_sub_le_differenceFirstMass
            hν U₀ hA hU₀
            hri.1 hri.2.le
            ht htR.le
            hlag
            i a x

      rw [hFreshEq]

      have hSplit :
          R - E
            =
          (R - T h) + (T h - E) := by
        abel

      rw [hSplit]

      calc
        ‖(R - T h) + (T h - E)‖
            ≤
          ‖R - T h‖ + ‖T h - E‖ :=
          norm_add_le _ _
        _ ≤
          (h3FourierFirstDerivativeL1Coefficient *
              M (t + h * u)) * ‖ea‖
            +
          ‖T h - E‖ :=
          add_le_add hMove (le_refl _)
        _ = g h := by
          rfl

  have hNonneg :
      ∀ᶠ h : ℝ in (𝓝[Set.Ici (0 : ℝ)] 0),
        0 ≤
          ‖h3RawFinLerayOuterProductDivergenceHeatFreshFirstFrechetRescaledIntegrand
              ν t h W i a x u
            -
          E‖ :=
    Eventually.of_forall
      (fun h => norm_nonneg _)

  have hToE :
      Tendsto
        (h3RawFinLerayOuterProductDivergenceHeatFreshFirstFrechetRescaledIntegrand
          ν t · W i a x u)
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝 E) := by
    exact
      (tendsto_iff_norm_sub_tendsto_zero).2
        (squeeze_zero'
          hNonneg
          hUpper
          hgZero)

  dsimp only [E, ea, W] at hToE
  exact hToE

end

end Euclidean
end Bridge
end PrimeTensor
