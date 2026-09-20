import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Second.Frechet.Fresh.Rescaled
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Forcing.Heat.Second.Derivative.Endpoint
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Forcing.Second.Difference.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.Second.Coordinate.State.Continuity

/-!
# Classicalization: second-Fréchet fresh-tail endpoint continuity

The fresh second-Fréchet quotient has been rescaled to the fixed unit interval.
For one ordered coordinate pair `(a,b)` its integrand is

    D_a D_b H_{h(1-u)}
      N(W(t+hu), W(t+hu))(x).

As `h ↓ 0`, both the heat lag and the selected source state move.  The two
pieces are now available separately:

* `Selected.Forcing.Heat.Second.Derivative.Endpoint` closes the fixed-state
  zero-lag second-coordinate limit;
* `Selected.Forcing.Second.Difference.Continuity` shows that the unheated
  forcing difference tends to zero in its second weighted raw Fourier mass.

The only missing bridge is a heat-contractive state-variation bound.  Two
coordinate derivative symbols cost `(2π)^2 |ξ|^2`, while the heat multiplier
has norm at most one, hence

    |D_a D_b H_τ(N(U,U)-N(V,V))(x)|
      ≤ (2π)^2 ∫ |ξ|^2 |N̂(U,U)-N̂(V,V)|.

This estimate is uniform as `τ ↓ 0`, unlike the older positive-lag state
continuity estimate that pays an inverse heat scale.

Combining the uniform moving-state bound with the frozen zero-lag endpoint
gives the joint fresh-integrand limit needed before integrating over `u`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelSecondFrechetFreshContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- At positive heat lag, changing the two selected forcing inputs is
controlled by the *unheated* second weighted Fourier mass of their forcing
difference.  Heat contractivity makes this uniform at zero lag. -/
theorem norm_h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative_selectedRestart_sub_le_differenceSecondMass
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
    (i a b : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ‖h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
          ν τ (W r) (W r) i a b x
        -
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
          ν τ (W s) (W s) i a b x‖
      ≤
    (2 * Real.pi) ^ 2 *
      (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3RawFinLerayOuterProductDivergence
                (W r) (W r) i ξ
              -
            h3RawFinLerayOuterProductDivergence
                (W s) (W s) i ξ‖) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let Fr : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence
      (W r) (W r) i

  let Fs : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence
      (W s) (W s) i

  let KU : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel
      ν τ (W r) (W r) i a b x

  let KV : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel
      ν τ (W s) (W s) i a b x

  let R : H3FourierPoint3 → ℝ :=
    fun ξ =>
      ‖ξ‖ ^ 2 * ‖Fr ξ - Fs ξ‖

  have hFr2 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 * ‖Fr ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [Fr, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_secondMoment_integrable
        hν U₀ hA hU₀ hr hrR i

  have hFs2 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 * ‖Fs ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [Fs, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_secondMoment_integrable
        hν U₀ hA hU₀ hs hsR i

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

  have hRawDiff0 :
      Integrable
        (fun ξ : H3FourierPoint3 => Fr ξ - Fs ξ)
        (volume : Measure H3FourierPoint3) :=
    hFr0.sub hFs0

  have hRawMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 * ‖Fr ξ‖ +
            ‖ξ‖ ^ 2 * ‖Fs ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hFr2.add hFs2

  have hRawDiffMeas :
      AEStronglyMeasurable R
        (volume : Measure H3FourierPoint3) := by
    dsimp only [R]
    exact
      (continuous_norm.pow 2).aestronglyMeasurable.mul
        hRawDiff0.aestronglyMeasurable.norm

  have hRawDiffPoint :
      ∀ ξ : H3FourierPoint3,
        R ξ
          ≤
        ‖ξ‖ ^ 2 * ‖Fr ξ‖ +
          ‖ξ‖ ^ 2 * ‖Fs ξ‖ := by
    intro ξ
    dsimp only [R]
    calc
      ‖ξ‖ ^ 2 * ‖Fr ξ - Fs ξ‖
          ≤
        ‖ξ‖ ^ 2 * (‖Fr ξ‖ + ‖Fs ξ‖) :=
      mul_le_mul_of_nonneg_left
        (norm_sub_le (Fr ξ) (Fs ξ))
        (by positivity)
      _ =
        ‖ξ‖ ^ 2 * ‖Fr ξ‖ +
          ‖ξ‖ ^ 2 * ‖Fs ξ‖ := by
        ring

  have hR :
      Integrable R
        (volume : Measure H3FourierPoint3) := by
    refine hRawMajor.mono' hRawDiffMeas ?_
    filter_upwards with ξ
    have hLeft0 : 0 ≤ R ξ := by
      dsimp only [R]
      positivity
    have hRight0 :
        0 ≤
          ‖ξ‖ ^ 2 * ‖Fr ξ‖ +
            ‖ξ‖ ^ 2 * ‖Fs ξ‖ := by
      positivity
    simpa only [
      Real.norm_eq_abs,
      abs_of_nonneg hLeft0,
      abs_of_nonneg hRight0
    ] using hRawDiffPoint ξ

  have hKU :
      Integrable KU
        (volume : Measure H3FourierPoint3) := by
    dsimp only [KU]
    exact
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel_integrable
        hν hτ (W r) (W r) i a b x

  have hKV :
      Integrable KV
        (volume : Measure H3FourierPoint3) := by
    dsimp only [KV]
    exact
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel_integrable
        hν hτ (W s) (W s) i a b x

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (2 * Real.pi) ^ 2 * R ξ)
        (volume : Measure H3FourierPoint3) :=
    hR.const_mul ((2 * Real.pi) ^ 2)

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        ‖KU ξ - KV ξ‖
          ≤
        (2 * Real.pi) ^ 2 * R ξ := by
    intro ξ
    dsimp only [KU, KV, R, Fr, Fs]
    unfold
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel
    rw [← smul_sub]
    simp only [Circle.norm_smul]
    unfold
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude
      h3RawFinLerayOuterProductDivergenceHeatRepresentative

    have hAlg :
        h3FourierDerivativeSymbol a ξ *
              (h3FourierDerivativeSymbol b ξ *
                (h3HeatFourierSymbol ν τ ξ *
                  h3RawFinLerayOuterProductDivergence (W r) (W r) i ξ))
            -
            h3FourierDerivativeSymbol a ξ *
              (h3FourierDerivativeSymbol b ξ *
                (h3HeatFourierSymbol ν τ ξ *
                  h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ))
          =
        h3FourierDerivativeSymbol a ξ *
          (h3FourierDerivativeSymbol b ξ *
            (h3HeatFourierSymbol ν τ ξ *
              (h3RawFinLerayOuterProductDivergence (W r) (W r) i ξ -
                h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ))) := by
      ring

    rw [hAlg, norm_mul, norm_mul, norm_mul]

    have ha :=
      norm_h3FourierDerivativeSymbol_le_gradientMagnitude a ξ

    have hb :=
      norm_h3FourierDerivativeSymbol_le_gradientMagnitude b ξ

    have hHeat :
        ‖h3HeatFourierSymbol ν τ ξ‖ ≤ 1 :=
      norm_h3HeatFourierSymbol_le_one hν.le hτ.le ξ

    have hRaw0 :
        0 ≤
          ‖h3RawFinLerayOuterProductDivergence (W r) (W r) i ξ -
            h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ‖ :=
      norm_nonneg _

    calc
      ‖h3FourierDerivativeSymbol a ξ‖ *
          (‖h3FourierDerivativeSymbol b ξ‖ *
            (‖h3HeatFourierSymbol ν τ ξ‖ *
              ‖h3RawFinLerayOuterProductDivergence (W r) (W r) i ξ -
                h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ‖))
          ≤
        h3FourierGradientMagnitude ξ *
          (‖h3FourierDerivativeSymbol b ξ‖ *
            (‖h3HeatFourierSymbol ν τ ξ‖ *
              ‖h3RawFinLerayOuterProductDivergence (W r) (W r) i ξ -
                h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ‖)) := by
        exact
          mul_le_mul_of_nonneg_right
            ha
            (mul_nonneg
              (norm_nonneg _)
              (mul_nonneg (norm_nonneg _) hRaw0))
      _ ≤
        h3FourierGradientMagnitude ξ *
          (h3FourierGradientMagnitude ξ *
            (‖h3HeatFourierSymbol ν τ ξ‖ *
              ‖h3RawFinLerayOuterProductDivergence (W r) (W r) i ξ -
                h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ‖)) := by
        exact
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right
              hb
              (mul_nonneg (norm_nonneg _) hRaw0))
            (by
              unfold h3FourierGradientMagnitude
              positivity)
      _ ≤
        h3FourierGradientMagnitude ξ *
          (h3FourierGradientMagnitude ξ *
            (1 *
              ‖h3RawFinLerayOuterProductDivergence (W r) (W r) i ξ -
                h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ‖)) := by
        exact
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right
                hHeat hRaw0)
              (by
                unfold h3FourierGradientMagnitude
                positivity))
            (by
              unfold h3FourierGradientMagnitude
              positivity)
      _ =
        (2 * Real.pi) ^ 2 *
          (‖ξ‖ ^ 2 *
            ‖h3RawFinLerayOuterProductDivergence (W r) (W r) i ξ -
              h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ‖) := by
        unfold h3FourierGradientMagnitude
        ring

  rw [
    h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative_eq_integral_kernel,
    h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative_eq_integral_kernel
  ]

  calc
    ‖(∫ ξ : H3FourierPoint3, KU ξ) -
        ∫ ξ : H3FourierPoint3, KV ξ‖
        =
      ‖∫ ξ : H3FourierPoint3, KU ξ - KV ξ‖ := by
        rw [integral_sub hKU hKV]
    _ ≤
      ∫ ξ : H3FourierPoint3, ‖KU ξ - KV ξ‖ :=
        norm_integral_le_integral_norm _
    _ ≤
      ∫ ξ : H3FourierPoint3, (2 * Real.pi) ^ 2 * R ξ := by
        refine integral_mono_ae (hKU.sub hKV).norm hMajor ?_
        exact Filter.Eventually.of_forall hPoint
    _ =
      (2 * Real.pi) ^ 2 *
        (∫ ξ : H3FourierPoint3, R ξ) := by
        rw [integral_const_mul]
    _ =
      (2 * Real.pi) ^ 2 *
        (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 *
            ‖h3RawFinLerayOuterProductDivergence (W r) (W r) i ξ -
              h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ‖) := by
        rfl

/-- For every interior unit parameter, the rescaled second-Fréchet fresh
integrand tends jointly in vanishing heat lag and moving selected state to the
instantaneous forcing Hessian coordinate. -/
theorem tendsto_h3RawFinLerayOuterProductDivergenceHeatFreshSecondFrechetRescaledIntegrand_selectedRestart_zero_right
    {ν A t u : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (hu : u ∈ Set.Ioo (0 : ℝ) 1)
    (i a b : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    Tendsto
      (fun h : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatFreshSecondFrechetRescaledIntegrand
          ν t h W i a b x u)
      (𝓝[Set.Ici (0 : ℝ)] 0)
      (𝓝
        (iteratedFDeriv ℝ 2
          (h3RawFinLerayOuterProductDivergenceC0Representative
            (W t) (W t) i)
          x
          ![
            h3FourierAxisDirection (h3AxisOfFin3 a),
            h3FourierAxisDirection (h3AxisOfFin3 b)
          ])) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let E : ℂ :=
    iteratedFDeriv ℝ 2
      (h3RawFinLerayOuterProductDivergenceC0Representative
        (W t) (W t) i)
      x
      ![
        h3FourierAxisDirection (h3AxisOfFin3 a),
        h3FourierAxisDirection (h3AxisOfFin3 b)
      ]

  let M : ℝ → ℝ :=
    fun r =>
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3RawFinLerayOuterProductDivergence
                (W r) (W r) i ξ
              -
            h3RawFinLerayOuterProductDivergence
                (W t) (W t) i ξ‖

  let T : ℝ → ℂ :=
    fun h =>
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
        ν (h * (1 - u)) (W t) (W t) i a b x

  let g : ℝ → ℝ :=
    fun h =>
      (2 * Real.pi) ^ 2 * M (t + h * u)
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
      Tendsto M (𝓝 t) (𝓝 0) := by
    dsimp only [M, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_differenceSecondMass_tendsto_zero
        hν U₀ hA hU₀ ht htR i

  have hMass :
      Tendsto
        (fun h : ℝ => M (t + h * u))
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝 0) :=
    hMassBase.comp hArg

  have hCoeff :
      Tendsto
        (fun _h : ℝ => ((2 * Real.pi) ^ 2 : ℝ))
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝 ((2 * Real.pi) ^ 2)) :=
    tendsto_const_nhds

  have hMovingUpperTend :
      Tendsto
        (fun h : ℝ =>
          (2 * Real.pi) ^ 2 * M (t + h * u))
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝 0) := by
    simpa only [mul_zero] using hCoeff.mul hMass

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
      (tendsto_h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative_selectedRestart_zero_right
        hν U₀ hA hU₀ ht htR.le i a b x).comp hLag
    dsimp only [T, E, W]
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
        ‖h3RawFinLerayOuterProductDivergenceHeatFreshSecondFrechetRescaledIntegrand
              ν t h W i a b x u
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
      rw [
        h3RawFinLerayOuterProductDivergenceHeatFreshSecondFrechetRescaledIntegrand_eq_secondCoordinateRetardedPath
      ]
      unfold
        h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
      simp only [zero_mul, add_zero, sub_self, norm_zero, zero_add]
      rw [
        h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative_zero_eq_selectedRestart_iteratedFDeriv
          hν U₀ hA hU₀ ht htR.le i a b x
      ]
      dsimp only [W]
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

      let R0 : ℂ :=
        h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
          ν (h * (1 - u))
          (W (t + h * u))
          (W (t + h * u))
          i a b x

      have hFreshEq :
          h3RawFinLerayOuterProductDivergenceHeatFreshSecondFrechetRescaledIntegrand
              ν t h W i a b x u
            =
          R0 := by
        rw [
          h3RawFinLerayOuterProductDivergenceHeatFreshSecondFrechetRescaledIntegrand_eq_secondCoordinateRetardedPath
        ]
        unfold
          h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
        rw [hLagEq]

      have hMove :
          ‖R0 - T h‖
            ≤
          (2 * Real.pi) ^ 2 *
            M (t + h * u) := by
        dsimp only [R0, T, M, W]
        exact
          norm_h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative_selectedRestart_sub_le_differenceSecondMass
            hν U₀ hA hU₀
            hri.1 hri.2.le
            ht htR.le
            hlag
            i a b x

      rw [hFreshEq]

      have hSplit :
          R0 - E
            =
          (R0 - T h) + (T h - E) := by
        abel

      rw [hSplit]

      calc
        ‖(R0 - T h) + (T h - E)‖
            ≤
          ‖R0 - T h‖ + ‖T h - E‖ :=
          norm_add_le _ _
        _ ≤
          (2 * Real.pi) ^ 2 *
              M (t + h * u)
            +
          ‖T h - E‖ :=
          add_le_add hMove (le_refl _)
        _ = g h := by
          rfl

  have hNonneg :
      ∀ᶠ h : ℝ in (𝓝[Set.Ici (0 : ℝ)] 0),
        0 ≤
          ‖h3RawFinLerayOuterProductDivergenceHeatFreshSecondFrechetRescaledIntegrand
              ν t h W i a b x u
            -
          E‖ :=
    Eventually.of_forall
      (fun h => norm_nonneg _)

  have hToE :
      Tendsto
        (h3RawFinLerayOuterProductDivergenceHeatFreshSecondFrechetRescaledIntegrand
          ν t · W i a b x u)
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝 E) := by
    exact
      (tendsto_iff_norm_sub_tendsto_zero).2
        (squeeze_zero'
          hNonneg
          hUpper
          hgZero)

  dsimp only [E, W] at hToE
  exact hToE

end

end Euclidean
end Bridge
end PrimeTensor
