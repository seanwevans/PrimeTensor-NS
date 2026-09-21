import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Third.Frechet.Fresh.Quotient
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Third.Frechet.Cocycle
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Second.Frechet.Fresh.Spectral.Quotient
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Sixth.Endpoint.Uniform.Third.Forcing.Envelope
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Classicalization: spectral third-Fréchet fresh quotient

The literal normalized third-coordinate fresh tail is already closed.  The
right-quotient split, however, contains the third Fréchet derivative of the
actual shifted spectral H³ Duhamel state.

We identify the two objects by differentiating the already-compiled fresh
Hessian identity one further spatial time.

The new analytic input is simpler than the historical third-endpoint branch.
On a short positive source interval `[t,t+h]`, the sixth-endpoint stack already
provides one interval-uniform cubic forcing mass.  Three coordinate symbols
therefore give a constant integrable source-time dominator.  This lets us move
the third spatial derivative through the short source integral directly.

Thus

    D³ Fresh_h(x)[e_a,e_b,e_c]
      =
    ∫ₜ^{t+h} D_a D_b D_c H_{t+h-s} N(W(s),W(s))(x) ds,

and the normalized spectral fresh quotient inherits the literal limit already
proved in `Fresh.Quotient`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelThirdFrechetFreshSpectralQuotient
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- Along an affine `l`-coordinate line, the derivative of the mixed
second-coordinate Fourier kernel is the ordered third-coordinate Fourier
kernel. -/
theorem hasDerivAt_h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel_thirdCoordinate
    (ν τ : ℝ)
    (U V : H3SpectralFinVectorState)
    (i j k l : Fin 3)
    (x ξ : H3FourierPoint3)
    (r : ℝ) :
    HasDerivAt
      (fun q : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel
          ν τ U V i j k
          (x + q • h3FourierAxisDirection (h3AxisOfFin3 l)) ξ)
      (h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateFourierKernel
        ν τ U V i j k l
        (x + r • h3FourierAxisDirection (h3AxisOfFin3 l)) ξ)
      r := by
  let e : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 l)

  have hSmul :
      HasDerivAt (fun q : ℝ => q • e) e r := by
    simpa using (hasDerivAt_id r).smul_const e

  have hLine :
      HasDerivAt (fun q : ℝ => x + q • e) e r :=
    HasDerivAt.const_add x hSmul

  have hInner :
      HasDerivAt
        (fun q : ℝ => inner ℝ ξ (x + q • e))
        (inner ℝ ξ e)
        r := by
    change
      HasDerivAt
        (((innerSL ℝ) ξ) ∘ fun q : ℝ => x + q • e)
        (((innerSL ℝ) ξ) e)
        r
    exact
      (ContinuousLinearMap.hasFDerivAt ((innerSL ℝ) ξ)).comp_hasDerivAt r hLine

  have hRealPhaseArg :
      HasDerivAt
        (fun q : ℝ => (2 * Real.pi) * inner ℝ ξ (x + q • e))
        ((2 * Real.pi) * inner ℝ ξ e)
        r :=
    HasDerivAt.const_mul (2 * Real.pi) hInner

  have hComplexPhaseArg :
      HasDerivAt
        (fun q : ℝ =>
          ((2 * Real.pi) * inner ℝ ξ (x + q • e)) • (Complex.I : ℂ))
        (((2 * Real.pi) * inner ℝ ξ e) • (Complex.I : ℂ))
        r :=
    hRealPhaseArg.smul_const (Complex.I : ℂ)

  have hPhaseExp := hComplexPhaseArg.cexp

  let A : ℂ :=
    h3FourierDerivativeSymbol j ξ *
      (h3FourierDerivativeSymbol k ξ *
        h3RawFinLerayOuterProductDivergenceHeatRepresentative
          ν τ U V i ξ)

  have hProductExp := hPhaseExp.mul_const A

  have hl :
      (((2 * Real.pi) * inner ℝ ξ e) • (Complex.I : ℂ))
        =
      h3FourierDerivativeSymbol l ξ := by
    rw [h3FourierDerivativeSymbol_eq_inner]
    dsimp [e]
    push_cast
    ring

  have hDerivativeEq :
      ((Complex.exp
          (((2 * Real.pi) * inner ℝ ξ (x + r • e)) • (Complex.I : ℂ)) *
        (((2 * Real.pi) * inner ℝ ξ e) • (Complex.I : ℂ))) * A)
        =
      Complex.exp
          (((2 * Real.pi) * inner ℝ ξ (x + r • e)) • (Complex.I : ℂ)) *
        h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude
          ν τ U V i j k l ξ := by
    rw [hl]
    dsimp only [A]
    unfold h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude
    ring

  rw [hDerivativeEq] at hProductExp

  have hKernelEq (q : ℝ) :
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel
          ν τ U V i j k (x + q • e) ξ
        =
      Complex.exp
          (((2 * Real.pi) * inner ℝ ξ (x + q • e)) • (Complex.I : ℂ)) * A := by
    unfold h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel
    unfold h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude
    dsimp only [A]
    simp only [
      Circle.smul_def,
      Real.fourierChar_apply,
      inner_neg_right,
      neg_neg,
      Complex.real_smul,
      smul_eq_mul
    ]

  have hDerivativeKernelEq :
      h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateFourierKernel
          ν τ U V i j k l (x + r • e) ξ
        =
      Complex.exp
          (((2 * Real.pi) * inner ℝ ξ (x + r • e)) • (Complex.I : ℂ)) *
        h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude
          ν τ U V i j k l ξ := by
    unfold h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateFourierKernel
    simp only [
      Circle.smul_def,
      Real.fourierChar_apply,
      inner_neg_right,
      neg_neg,
      Complex.real_smul,
      smul_eq_mul
    ]

  simpa only [e, hKernelEq, hDerivativeKernelEq] using hProductExp

/-- At positive heat lag, differentiating an ordered mixed second-coordinate
representative in one further canonical direction gives the corresponding
third-coordinate representative. -/
theorem h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative_hasDerivAt_thirdCoordinate
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i j k l : Fin 3)
    (x : H3FourierPoint3) :
    HasDerivAt
      (fun r : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
          ν τ U V i j k
          (x + r • h3FourierAxisDirection (h3AxisOfFin3 l)))
      (h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative
        ν τ U V i j k l x)
      0 := by
  let e : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 l)

  let F : ℝ → H3FourierPoint3 → ℂ :=
    fun r ξ =>
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel
        ν τ U V i j k (x + r • e) ξ

  let F' : ℝ → H3FourierPoint3 → ℂ :=
    fun r ξ =>
      h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateFourierKernel
        ν τ U V i j k l (x + r • e) ξ

  let bound : H3FourierPoint3 → ℝ :=
    fun ξ =>
      ‖h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude
        ν τ U V i j k l ξ‖

  have hFInt :
      ∀ r : ℝ,
        Integrable (F r) (volume : Measure H3FourierPoint3) := by
    intro r
    dsimp only [F]
    exact
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel_integrable
        hν hτ U V i j k (x + r • e)

  have hFMeas :
      ∀ᶠ r : ℝ in 𝓝 0,
        AEStronglyMeasurable
          (F r)
          (volume : Measure H3FourierPoint3) :=
    Filter.Eventually.of_forall fun r =>
      (hFInt r).aestronglyMeasurable

  have hF0Int :
      Integrable (F 0) (volume : Measure H3FourierPoint3) :=
    hFInt 0

  have hHeat3 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 *
            ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
              ν τ U V i ξ‖)
        (volume : Measure H3FourierPoint3) := by
    exact
      h3RawFinLerayOuterProductDivergenceHeatRepresentative_moment_integrable
        hν hτ U V i 3 (by norm_num)

  have hAmpMeas :
      AEStronglyMeasurable
        (h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude
          ν τ U V i j k l)
        (volume : Measure H3FourierPoint3) := by
    unfold h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude
    exact
      (h3FourierDerivativeSymbol_continuous j).aestronglyMeasurable.mul
        ((h3FourierDerivativeSymbol_continuous k).aestronglyMeasurable.mul
          ((h3FourierDerivativeSymbol_continuous l).aestronglyMeasurable.mul
            (h3RawFinLerayOuterProductDivergenceHeatRepresentative_aestronglyMeasurable
              ν τ U V i)))

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (2 * Real.pi) ^ 3 *
            (‖ξ‖ ^ 3 *
              ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
                ν τ U V i ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hHeat3.const_mul ((2 * Real.pi) ^ 3)

  have hAmpInt :
      Integrable
        (h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude
          ν τ U V i j k l)
        (volume : Measure H3FourierPoint3) := by
    refine hMajor.mono' hAmpMeas ?_
    filter_upwards with ξ
    exact
      norm_h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude_le_thirdMoment
        ν τ U V i j k l ξ

  have hF'0Int :
      Integrable (F' 0) (volume : Measure H3FourierPoint3) := by
    dsimp only [F']
    unfold h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateFourierKernel
    rw [Real.fourierIntegral_convergent_iff (-(x + 0 • e))]
    exact hAmpInt

  have hF'0Meas :
      AEStronglyMeasurable
        (F' 0)
        (volume : Measure H3FourierPoint3) :=
    hF'0Int.aestronglyMeasurable

  have hBoundInt :
      Integrable bound
        (volume : Measure H3FourierPoint3) := by
    dsimp only [bound]
    exact hAmpInt.norm

  have hBound :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        ∀ r ∈ (Set.univ : Set ℝ),
          ‖F' r ξ‖ ≤ bound ξ := by
    filter_upwards with ξ
    intro r hr
    dsimp only [F', bound]
    unfold h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateFourierKernel
    simp only [Circle.norm_smul]
    exact le_rfl

  have hDiff :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        ∀ r ∈ (Set.univ : Set ℝ),
          HasDerivAt (F · ξ) (F' r ξ) r := by
    filter_upwards with ξ
    intro r hr
    dsimp only [F, F']
    simpa only [e] using
      (hasDerivAt_h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel_thirdCoordinate
        ν τ U V i j k l x ξ r)

  have hIntegral :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (s := (Set.univ : Set ℝ))
      (F := F)
      (F' := F')
      (x₀ := (0 : ℝ))
      (bound := bound)
      (μ := (volume : Measure H3FourierPoint3))
      Filter.univ_mem
      hFMeas
      hF0Int
      hF'0Meas
      hBound
      hBoundInt
      hDiff).2

  simpa only [
    F, F', e,
    zero_smul, add_zero,
    h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative_eq_integral_kernel,
    h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative_eq_integral_kernel
  ] using hIntegral

/-- Translated fixed-lag third-coordinate derivative identity. -/
theorem h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative_hasDerivAt_thirdCoordinate_at
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i j k l : Fin 3)
    (x : H3FourierPoint3)
    (r : ℝ) :
    HasDerivAt
      (fun q : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
          ν τ U V i j k
          (x + q • h3FourierAxisDirection (h3AxisOfFin3 l)))
      (h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative
        ν τ U V i j k l
        (x + r • h3FourierAxisDirection (h3AxisOfFin3 l)))
      r := by
  let e : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 l)

  have h0 :
      HasDerivAt
        (fun q : ℝ =>
          h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
            ν τ U V i j k ((x + r • e) + q • e))
        (h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative
          ν τ U V i j k l (x + r • e))
        0 := by
    simpa only [e] using
      (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative_hasDerivAt_thirdCoordinate
        hν hτ U V i j k l (x + r • e))

  have hShift :
      HasDerivAt (fun q : ℝ => q - r) 1 r := by
    simpa using (hasDerivAt_id r).sub_const r

  have hComp := h0.scomp_of_eq r hShift (by simp)

  have hPoint (q : ℝ) :
      (x + r • e) + (q - r) • e = x + q • e := by
    rw [sub_smul]
    abel

  have hFunEq :
      (fun q : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
          ν τ U V i j k (x + q • e))
        =ᶠ[𝓝 r]
      ((fun q : ℝ =>
          h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
            ν τ U V i j k ((x + r • e) + q • e)) ∘
        fun q : ℝ => q - r) := by
    filter_upwards with q
    simp only [Function.comp_apply]
    rw [hPoint q]

  have hTransport := hComp.congr_of_eventuallyEq hFunEq

  have hDerivEq :
      (1 : ℝ) •
          h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative
            ν τ U V i j k l (x + r • e)
        =
      h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative
        ν τ U V i j k l (x + r • e) :=
    one_smul ℝ _

  have hFinal := hTransport.congr_deriv hDerivEq
  simpa only [e] using hFinal

/-- The ordered third-coordinate representative is invariant under the cyclic
permutation `(a,b,c) ↦ (b,c,a)`. -/
theorem h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative_cycle
    (ν τ : ℝ)
    (U V : H3SpectralFinVectorState)
    (i a b c : Fin 3)
    (x : H3FourierPoint3) :
    h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative
        ν τ U V i b c a x
      =
    h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative
        ν τ U V i a b c x := by
  unfold h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative
  apply congrArg
    (fun F : H3FourierPoint3 → ℂ =>
      FourierTransformInv.fourierInv F x)
  funext ξ
  unfold h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude
  ring

/-- Cyclic symmetry of the ordered third-coordinate representative along the
retarded selected path. -/
theorem h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRetardedPath_cycle
    (ν T : ℝ)
    (U V : ℝ → H3SpectralFinVectorState)
    (i a b c : Fin 3)
    (x : H3FourierPoint3)
    (s : ℝ) :
    h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRetardedPath
        ν T U V i b c a x s
      =
    h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRetardedPath
        ν T U V i a b c x s := by
  unfold h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRetardedPath
  exact
    h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative_cycle
      ν (T - s) (U s) (V s) i a b c x

/-- Every fixed-spatial-point selected third-coordinate retarded path is a.e.
strongly measurable on a positive source interval. -/
theorem h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRetardedPath_selectedRestart_aestronglyMeasurable
    {ν A a T : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i j k l : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    AEStronglyMeasurable
      (h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRetardedPath
        ν T W W i j k l x)
      ((volume : Measure ℝ).restrict (Set.Ioo a T)) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let μs : Measure ℝ :=
    (volume : Measure ℝ).restrict (Set.Ioo a T)

  let phase : H3FourierPoint3 → ℂ :=
    fun ξ =>
      Complex.exp
        (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) *
          Complex.I)

  let K : ℝ × H3FourierPoint3 → ℂ :=
    fun p =>
      phase p.2 *
        h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude
          ν (T - p.1) (W p.1) (W p.1) i j k l p.2

  have hW :
      Continuous W := by
    dsimp only [W]
    exact
      continuous_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀

  have hRaw :
      Measurable
        (fun p : ℝ × H3FourierPoint3 =>
          h3RawFinLerayOuterProductDivergence
            (W p.1) (W p.1) i p.2) :=
    measurable_h3RawFinLerayOuterProductDivergence_continuousPaths_joint
      W W hW hW i

  have hHeat :
      Measurable
        (fun p : ℝ × H3FourierPoint3 =>
          h3HeatFourierSymbol ν (T - p.1) p.2) :=
    (continuous_h3HeatFourierSymbol_retarded ν T).measurable

  have hj :
      Measurable
        (fun p : ℝ × H3FourierPoint3 =>
          h3FourierDerivativeSymbol j p.2) :=
    (h3FourierDerivativeSymbol_continuous j).measurable.comp measurable_snd

  have hk :
      Measurable
        (fun p : ℝ × H3FourierPoint3 =>
          h3FourierDerivativeSymbol k p.2) :=
    (h3FourierDerivativeSymbol_continuous k).measurable.comp measurable_snd

  have hl :
      Measurable
        (fun p : ℝ × H3FourierPoint3 =>
          h3FourierDerivativeSymbol l p.2) :=
    (h3FourierDerivativeSymbol_continuous l).measurable.comp measurable_snd

  have hPhaseCont :
      Continuous phase := by
    dsimp only [phase]
    fun_prop

  have hPhase :
      Measurable
        (fun p : ℝ × H3FourierPoint3 =>
          phase p.2) :=
    hPhaseCont.measurable.comp measurable_snd

  have hAmp :
      Measurable
        (fun p : ℝ × H3FourierPoint3 =>
          h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude
            ν (T - p.1) (W p.1) (W p.1) i j k l p.2) := by
    unfold h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude
    unfold h3RawFinLerayOuterProductDivergenceHeatRepresentative
    exact
      hj.mul
        (hk.mul
          (hl.mul
            (hHeat.mul hRaw)))

  have hK :
      AEStronglyMeasurable
        K
        (μs.prod (volume : Measure H3FourierPoint3)) := by
    have hKMeas : Measurable K := by
      dsimp only [K]
      exact hPhase.mul hAmp
    exact hKMeas.aestronglyMeasurable

  have hOuter :
      AEStronglyMeasurable
        (fun s : ℝ =>
          ∫ ξ : H3FourierPoint3, K (s, ξ))
        μs :=
    hK.integral_prod_right'

  have hEq :
      (fun s : ℝ =>
        ∫ ξ : H3FourierPoint3, K (s, ξ))
        =
      h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRetardedPath
        ν T W W i j k l x := by
    funext s
    unfold h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRetardedPath
    unfold h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative
    rw [Real.fourierInv_eq']
    dsimp only [K, phase]
    simp only [smul_eq_mul]

  rw [hEq] at hOuter
  exact hOuter

/-- On every positive selected source interval, the ordered third-coordinate
retarded path is integrable and uniformly controlled by the interval-uniform
cubic forcing envelope. -/
theorem h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRetardedPath_selectedRestart_integrableOn_Ioo
    {ν A a T : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (haT : a < T)
    (hTR : T ≤ h3FinHeatLerayRestartRadius ν A)
    (i j k l : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    IntegrableOn
      (h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRetardedPath
        ν T W W i j k l x)
      (Set.Ioo a T)
      volume := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let B : ℝ :=
    (2 * Real.pi) ^ 3 *
      h3SelectedForcingThirdMomentUniformEnvelope ν A a T

  have hEnv0 :
      0 ≤
        h3SelectedForcingThirdMomentUniformEnvelope ν A a T :=
    h3SelectedForcingThirdMomentUniformEnvelope_nonneg
      hν U₀ hA hU₀ ha haT hTR

  have hB0 : 0 ≤ B := by
    dsimp only [B]
    positivity

  have hMeas :
      AEStronglyMeasurable
        (h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRetardedPath
          ν T W W i j k l x)
        ((volume : Measure ℝ).restrict (Set.Ioo a T)) := by
    dsimp only [W]
    exact
      h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRetardedPath_selectedRestart_aestronglyMeasurable
        hν U₀ hA hU₀ i j k l x

  have hMajor :
      IntegrableOn
        (fun _s : ℝ => B)
        (Set.Ioo a T)
        volume := by
    rw [
      ← intervalIntegrable_iff_integrableOn_Ioo_of_le
        haT.le
    ]
    exact intervalIntegrable_const

  refine hMajor.mono' hMeas ?_
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards with s hs

  have hs0 : 0 < s :=
    lt_trans ha hs.1

  have hsR :
      s ≤ h3FinHeatLerayRestartRadius ν A :=
    le_trans hs.2.le hTR

  have hlag :
      0 < T - s :=
    sub_pos.mpr hs.2

  have hRep :=
    norm_h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative_selectedRestart_le_unheatedThirdMoment
      hν U₀ hA hU₀ hs0 hsR hlag i j k l x

  have hMass :=
    h3RawFinLerayOuterProductDivergence_selectedRestart_thirdMass_le_uniform_on
      hν U₀ hA hU₀
      ha hs.1.le hs.2.le hTR i

  dsimp only [W] at hRep hMass
  unfold h3RawFinLerayOuterProductDivergenceThirdMass at hMass

  calc
    ‖h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRetardedPath
        ν T W W i j k l x s‖
        =
      ‖h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative
        ν (T - s) (W s) (W s) i j k l x‖ := by
          rfl
    _ ≤
      (2 * Real.pi) ^ 3 *
        (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 3 *
            ‖h3RawFinLerayOuterProductDivergence
              (W s) (W s) i ξ‖) :=
      hRep
    _ ≤ B := by
      dsimp only [B]
      exact
        mul_le_mul_of_nonneg_left
          hMass
          (by positivity)

/-- Differentiating the fresh short-interval second-coordinate integral in one
further canonical direction gives the corresponding third-coordinate short
integral. -/
theorem h3RawFinLerayOuterProductDivergenceHeatFreshSecondCoordinateIntegral_hasDerivAt_thirdCoordinate
    {ν A t h : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (hh : 0 < h)
    (hthR : t + h ≤ h3FinHeatLerayRestartRadius ν A)
    (i j k l : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let el : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 l)
    HasDerivAt
      (fun r : ℝ =>
        ∫ s in t..t + h,
          h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
            ν (t + h) W W i j k (x + r • el) s)
      (∫ s in t..t + h,
        h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRetardedPath
          ν (t + h) W W i j k l x s)
      0 := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let T : ℝ := t + h

  let el : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 l)

  let F : ℝ → ℝ → ℂ :=
    fun r s =>
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
        ν T W W i j k (x + r • el) s

  let F' : ℝ → ℝ → ℂ :=
    fun r s =>
      h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRetardedPath
        ν T W W i j k l (x + r • el) s

  let B : ℝ :=
    (2 * Real.pi) ^ 3 *
      h3SelectedForcingThirdMomentUniformEnvelope ν A t T

  let bound : ℝ → ℝ :=
    fun _s => B

  have hT : 0 < T := by
    dsimp only [T]
    linarith

  have htT : t ≤ T := by
    dsimp only [T]
    linarith

  have htTstrict : t < T := by
    dsimp only [T]
    linarith

  have hFreshSubset :
      Set.Ioo t T ⊆ Set.Ioo (0 : ℝ) T := by
    intro s hs
    exact ⟨lt_trans ht hs.1, hs.2⟩

  have hFInt :
      ∀ r : ℝ,
        Integrable
          (F r)
          (volume.restrict (Set.Ioo t T)) := by
    intro r
    have hLong :
        IntegrableOn
          (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
            ν T W W i j k (x + r • el))
          (Set.Ioo (0 : ℝ) T)
          volume :=
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath_selectedRestart_integrableOn_Ioo
        hν U₀ hA hU₀ hT hthR i j k (x + r • el)
    exact hLong.mono_set hFreshSubset

  have hFMeas :
      ∀ᶠ r : ℝ in 𝓝 0,
        AEStronglyMeasurable
          (F r)
          (volume.restrict (Set.Ioo t T)) :=
    Filter.Eventually.of_forall fun r =>
      (hFInt r).aestronglyMeasurable

  have hF0Int :
      Integrable
        (F 0)
        (volume.restrict (Set.Ioo t T)) :=
    hFInt 0

  have hF'0Int :
      Integrable
        (F' 0)
        (volume.restrict (Set.Ioo t T)) := by
    dsimp only [F']
    simp only [zero_smul, add_zero]
    exact
      h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRetardedPath_selectedRestart_integrableOn_Ioo
        hν U₀ hA hU₀ ht htTstrict hthR i j k l x

  have hF'0Meas :
      AEStronglyMeasurable
        (F' 0)
        (volume.restrict (Set.Ioo t T)) :=
    hF'0Int.aestronglyMeasurable

  have hEnv0 :
      0 ≤
        h3SelectedForcingThirdMomentUniformEnvelope ν A t T :=
    h3SelectedForcingThirdMomentUniformEnvelope_nonneg
      hν U₀ hA hU₀ ht htTstrict hthR

  have hB0 : 0 ≤ B := by
    dsimp only [B]
    positivity

  have hBoundInt :
      Integrable
        bound
        (volume.restrict (Set.Ioo t T)) := by
    change
      IntegrableOn
        (fun _s : ℝ => B)
        (Set.Ioo t T)
        volume
    rw [
      ← intervalIntegrable_iff_integrableOn_Ioo_of_le
        htT
    ]
    exact intervalIntegrable_const

  have hBound :
      ∀ᵐ s : ℝ ∂(volume.restrict (Set.Ioo t T)),
        ∀ r ∈ (Set.univ : Set ℝ),
          ‖F' r s‖ ≤ bound s := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards with s hs
    intro r hr

    have hs0 : 0 < s :=
      lt_trans ht hs.1

    have hsR :
        s ≤ h3FinHeatLerayRestartRadius ν A :=
      le_trans hs.2.le hthR

    have hlag :
        0 < T - s :=
      sub_pos.mpr hs.2

    have hRep :=
      norm_h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative_selectedRestart_le_unheatedThirdMoment
        hν U₀ hA hU₀ hs0 hsR hlag i j k l (x + r • el)

    have hMass :=
      h3RawFinLerayOuterProductDivergence_selectedRestart_thirdMass_le_uniform_on
        hν U₀ hA hU₀
        ht hs.1.le hs.2.le hthR i

    dsimp only [W] at hRep hMass
    unfold h3RawFinLerayOuterProductDivergenceThirdMass at hMass

    dsimp only [F', bound, B]
    unfold h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRetardedPath

    exact
      hRep.trans
        (mul_le_mul_of_nonneg_left
          hMass
          (by positivity))

  have hDiff :
      ∀ᵐ s : ℝ ∂(volume.restrict (Set.Ioo t T)),
        ∀ r ∈ (Set.univ : Set ℝ),
          HasDerivAt (F · s) (F' r s) r := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards with s hs
    intro r hr
    dsimp only [F, F']
    unfold
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
      h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRetardedPath
    simpa only [el] using
      (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative_hasDerivAt_thirdCoordinate_at
        hν (sub_pos.mpr hs.2) (W s) (W s) i j k l x r)

  have hIntegral :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (s := (Set.univ : Set ℝ))
      (F := F)
      (F' := F')
      (x₀ := (0 : ℝ))
      (bound := bound)
      (μ := volume.restrict (Set.Ioo t T))
      Filter.univ_mem
      hFMeas
      hF0Int
      hF'0Meas
      hBound
      hBoundInt
      hDiff).2

  have hValueIntegral (r : ℝ) :
      (∫ s : ℝ,
          F r s
          ∂(volume.restrict (Set.Ioo t T)))
        =
      ∫ s in t..T,
        h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
          ν T W W i j k (x + r • el) s := by
    rw [intervalIntegral.integral_of_le htT]
    rw [← restrict_Ioo_eq_restrict_Ioc]

  have hDerivativeIntegral :
      (∫ s : ℝ,
          F' 0 s
          ∂(volume.restrict (Set.Ioo t T)))
        =
      ∫ s in t..T,
        h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRetardedPath
          ν T W W i j k l x s := by
    rw [intervalIntegral.integral_of_le htT]
    rw [← restrict_Ioo_eq_restrict_Ioc]
    simp only [F', el, zero_smul, add_zero]

  change
    HasDerivAt
      (fun r : ℝ =>
        ∫ s in t..T,
          h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
            ν T W W i j k (x + r • el) s)
      (∫ s in t..T,
        h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRetardedPath
          ν T W W i j k l x s)
      0

  have hValueFunction :
      (fun r : ℝ =>
        ∫ s in t..T,
          h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
            ν T W W i j k (x + r • el) s)
        =
      (fun r : ℝ =>
        ∫ s : ℝ,
          F r s
          ∂(volume.restrict (Set.Ioo t T))) := by
    funext r
    exact (hValueIntegral r).symm

  rw [hValueFunction]
  rw [← hDerivativeIntegral]
  exact hIntegral

/-- For every positive increment staying inside the restart interval, the
ordered third Fréchet coordinate of the actual shifted spectral fresh Duhamel
state is exactly the literal translated third-coordinate retarded integral. -/
theorem h3SelectedDuhamelFresh_thirdFrechet_coordinate_eq_intervalIntegral
    {ν A t h : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (hh : 0 < h)
    (hthR : t + h ≤ h3FinHeatLerayRestartRadius ν A)
    (i a b c : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let Dfresh : H3SpectralScalarState :=
      h3SpectralFinHeatLerayDuhamel
        ν h hν
        (fun r => W (r + t))
        (fun r => W (r + t))
        i
    let ea : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 a)
    let eb : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 b)
    let ec : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 c)
    iteratedFDeriv ℝ 3
        (h3SpectralScalarC1Representative Dfresh)
        x
        ![ea, eb, ec]
      =
    ∫ s in t..t + h,
      h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRetardedPath
        ν (t + h) W W i a b c x s := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let Dfresh : H3SpectralScalarState :=
    h3SpectralFinHeatLerayDuhamel
      ν h hν
      (fun r => W (r + t))
      (fun r => W (r + t))
      i

  let Fresh : H3FourierPoint3 → ℂ :=
    h3SpectralScalarC1Representative Dfresh

  let ea : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 a)

  let eb : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 b)

  let ec : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 c)

  have hFreshC3 :
      ContDiff ℝ 3 Fresh := by
    dsimp only [Fresh, Dfresh, W]
    exact
      h3SelectedDuhamelFresh_C1Representative_contDiff_three
        hν U₀ hA hU₀ ht hh hthR i

  have hFreshSecondEq
      (y : H3FourierPoint3) :
      iteratedFDeriv ℝ 2 Fresh y ![eb, ec]
        =
      ∫ s in t..t + h,
        h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
          ν (t + h) W W i b c y s := by
    have hSecond :=
      h3SelectedDuhamelFresh_secondFrechet_coordinate_eq_intervalIntegral
        hν U₀ hA hU₀ ht hh hthR i b c y

    dsimp only [W, Dfresh, Fresh, eb, ec] at hSecond ⊢

    have hAxis :
        (∫ s in t..t + h,
          h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRetardedPath
            ν (t + h) W W i y s
            (h3FourierAxisDirection (h3AxisOfFin3 c))
            (h3FourierAxisDirection (h3AxisOfFin3 b)))
          =
        ∫ s in t..t + h,
          h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
            ν (t + h) W W i b c y s := by
      apply intervalIntegral.integral_congr_uIoo
      intro s hs
      exact
        h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRetardedPath_axis_axis
          ν (t + h) W W i b c y s

    exact hSecond.trans hAxis

  have hFreshC3' :
      ContDiff ℝ (2 + 1) Fresh := by
    convert hFreshC3 using 1 <;> norm_num

  have hfdC2 :
      ContDiff ℝ 2 (fderiv ℝ Fresh) := by
    exact
      (contDiff_succ_iff_fderiv.mp hFreshC3').2.2

  have hfdC2' :
      ContDiff ℝ (1 + 1) (fderiv ℝ Fresh) := by
    convert hfdC2 using 1 <;> norm_num

  have hfd2C1 :
      ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ Fresh)) := by
    exact
      (contDiff_succ_iff_fderiv.mp hfdC2').2.2

  have hfd2DiffAt :
      DifferentiableAt ℝ
        (fderiv ℝ (fderiv ℝ Fresh))
        x :=
    hfd2C1.differentiable_one.differentiableAt

  have hEval1 :=
    hfd2DiffAt.hasFDerivAt.clm_apply
      (hasFDerivAt_const eb x)

  have hEval2 :=
    hEval1.clm_apply
      (hasFDerivAt_const ec x)

  have hEvalFDeriv :
      HasFDerivAt
        (fun y : H3FourierPoint3 =>
          (fderiv ℝ (fderiv ℝ Fresh) y) eb ec)
        (((fderiv ℝ (fderiv ℝ (fderiv ℝ Fresh)) x).flip eb).flip ec)
        x := by
    simpa using hEval2

  have hEvalLineRaw :=
    hEvalFDeriv.hasLineDerivAt ea

  have hEvalLine :
      HasDerivAt
        (fun r : ℝ =>
          (fderiv ℝ (fderiv ℝ Fresh) (x + r • ea)) eb ec)
        ((fderiv ℝ (fderiv ℝ (fderiv ℝ Fresh)) x) ea eb ec)
        0 := by
    change
      HasDerivAt
        (fun r : ℝ =>
          (fderiv ℝ (fderiv ℝ Fresh) (x + r • ea)) eb ec)
        ((fderiv ℝ (fderiv ℝ (fderiv ℝ Fresh)) x) ea eb ec)
        0
      at hEvalLineRaw
    exact hEvalLineRaw

  have hEvalLine' :
      HasDerivAt
        (fun r : ℝ =>
          ∫ s in t..t + h,
            h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
              ν (t + h) W W i b c (x + r • ea) s)
        ((fderiv ℝ (fderiv ℝ (fderiv ℝ Fresh)) x) ea eb ec)
        0 := by
    convert hEvalLine using 1
    funext r
    have hSecond :=
      hFreshSecondEq (x + r • ea)
    rw [iteratedFDeriv_two_apply] at hSecond
    simpa only [
      Matrix.cons_val_zero,
      Matrix.cons_val_one,
      Matrix.head_cons,
      Matrix.tail_cons
    ] using hSecond.symm

  have hMixed :
      HasDerivAt
        (fun r : ℝ =>
          ∫ s in t..t + h,
            h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
              ν (t + h) W W i b c (x + r • ea) s)
        (∫ s in t..t + h,
          h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRetardedPath
            ν (t + h) W W i b c a x s)
        0 := by
    dsimp only [ea]
    exact
      h3RawFinLerayOuterProductDivergenceHeatFreshSecondCoordinateIntegral_hasDerivAt_thirdCoordinate
        hν U₀ hA hU₀ ht hh hthR i b c a x

  have hNested :
      ((fderiv ℝ (fderiv ℝ (fderiv ℝ Fresh)) x) ea eb ec)
        =
      ∫ s in t..t + h,
        h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRetardedPath
          ν (t + h) W W i b c a x s :=
    hEvalLine'.unique hMixed

  have hCycle :
      (∫ s in t..t + h,
        h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRetardedPath
          ν (t + h) W W i b c a x s)
        =
      ∫ s in t..t + h,
        h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRetardedPath
          ν (t + h) W W i a b c x s := by
    apply intervalIntegral.integral_congr_uIoo
    intro s hs
    exact
      h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRetardedPath_cycle
        ν (t + h) W W i a b c x s

  have hIterated :
      iteratedFDeriv ℝ 3 Fresh x ![ea, eb, ec]
        =
      (fderiv ℝ (fderiv ℝ (fderiv ℝ Fresh)) x) ea eb ec := by
    calc
      iteratedFDeriv ℝ 3 Fresh x ![ea, eb, ec]
          =
        iteratedFDeriv ℝ 2
            (fun y => fderiv ℝ Fresh y)
            x
            (Fin.init ![ea, eb, ec])
            (![ea, eb, ec] (Fin.last 2)) := by
          exact
            iteratedFDeriv_succ_apply_right
              (𝕜 := ℝ) (f := Fresh) (x := x) ![ea, eb, ec]
      _ =
        (fderiv ℝ (fderiv ℝ (fderiv ℝ Fresh)) x) ea eb ec := by
          rw [iteratedFDeriv_two_apply]
          simp [Fin.init]

  exact
    hIterated.trans
      (hNested.trans hCycle)

/-- The normalized ordered third Fréchet coordinate of the actual shifted
spectral fresh Duhamel remainder converges from the right to the instantaneous
forcing third-coordinate derivative. -/
theorem tendsto_inv_smul_h3SelectedDuhamelFresh_thirdFrechet_coordinate_zero_right
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i a b c : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let ea : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 a)
    let eb : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 b)
    let ec : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 c)
    Tendsto
      (fun h : ℝ =>
        h⁻¹ •
          iteratedFDeriv ℝ 3
            (h3SpectralScalarC1Representative
              (h3SpectralFinHeatLerayDuhamel
                ν h hν
                (fun r => W (r + t))
                (fun r => W (r + t))
                i))
            x
            ![ea, eb, ec])
      (𝓝[Set.Ioi (0 : ℝ)] 0)
      (𝓝
        (iteratedFDeriv ℝ 3
          (h3RawFinLerayOuterProductDivergenceC0Representative
            (W t) (W t) i)
          x
          ![ea, eb, ec])) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let ea : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 a)

  let eb : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 b)

  let ec : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 c)

  have hLiteral :=
    tendsto_inv_smul_intervalIntegral_h3RawFinLerayOuterProductDivergenceHeatFreshThirdFrechet_selectedRestart_zero_right
      hν U₀ hA hU₀ ht htR i a b c x

  have hLiteral' :
      Tendsto
        (fun h : ℝ =>
          h⁻¹ •
            (∫ s in t..t + h,
              h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRetardedPath
                ν (t + h) W W i a b c x s))
        (𝓝[Set.Ioi (0 : ℝ)] 0)
        (𝓝
          (iteratedFDeriv ℝ 3
            (h3RawFinLerayOuterProductDivergenceC0Representative
              (W t) (W t) i)
            x
            ![ea, eb, ec])) := by
    simpa only [W, ea, eb, ec] using hLiteral

  let R : ℝ :=
    h3FinHeatLerayRestartRadius ν A

  have hGap :
      0 < R - t := by
    dsimp only [R]
    linarith

  have hSmall :
      Set.Iio (R - t) ∈
        (𝓝[Set.Ioi (0 : ℝ)] 0) := by
    exact
      mem_inf_of_left
        (Iio_mem_nhds hGap)

  have hEq :
      (fun h : ℝ =>
        h⁻¹ •
          iteratedFDeriv ℝ 3
            (h3SpectralScalarC1Representative
              (h3SpectralFinHeatLerayDuhamel
                ν h hν
                (fun r => W (r + t))
                (fun r => W (r + t))
                i))
            x
            ![ea, eb, ec])
        =ᶠ[𝓝[Set.Ioi (0 : ℝ)] 0]
      (fun h : ℝ =>
        h⁻¹ •
          (∫ s in t..t + h,
            h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRetardedPath
              ν (t + h) W W i a b c x s)) := by
    filter_upwards
      [self_mem_nhdsWithin, hSmall]
      with h hh hsmall

    have hthR :
        t + h ≤
          h3FinHeatLerayRestartRadius ν A := by
      dsimp only [R] at hsmall
      change
        h <
          h3FinHeatLerayRestartRadius ν A - t
        at hsmall
      linarith

    have hFresh :=
      h3SelectedDuhamelFresh_thirdFrechet_coordinate_eq_intervalIntegral
        hν U₀ hA hU₀ ht hh hthR i a b c x

    dsimp only [W, ea, eb, ec] at hFresh
    rw [hFresh]

  exact
    Tendsto.congr'
      hEq.symm
      hLiteral'

end

end Euclidean
end Bridge
end PrimeTensor
