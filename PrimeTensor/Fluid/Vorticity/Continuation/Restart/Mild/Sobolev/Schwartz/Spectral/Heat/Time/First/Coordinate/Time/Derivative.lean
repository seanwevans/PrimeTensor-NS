import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Time.First.Coordinate.Representative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Time.Hessian.Trace.Representative
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Positive-time derivative of the scalar heat first coordinate

`FirstCoordinateRepresentative` identifies the canonical first spatial
coordinate derivative of the positive-time heat reconstruction with the
inverse Fourier transform of

    D_a(ξ) heatRaw(ν,t,G,ξ).

The time derivative of this raw amplitude is

    D_a(ξ) heatGeneratorRaw(ν,t,G,ξ).

At a positive base time, one derivative symbol together with the order-two
heat generator is dominated by the third heat moment at time `t/2`.  Thus the
same dominated parametric-integral theorem used for the zeroth spatial heat
derivative differentiates the first-coordinate reconstruction in time.

Finally, the existing raw heat-generator Hessian-trace identity gives

    D_a heatGeneratorRaw
      = ν * Σ_k D_a D_k D_k heatRaw.

Passing this finite identity through inverse Fourier reconstruction identifies
the derivative coefficient with viscosity times the genuine third spatial
Fréchet trace.

No new analytic estimate is introduced beyond the already-compiled positive
time third-moment smoothing.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzHeatTimeFirstCoordinateTimeDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- Raw amplitude obtained by taking the time derivative of one heat first
coordinate amplitude. -/
noncomputable def h3SpectralScalarHeatFirstCoordinateTimeGeneratorRawAmplitude
    (ν t : ℝ)
    (G : H3SpectralScalarState)
    (a : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  h3FourierDerivativeSymbol a ξ *
    h3SpectralScalarHeatTimeGeneratorRawRepresentative ν t G ξ

/-- The first-coordinate time-generator raw amplitude is measurable. -/
theorem h3SpectralScalarHeatFirstCoordinateTimeGeneratorRawAmplitude_aestronglyMeasurable
    (ν t : ℝ)
    (G : H3SpectralScalarState)
    (a : Fin 3) :
    AEStronglyMeasurable
      (h3SpectralScalarHeatFirstCoordinateTimeGeneratorRawAmplitude
        ν t G a)
      (volume : Measure H3FourierPoint3) := by
  unfold h3SpectralScalarHeatFirstCoordinateTimeGeneratorRawAmplitude
  exact
    (h3FourierDerivativeSymbol_continuous a).aestronglyMeasurable.mul
      (h3SpectralScalarHeatTimeGeneratorRawRepresentative_aestronglyMeasurable
        ν t G)

/-- Pointwise raw identity: differentiating the first spatial coordinate of
the heat flow in time gives viscosity times the ordered third-coordinate
trace. -/
theorem h3SpectralScalarHeatFirstCoordinateTimeGeneratorRawAmplitude_eq_viscosity_mul_thirdTrace
    (ν t : ℝ)
    (G : H3SpectralScalarState)
    (a : Fin 3)
    (ξ : H3FourierPoint3) :
    h3SpectralScalarHeatFirstCoordinateTimeGeneratorRawAmplitude
        ν t G a ξ
      =
    (ν : ℂ) *
      (∑ k : Fin 3,
        h3SpectralScalarHeatThirdCoordinateRawAmplitude
          ν t G a k k ξ) := by
  unfold h3SpectralScalarHeatFirstCoordinateTimeGeneratorRawAmplitude

  rw [
    h3SpectralScalarHeatTimeGeneratorRawRepresentative_eq_viscosity_mul_laplacian
      ν t G ξ
  ]

  calc
    h3FourierDerivativeSymbol a ξ *
        ((ν : ℂ) *
          h3SpectralScalarHeatLaplacianRawAmplitude ν t G ξ)
        =
      (ν : ℂ) *
        (h3FourierDerivativeSymbol a ξ *
          h3SpectralScalarHeatLaplacianRawAmplitude ν t G ξ) := by
            ring
    _ =
      (ν : ℂ) *
        (∑ k : Fin 3,
          h3FourierDerivativeSymbol a ξ *
            h3SpectralScalarHeatSecondDiagonalRawAmplitude
              ν t G k ξ) := by
            unfold h3SpectralScalarHeatLaplacianRawAmplitude
            rw [Finset.mul_sum]
    _ =
      (ν : ℂ) *
        (∑ k : Fin 3,
          h3SpectralScalarHeatThirdCoordinateRawAmplitude
            ν t G a k k ξ) := by
            congr 1

/-- Physical inverse-Fourier representative of the first-coordinate heat time
generator. -/
noncomputable def h3SpectralScalarHeatFirstCoordinateTimeGeneratorRepresentative
    (ν t : ℝ)
    (G : H3SpectralScalarState)
    (a : Fin 3) :
    H3FourierPoint3 → ℂ :=
  FourierTransformInv.fourierInv
    (h3SpectralScalarHeatFirstCoordinateTimeGeneratorRawAmplitude
      ν t G a)

/-- Passing the raw trace identity through inverse Fourier reconstruction
identifies the first-coordinate heat time generator with viscosity times the
genuine third spatial Fréchet trace. -/
theorem h3SpectralScalarHeatFirstCoordinateTimeGeneratorRepresentative_eq_viscosity_mul_thirdTrace
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState)
    (a : Fin 3)
    (x : H3FourierPoint3) :
    h3SpectralScalarHeatFirstCoordinateTimeGeneratorRepresentative
        ν t G a x
      =
    (ν : ℂ) *
      (∑ k : Fin 3,
        iteratedFDeriv ℝ 3
          (h3SpectralScalarHeatC3Representative ν t G)
          x
          ![
            h3FourierAxisDirection (h3AxisOfFin3 a),
            h3FourierAxisDirection (h3AxisOfFin3 k),
            h3FourierAxisDirection (h3AxisOfFin3 k)
          ]) := by
  let A0 : H3FourierPoint3 → ℂ :=
    h3SpectralScalarHeatThirdCoordinateRawAmplitude
      ν t G a (0 : Fin 3) (0 : Fin 3)

  let A1 : H3FourierPoint3 → ℂ :=
    h3SpectralScalarHeatThirdCoordinateRawAmplitude
      ν t G a (1 : Fin 3) (1 : Fin 3)

  let A2 : H3FourierPoint3 → ℂ :=
    h3SpectralScalarHeatThirdCoordinateRawAmplitude
      ν t G a (2 : Fin 3) (2 : Fin 3)

  have hA0 :
      Integrable A0
        (volume : Measure H3FourierPoint3) := by
    dsimp only [A0]
    exact
      h3SpectralScalarHeatThirdCoordinateRawAmplitude_integrable
        hν ht G a (0 : Fin 3) (0 : Fin 3)

  have hA1 :
      Integrable A1
        (volume : Measure H3FourierPoint3) := by
    dsimp only [A1]
    exact
      h3SpectralScalarHeatThirdCoordinateRawAmplitude_integrable
        hν ht G a (1 : Fin 3) (1 : Fin 3)

  have hA2 :
      Integrable A2
        (volume : Measure H3FourierPoint3) := by
    dsimp only [A2]
    exact
      h3SpectralScalarHeatThirdCoordinateRawAmplitude_integrable
        hν ht G a (2 : Fin 3) (2 : Fin 3)

  have hRaw :
      h3SpectralScalarHeatFirstCoordinateTimeGeneratorRawAmplitude
          ν t G a
        =
      (ν : ℂ) • ((A0 + A1) + A2) := by
    funext ξ
    rw [
      h3SpectralScalarHeatFirstCoordinateTimeGeneratorRawAmplitude_eq_viscosity_mul_thirdTrace
        ν t G a ξ
    ]
    rw [Fin.sum_univ_three]
    dsimp only [A0, A1, A2, Pi.smul_apply, Pi.add_apply]
    simp only [smul_eq_mul]

  have hInnerNegContinuous :
      Continuous
        (fun p : H3FourierPoint3 × H3FourierPoint3 =>
          ((-(innerₗ H3FourierPoint3)) p.1) p.2) := by
    change
      Continuous
        (fun p : H3FourierPoint3 × H3FourierPoint3 =>
          -inner ℝ p.1 p.2)
    exact
      (continuous_inner
        (𝕜 := ℝ)
        (E := H3FourierPoint3)).neg

  have hInv01 :
      FourierTransformInv.fourierInv (A0 + A1) x
        =
      FourierTransformInv.fourierInv A0 x
        +
      FourierTransformInv.fourierInv A1 x := by
    change
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          (A0 + A1)
          x
        =
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          A0
          x
        +
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          A1
          x

    exact
      congrFun
        (VectorFourier.fourierIntegral_add
          (e := Real.fourierChar)
          (μ := (volume : Measure H3FourierPoint3))
          (L := -(innerₗ H3FourierPoint3))
          Real.continuous_fourierChar
          hInnerNegContinuous
          hA0
          hA1)
        x

  have hInv012 :
      FourierTransformInv.fourierInv ((A0 + A1) + A2) x
        =
      FourierTransformInv.fourierInv (A0 + A1) x
        +
      FourierTransformInv.fourierInv A2 x := by
    change
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          ((A0 + A1) + A2)
          x
        =
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          (A0 + A1)
          x
        +
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          A2
          x

    exact
      congrFun
        (VectorFourier.fourierIntegral_add
          (e := Real.fourierChar)
          (μ := (volume : Measure H3FourierPoint3))
          (L := -(innerₗ H3FourierPoint3))
          Real.continuous_fourierChar
          hInnerNegContinuous
          (hA0.add hA1)
          hA2)
        x

  have hInvSmul :
      FourierTransformInv.fourierInv
          ((ν : ℂ) • ((A0 + A1) + A2))
          x
        =
      (ν : ℂ) *
        FourierTransformInv.fourierInv
          ((A0 + A1) + A2)
          x := by
    change
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          ((ν : ℂ) • ((A0 + A1) + A2))
          x
        =
      (ν : ℂ) *
        VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          ((A0 + A1) + A2)
          x

    simpa only [Pi.smul_apply, smul_eq_mul] using
      congrFun
        (VectorFourier.fourierIntegral_const_smul
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          ((A0 + A1) + A2)
          (ν : ℂ))
        x

  have hThird0 :=
    h3SpectralScalarHeatThirdCoordinateRepresentative_eq_iteratedFDeriv
      hν ht G a (0 : Fin 3) (0 : Fin 3) x

  have hThird1 :=
    h3SpectralScalarHeatThirdCoordinateRepresentative_eq_iteratedFDeriv
      hν ht G a (1 : Fin 3) (1 : Fin 3) x

  have hThird2 :=
    h3SpectralScalarHeatThirdCoordinateRepresentative_eq_iteratedFDeriv
      hν ht G a (2 : Fin 3) (2 : Fin 3) x

  unfold h3SpectralScalarHeatFirstCoordinateTimeGeneratorRepresentative
  rw [hRaw, hInvSmul, hInv012, hInv01]
  dsimp only [A0, A1, A2]
  change
    (ν : ℂ) *
      (h3SpectralScalarHeatThirdCoordinateRepresentative
          ν t G a (0 : Fin 3) (0 : Fin 3) x
        +
       h3SpectralScalarHeatThirdCoordinateRepresentative
          ν t G a (1 : Fin 3) (1 : Fin 3) x
        +
       h3SpectralScalarHeatThirdCoordinateRepresentative
          ν t G a (2 : Fin 3) (2 : Fin 3) x)
      =
    (ν : ℂ) *
      (∑ k : Fin 3,
        iteratedFDeriv ℝ 3
          (h3SpectralScalarHeatC3Representative ν t G)
          x
          ![
            h3FourierAxisDirection (h3AxisOfFin3 a),
            h3FourierAxisDirection (h3AxisOfFin3 k),
            h3FourierAxisDirection (h3AxisOfFin3 k)
          ])
  rw [hThird0, hThird1, hThird2]
  rw [Fin.sum_univ_three]

/-- The positive-time first-coordinate heat reconstruction has an ordinary
time derivative whose coefficient is the named first-coordinate heat time
generator. -/
theorem h3SpectralScalarHeatFirstCoordinateRepresentative_hasDerivAt_time
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState)
    (a : Fin 3)
    (x : H3FourierPoint3) :
    HasDerivAt
      (fun s : ℝ =>
        h3SpectralScalarHeatFirstCoordinateRepresentative
          ν s G a x)
      (h3SpectralScalarHeatFirstCoordinateTimeGeneratorRepresentative
        ν t G a x)
      t := by
  let τ : ℝ := t / 2
  let S : Set ℝ := Set.Ioi τ
  let C : ℝ := ν * (2 * Real.pi) ^ 3

  let phase : H3FourierPoint3 → ℂ :=
    fun ξ =>
      Complex.exp
        (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) *
          Complex.I)

  let F : ℝ → H3FourierPoint3 → ℂ :=
    fun s ξ =>
      phase ξ *
        h3SpectralScalarHeatFirstCoordinateRawAmplitude
          ν s G a ξ

  let F' : ℝ → H3FourierPoint3 → ℂ :=
    fun s ξ =>
      phase ξ *
        h3SpectralScalarHeatFirstCoordinateTimeGeneratorRawAmplitude
          ν s G a ξ

  let bound : H3FourierPoint3 → ℝ :=
    fun ξ =>
      C *
        (‖ξ‖ ^ 3 *
          ‖h3SpectralScalarHeatRawRepresentative ν τ G ξ‖)

  have hτ : 0 < τ := by
    dsimp only [τ]
    linarith

  have hτt : τ < t := by
    dsimp only [τ]
    linarith

  have hS : S ∈ 𝓝 t := by
    dsimp only [S]
    exact Ioi_mem_nhds hτt

  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity

  have hPhaseContinuous : Continuous phase := by
    dsimp only [phase]
    fun_prop

  have hF_meas :
      ∀ᶠ s in 𝓝 t,
        AEStronglyMeasurable
          (F s)
          (volume : Measure H3FourierPoint3) := by
    exact Filter.Eventually.of_forall (fun s => by
      dsimp only [F]
      exact
        hPhaseContinuous.aestronglyMeasurable.mul
          ((h3FourierDerivativeSymbol_continuous a).aestronglyMeasurable.mul
            (h3SpectralScalarHeatRawRepresentative_aestronglyMeasurable
              ν s G)))

  have hF_int :
      Integrable
        (F t)
        (volume : Measure H3FourierPoint3) := by
    have hFirst :=
      h3SpectralScalarHeatFirstCoordinateRawAmplitude_integrable
        hν ht G a

    have hMeas :
        AEStronglyMeasurable
          (F t)
          (volume : Measure H3FourierPoint3) := by
      dsimp only [F]
      exact
        hPhaseContinuous.aestronglyMeasurable.mul
          hFirst.aestronglyMeasurable

    rw [← integrable_norm_iff hMeas]

    simpa only [
      F,
      phase,
      norm_mul,
      Complex.norm_exp,
      Complex.mul_re,
      Complex.ofReal_re,
      Complex.ofReal_im,
      Complex.I_re,
      Complex.I_im,
      mul_zero,
      zero_mul,
      sub_self,
      Real.exp_zero,
      one_mul
    ] using hFirst.norm

  have hF'_meas :
      AEStronglyMeasurable
        (F' t)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [F']
    exact
      hPhaseContinuous.aestronglyMeasurable.mul
        (h3SpectralScalarHeatFirstCoordinateTimeGeneratorRawAmplitude_aestronglyMeasurable
          ν t G a)

  have h_bound :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        ∀ s ∈ S, ‖F' s ξ‖ ≤ bound ξ := by
    filter_upwards with ξ
    intro s hs

    have hτs : τ ≤ s := hs.le

    have hDa :=
      norm_h3FourierDerivativeSymbol_le_gradientMagnitude a ξ

    have hDa' :
        ‖h3FourierDerivativeSymbol a ξ‖
          ≤
        (2 * Real.pi) * ‖ξ‖ := by
      simpa only [h3FourierGradientMagnitude] using hDa

    have hGen :=
      norm_h3SpectralScalarHeatTimeGeneratorRawRepresentative_le_anchor
        hν hτs G ξ

    have hAmp :
        ‖h3SpectralScalarHeatFirstCoordinateTimeGeneratorRawAmplitude
            ν s G a ξ‖
          ≤
        C *
          (‖ξ‖ ^ 3 *
            ‖h3SpectralScalarHeatRawRepresentative ν τ G ξ‖) := by
      unfold h3SpectralScalarHeatFirstCoordinateTimeGeneratorRawAmplitude
      rw [norm_mul]

      calc
        ‖h3FourierDerivativeSymbol a ξ‖ *
            ‖h3SpectralScalarHeatTimeGeneratorRawRepresentative
              ν s G ξ‖
            ≤
          ((2 * Real.pi) * ‖ξ‖) *
            ‖h3SpectralScalarHeatTimeGeneratorRawRepresentative
              ν s G ξ‖ := by
                exact
                  mul_le_mul_of_nonneg_right
                    hDa'
                    (norm_nonneg _)
        _ ≤
          ((2 * Real.pi) * ‖ξ‖) *
            ((ν * (2 * Real.pi) ^ 2) *
              (‖ξ‖ ^ 2 *
                ‖h3SpectralScalarHeatRawRepresentative
                  ν τ G ξ‖)) := by
                exact
                  mul_le_mul_of_nonneg_left
                    hGen
                    (by positivity)
        _ =
          C *
            (‖ξ‖ ^ 3 *
              ‖h3SpectralScalarHeatRawRepresentative ν τ G ξ‖) := by
                dsimp only [C]
                ring

    dsimp only [F', bound]
    rw [norm_mul]

    have hPhaseNorm : ‖phase ξ‖ = 1 := by
      dsimp only [phase]
      simp only [
        Complex.norm_exp,
        Complex.mul_re,
        Complex.ofReal_re,
        Complex.ofReal_im,
        Complex.I_re,
        Complex.I_im,
        mul_zero,
        zero_mul,
        sub_self,
        Real.exp_zero
      ]

    rw [hPhaseNorm, one_mul]
    exact hAmp

  have bound_integrable :
      Integrable
        bound
        (volume : Measure H3FourierPoint3) := by
    have hMoment :=
      h3SpectralScalarHeatRawRepresentative_moment_integrable
        hν hτ G 3 (by norm_num)

    dsimp only [bound, C]
    exact
      hMoment.const_mul
        (ν * (2 * Real.pi) ^ 3)

  have h_diff :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        ∀ s ∈ S, HasDerivAt (F · ξ) (F' s ξ) s := by
    filter_upwards with ξ
    intro s hs

    have hRaw :=
      h3SpectralScalarHeatRawRepresentative_hasDerivAt_time
        ν s G ξ

    have hCoord :=
      HasDerivAt.const_mul
        (h3FourierDerivativeSymbol a ξ)
        hRaw

    have hPhase :=
      HasDerivAt.const_mul
        (phase ξ)
        hCoord

    simpa only [
      F,
      F',
      h3SpectralScalarHeatFirstCoordinateRawAmplitude,
      h3SpectralScalarHeatFirstCoordinateTimeGeneratorRawAmplitude,
      mul_assoc
    ] using hPhase

  have hMain :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := F)
      (F' := F')
      (x₀ := t)
      (s := S)
      (bound := bound)
      (μ := (volume : Measure H3FourierPoint3))
      hS
      hF_meas
      hF_int
      hF'_meas
      h_bound
      bound_integrable
      h_diff

  have hPathEq :
      (fun s : ℝ =>
        ∫ ξ : H3FourierPoint3, F s ξ)
        =
      (fun s : ℝ =>
        h3SpectralScalarHeatFirstCoordinateRepresentative
          ν s G a x) := by
    funext s
    dsimp only [F, phase]
    unfold h3SpectralScalarHeatFirstCoordinateRepresentative
    rw [Real.fourierInv_eq']
    simp only [smul_eq_mul]

  have hGeneratorEq :
      (∫ ξ : H3FourierPoint3, F' t ξ)
        =
      h3SpectralScalarHeatFirstCoordinateTimeGeneratorRepresentative
        ν t G a x := by
    dsimp only [F', phase]
    unfold h3SpectralScalarHeatFirstCoordinateTimeGeneratorRepresentative
    rw [Real.fourierInv_eq']
    simp only [smul_eq_mul]

  have hDeriv := hMain.2
  rw [hPathEq, hGeneratorEq] at hDeriv
  exact hDeriv

/-- Direct form consumed by the selected mixed-derivative closure: the time
derivative of one spatial coordinate of the positive-time heat reconstruction
is viscosity times its third spatial coordinate trace. -/
theorem h3SpectralScalarHeatFirstCoordinateRepresentative_hasDerivAt_time_eq_viscosity_thirdTrace
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState)
    (a : Fin 3)
    (x : H3FourierPoint3) :
    HasDerivAt
      (fun s : ℝ =>
        h3SpectralScalarHeatFirstCoordinateRepresentative
          ν s G a x)
      ((ν : ℂ) *
        (∑ k : Fin 3,
          iteratedFDeriv ℝ 3
            (h3SpectralScalarHeatC3Representative ν t G)
            x
            ![
              h3FourierAxisDirection (h3AxisOfFin3 a),
              h3FourierAxisDirection (h3AxisOfFin3 k),
              h3FourierAxisDirection (h3AxisOfFin3 k)
            ]))
      t := by
  have h :=
    h3SpectralScalarHeatFirstCoordinateRepresentative_hasDerivAt_time
      hν ht G a x

  rw [
    h3SpectralScalarHeatFirstCoordinateTimeGeneratorRepresentative_eq_viscosity_mul_thirdTrace
      hν ht G a x
  ] at h

  exact h

end

end Euclidean
end Bridge
end PrimeTensor
