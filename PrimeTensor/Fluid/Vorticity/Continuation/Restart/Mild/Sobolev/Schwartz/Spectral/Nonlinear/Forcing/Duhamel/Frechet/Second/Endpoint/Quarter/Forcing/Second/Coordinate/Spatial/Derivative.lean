import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.Second.Coordinate.Lag.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Heat.Spatial.Derivative

/-!
# Fixed-lag mixed second spatial derivative identity

The first coordinate derivative representative is itself an inverse Fourier
transform.  Differentiating its phase along a second Euclidean coordinate
produces one more Fourier derivative symbol.  This file identifies that
derivative with the mixed second-coordinate representative already controlled
by the endpoint second-moment branch.

This is the fixed-lag input needed before the second spatial derivative can be
moved through the Duhamel source-time integral.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped ENNReal NNReal Topology RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3SchwartzQuarterForcingSecondCoordinateSpatialDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Along an affine `k`-coordinate line, the derivative of the first-coordinate
Fourier kernel is exactly the mixed `j,k` second-coordinate Fourier kernel. -/
theorem hasDerivAt_h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeFourierKernel_secondCoordinate
    (ν τ : ℝ)
    (U V : H3SpectralFinVectorState)
    (i j k : Fin 3)
    (x ξ : H3FourierPoint3)
    (r : ℝ) :
    HasDerivAt
      (fun q : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeFourierKernel
          ν τ U V i j
          (x + q • h3FourierAxisDirection (h3AxisOfFin3 k)) ξ)
      (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel
        ν τ U V i j k
        (x + r • h3FourierAxisDirection (h3AxisOfFin3 k)) ξ)
      r := by
  let e : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 k)

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
    change HasDerivAt
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
      h3RawFinLerayOuterProductDivergenceHeatRepresentative
        ν τ U V i ξ

  have hProductExp := hPhaseExp.mul_const A

  have hk :
      (((2 * Real.pi) * inner ℝ ξ e) • (Complex.I : ℂ))
        =
      h3FourierDerivativeSymbol k ξ := by
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
        h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude
          ν τ U V i j k ξ := by
    rw [hk]
    dsimp [A]
    unfold h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude
    ring

  rw [hDerivativeEq] at hProductExp

  have hKernelEq (q : ℝ) :
      h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeFourierKernel
          ν τ U V i j (x + q • e) ξ
        =
      Complex.exp
          (((2 * Real.pi) * inner ℝ ξ (x + q • e)) • (Complex.I : ℂ)) * A := by
    unfold h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeFourierKernel
    dsimp [A]
    simp only [Circle.smul_def, Real.fourierChar_apply,
      inner_neg_right, neg_neg, smul_eq_mul]

  have hDerivativeKernelEq :
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel
          ν τ U V i j k (x + r • e) ξ
        =
      Complex.exp
          (((2 * Real.pi) * inner ℝ ξ (x + r • e)) • (Complex.I : ℂ)) *
        h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude
          ν τ U V i j k ξ := by
    unfold h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel
    simp only [Circle.smul_def, Real.fourierChar_apply,
      inner_neg_right, neg_neg, Complex.real_smul, smul_eq_mul]

  change HasDerivAt
    (fun q : ℝ =>
      h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeFourierKernel
        ν τ U V i j (x + q • e) ξ)
    (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel
      ν τ U V i j k (x + r • e) ξ)
    r

  simpa only [hKernelEq, hDerivativeKernelEq] using hProductExp

/-- At positive heat lag, the mixed second-coordinate representative is the
genuine derivative of the first-coordinate representative. -/
theorem h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_hasDerivAt_secondCoordinate
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i j k : Fin 3)
    (x : H3FourierPoint3) :
    HasDerivAt
      (fun r : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
          ν τ U V i j
          (x + r • h3FourierAxisDirection (h3AxisOfFin3 k)))
      (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
        ν τ U V i j k x)
      0 := by
  let e : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 k)

  let F : ℝ → H3FourierPoint3 → ℂ :=
    fun r ξ =>
      h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeFourierKernel
        ν τ U V i j (x + r • e) ξ

  let F' : ℝ → H3FourierPoint3 → ℂ :=
    fun r ξ =>
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel
        ν τ U V i j k (x + r • e) ξ

  let bound : H3FourierPoint3 → ℝ :=
    fun ξ =>
      ‖h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude
        ν τ U V i j k ξ‖

  have hFInt :
      ∀ r : ℝ,
        Integrable (F r) (volume : Measure H3FourierPoint3) := by
    intro r
    dsimp only [F]
    exact
      h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeFourierKernel_integrable
        hν hτ U V i j (x + r • e)

  have hFMeas :
      ∀ᶠ r : ℝ in 𝓝 0,
        AEStronglyMeasurable
          (F r)
          (volume : Measure H3FourierPoint3) :=
    Filter.Eventually.of_forall fun r => (hFInt r).aestronglyMeasurable

  have hF0Int :
      Integrable (F 0) (volume : Measure H3FourierPoint3) :=
    hFInt 0

  have hF'0Meas :
      AEStronglyMeasurable
        (F' 0)
        (volume : Measure H3FourierPoint3) := by
    have h :=
      (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel_integrable
        hν hτ U V i j k x).aestronglyMeasurable
    simpa [F', e] using h

  have hBoundInt :
      Integrable bound (volume : Measure H3FourierPoint3) := by
    dsimp only [bound]
    exact
      (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude_integrable
        hν hτ U V i j k).norm

  have hBound :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        ∀ r ∈ (Set.univ : Set ℝ),
          ‖F' r ξ‖ ≤ bound ξ := by
    filter_upwards with ξ
    intro r hr
    dsimp only [F', bound]
    unfold h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel
    simp only [Circle.norm_smul]
    exact le_rfl

  have hDiff :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        ∀ r ∈ (Set.univ : Set ℝ),
          HasDerivAt (F · ξ) (F' r ξ) r := by
    filter_upwards with ξ
    intro r hr
    dsimp only [F, F']
    simpa [e] using
      (hasDerivAt_h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeFourierKernel_secondCoordinate
        ν τ U V i j k x ξ r)

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

  simpa [F, F', e,
    h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_eq_integral_kernel,
    h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative_eq_integral_kernel]
    using hIntegral

/-- Translated fixed-lag mixed second-coordinate derivative identity. -/
theorem h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_hasDerivAt_secondCoordinate_at
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i j k : Fin 3)
    (x : H3FourierPoint3)
    (r : ℝ) :
    HasDerivAt
      (fun q : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
          ν τ U V i j
          (x + q • h3FourierAxisDirection (h3AxisOfFin3 k)))
      (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
        ν τ U V i j k
        (x + r • h3FourierAxisDirection (h3AxisOfFin3 k)))
      r := by
  let e : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 k)

  have h0 :
      HasDerivAt
        (fun q : ℝ =>
          h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
            ν τ U V i j ((x + r • e) + q • e))
        (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
          ν τ U V i j k (x + r • e))
        0 := by
    simpa [e] using
      (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_hasDerivAt_secondCoordinate
        hν hτ U V i j k (x + r • e))

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
        h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
          ν τ U V i j (x + q • e))
        =ᶠ[𝓝 r]
      ((fun q : ℝ =>
          h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
            ν τ U V i j ((x + r • e) + q • e)) ∘
        fun q : ℝ => q - r) := by
    filter_upwards with q
    simp only [Function.comp_apply]
    rw [hPoint q]

  have hTransport := hComp.congr_of_eventuallyEq hFunEq

  have hDerivEq :
      (1 : ℝ) •
          h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
            ν τ U V i j k (x + r • e)
        =
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
        ν τ U V i j k (x + r • e) :=
    one_smul ℝ _

  have hFinal := hTransport.congr_deriv hDerivEq
  simpa only [e] using hFinal

end
end Euclidean
end Bridge
end PrimeTensor
