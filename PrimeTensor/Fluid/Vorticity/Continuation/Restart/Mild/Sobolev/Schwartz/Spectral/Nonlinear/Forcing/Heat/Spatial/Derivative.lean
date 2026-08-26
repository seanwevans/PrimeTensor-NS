import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Path.Derivative.Continuity
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Fixed-lag spatial derivative identity for the nonlinear heat forcing

The preceding pathwise modules constructed and controlled the inverse-Fourier
representative obtained by multiplying the positive-lag nonlinear forcing by
one coordinate derivative symbol.  Before differentiating the Duhamel time
integral, we must identify that representative with the actual spatial
coordinate derivative of the fixed-lag classical `C³` reconstruction.

This file closes that identification directly at the Fourier-integral level.
For a fixed positive heat lag, vary the spatial point along one Euclidean
coordinate direction.  The inverse-Fourier phase differentiates to exactly
`h3FourierDerivativeSymbol j`; the derivative amplitude is already `L¹`, so
Mathlib's dominated parametric-integral theorem moves this one-dimensional
spatial derivative through the Fourier integral.

The resulting theorem is the precise fixed-lag ingredient required by the
next layer, where the same spatial coordinate derivative will be moved through
the retarded Duhamel time integral.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped ENNReal NNReal Topology Real RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralNonlinearForcingHeatSpatialDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The positive-lag heat-multiplied nonlinear forcing itself is in Fourier
`L¹`. -/
theorem h3RawFinLerayOuterProductDivergenceHeatRepresentative_integrable
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    Integrable
      (h3RawFinLerayOuterProductDivergenceHeatRepresentative
        ν τ U V i)
      (volume : Measure H3FourierPoint3) := by
  rw [← integrable_norm_iff
    (h3RawFinLerayOuterProductDivergenceHeatRepresentative_aestronglyMeasurable
      ν τ U V i)]
  simpa using
    (h3RawFinLerayOuterProductDivergenceHeatRepresentative_moment_integrable
      hν hτ U V i 0 (by norm_num))

/-- Fourier-integral kernel of the fixed-lag classical inverse-Fourier
reconstruction.  It is written in the same `fourier-at-negation` form as the
existing first-derivative kernel. -/
noncomputable def h3RawFinLerayOuterProductDivergenceHeatInverseFourierKernel
    (ν τ : ℝ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (x ξ : H3FourierPoint3) : ℂ :=
  𝐞 (-(inner ℝ ξ (-x))) •
    h3RawFinLerayOuterProductDivergenceHeatRepresentative
      ν τ U V i ξ

/-- The fixed-lag inverse-Fourier kernel is integrable at every spatial point. -/
theorem h3RawFinLerayOuterProductDivergenceHeatInverseFourierKernel_integrable
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    Integrable
      (h3RawFinLerayOuterProductDivergenceHeatInverseFourierKernel
        ν τ U V i x)
      (volume : Measure H3FourierPoint3) := by
  unfold h3RawFinLerayOuterProductDivergenceHeatInverseFourierKernel
  rw [Real.fourierIntegral_convergent_iff (-x)]
  exact
    h3RawFinLerayOuterProductDivergenceHeatRepresentative_integrable
      hν hτ U V i

/-- The fixed-lag `C³` reconstruction is literally the integral of the kernel
introduced above. -/
theorem h3RawFinLerayOuterProductDivergenceHeatC3Representative_eq_integral_kernel
    (ν τ : ℝ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    h3RawFinLerayOuterProductDivergenceHeatC3Representative
        ν τ U V i x
      =
    ∫ ξ : H3FourierPoint3,
      h3RawFinLerayOuterProductDivergenceHeatInverseFourierKernel
        ν τ U V i x ξ := by
  unfold h3RawFinLerayOuterProductDivergenceHeatC3Representative
  rw [Real.fourierInv_eq_fourier_neg]
  rw [Real.fourier_eq]
  rfl

/-- Along one affine coordinate line, the derivative of the fixed-lag
inverse-Fourier kernel is exactly the already-constructed first-derivative
Fourier kernel. -/
theorem hasDerivAt_h3RawFinLerayOuterProductDivergenceHeatInverseFourierKernel_coordinate
    (ν τ : ℝ)
    (U V : H3SpectralFinVectorState)
    (i j : Fin 3)
    (x ξ : H3FourierPoint3)
    (r : ℝ) :
    HasDerivAt
      (fun q : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatInverseFourierKernel
          ν τ U V i
          (x + q • h3FourierAxisDirection (h3AxisOfFin3 j)) ξ)
      (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeFourierKernel
        ν τ U V i j
        (x + r • h3FourierAxisDirection (h3AxisOfFin3 j)) ξ)
      r := by
  let e : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 j)

  have hSmul :
      HasDerivAt (fun q : ℝ => q • e) e r := by
    simpa using (hasDerivAt_id r).smul_const e

  have hLine :
      HasDerivAt (fun q : ℝ => x + q • e) e r := by
    exact HasDerivAt.const_add x hSmul

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
        r := by
    exact HasDerivAt.const_mul (2 * Real.pi) hInner

  have hComplexPhaseArg :
      HasDerivAt
        (fun q : ℝ =>
          ((2 * Real.pi) * inner ℝ ξ (x + q • e)) • (Complex.I : ℂ))
        (((2 * Real.pi) * inner ℝ ξ e) • (Complex.I : ℂ))
        r :=
    hRealPhaseArg.smul_const (Complex.I : ℂ)

  have hPhaseExp := hComplexPhaseArg.cexp

  let A : ℂ :=
    h3RawFinLerayOuterProductDivergenceHeatRepresentative
      ν τ U V i ξ

  have hProductExp := hPhaseExp.mul_const A

  have hDerivativeEq :
      ((Complex.exp
          (((2 * Real.pi) * inner ℝ ξ (x + r • e)) • (Complex.I : ℂ)) *
        (((2 * Real.pi) * inner ℝ ξ e) • (Complex.I : ℂ))) * A)
        =
      Complex.exp
          (((2 * Real.pi) * inner ℝ ξ (x + r • e)) • (Complex.I : ℂ)) *
        (h3FourierDerivativeSymbol j ξ * A) := by
    rw [h3FourierDerivativeSymbol_eq_inner]
    dsimp [e]
    push_cast
    ring

  rw [hDerivativeEq] at hProductExp

  have hKernelEq (q : ℝ) :
      h3RawFinLerayOuterProductDivergenceHeatInverseFourierKernel
          ν τ U V i (x + q • e) ξ
        =
      Complex.exp
          (((2 * Real.pi) * inner ℝ ξ (x + q • e)) • (Complex.I : ℂ)) * A := by
    unfold h3RawFinLerayOuterProductDivergenceHeatInverseFourierKernel
    dsimp [A]
    simp only [Circle.smul_def, Real.fourierChar_apply,
      inner_neg_right, neg_neg, Complex.real_smul, smul_eq_mul]

  have hDerivativeKernelEq :
      h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeFourierKernel
          ν τ U V i j (x + r • e) ξ
        =
      Complex.exp
          (((2 * Real.pi) * inner ℝ ξ (x + r • e)) • (Complex.I : ℂ)) *
        (h3FourierDerivativeSymbol j ξ * A) := by
    unfold h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeFourierKernel
    dsimp [A]
    simp only [Circle.smul_def, Real.fourierChar_apply,
      inner_neg_right, neg_neg, Complex.real_smul, smul_eq_mul]

  change HasDerivAt
    (fun q : ℝ =>
      h3RawFinLerayOuterProductDivergenceHeatInverseFourierKernel
        ν τ U V i (x + q • e) ξ)
    (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeFourierKernel
      ν τ U V i j (x + r • e) ξ)
    r
  simpa only [hKernelEq, hDerivativeKernelEq] using hProductExp

/-- At every positive heat lag, the inverse-Fourier representative obtained by
multiplying with `h3FourierDerivativeSymbol j` is the genuine derivative of
the fixed-lag classical reconstruction along the corresponding Euclidean
coordinate direction. -/
theorem h3RawFinLerayOuterProductDivergenceHeatC3Representative_hasDerivAt_coordinate
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i j : Fin 3)
    (x : H3FourierPoint3) :
    HasDerivAt
      (fun r : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatC3Representative
          ν τ U V i
          (x + r • h3FourierAxisDirection (h3AxisOfFin3 j)))
      (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
        ν τ U V i j x)
      0 := by
  let e : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 j)

  let F : ℝ → H3FourierPoint3 → ℂ :=
    fun r ξ =>
      h3RawFinLerayOuterProductDivergenceHeatInverseFourierKernel
        ν τ U V i (x + r • e) ξ

  let F' : ℝ → H3FourierPoint3 → ℂ :=
    fun r ξ =>
      h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeFourierKernel
        ν τ U V i j (x + r • e) ξ

  let bound : H3FourierPoint3 → ℝ :=
    fun ξ =>
      ‖h3FourierDerivativeSymbol j ξ *
        h3RawFinLerayOuterProductDivergenceHeatRepresentative
          ν τ U V i ξ‖

  have hFInt :
      ∀ r : ℝ,
        Integrable (F r) (volume : Measure H3FourierPoint3) := by
    intro r
    dsimp [F]
    exact
      h3RawFinLerayOuterProductDivergenceHeatInverseFourierKernel_integrable
        hν hτ U V i (x + r • e)

  have hFMeas :
      ∀ᶠ r : ℝ in 𝓝 0,
        AEStronglyMeasurable
          (F r)
          (volume : Measure H3FourierPoint3) :=
    Filter.Eventually.of_forall fun r => (hFInt r).1

  have hF0Int :
      Integrable (F 0) (volume : Measure H3FourierPoint3) :=
    hFInt 0

  have hF'0Meas :
      AEStronglyMeasurable
        (F' 0)
        (volume : Measure H3FourierPoint3) := by
    have h :=
      (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeFourierKernel_integrable
        hν hτ U V i j x).1
    simpa [F', e] using h

  have hBoundInt :
      Integrable bound (volume : Measure H3FourierPoint3) := by
    dsimp [bound]
    exact
      (h3RawFinLerayOuterProductDivergenceHeatRepresentative_derivative_integrable
        hν hτ U V i j).norm

  have hBound :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        ∀ r ∈ (Set.univ : Set ℝ),
          ‖F' r ξ‖ ≤ bound ξ := by
    filter_upwards with ξ
    intro r hr
    dsimp [F', bound]
    unfold h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeFourierKernel
    simp only [Circle.norm_smul]
    exact le_rfl

  have hDiff :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        ∀ r ∈ (Set.univ : Set ℝ),
          HasDerivAt (F · ξ) (F' r ξ) r := by
    filter_upwards with ξ
    intro r hr
    dsimp [F, F']
    simpa [e] using
      (hasDerivAt_h3RawFinLerayOuterProductDivergenceHeatInverseFourierKernel_coordinate
        ν τ U V i j x ξ r)

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
    h3RawFinLerayOuterProductDivergenceHeatC3Representative_eq_integral_kernel,
    h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_eq_integral_kernel]
    using hIntegral

end

end Euclidean
end Bridge
end PrimeTensor
