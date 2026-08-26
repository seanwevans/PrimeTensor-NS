import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Transport

/-!
# Weak H³ derivatives become Fourier multipliers

`Sobolev.Transport` proves that the project's classical coordinate derivatives,
after transport to the Euclidean Fourier carrier, are the corresponding weak
derivatives of complex `L²` classes.

This file performs the next exact step: Fourier transformation of that weak
derivative identity.

For complex `L²` classes `F,G`, if

    ∂_v F = G

as tempered distributions, then Mathlib's distributional Fourier theorem and
the compatibility of the `L²` and tempered-distribution Fourier transforms give

    𝓕 G
      =
    (2 π i) · <ξ,v> · 𝓕 F

as tempered distributions.

The final a.e. representative-identification is intentionally left separate.
That next step uses uniqueness of locally integrable representatives of a
distribution.  Keeping the two steps apart makes the unbounded coordinate
multiplier explicit instead of pretending it is a bounded `L² → L²`
multiplier.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform
open scoped ENNReal NNReal SchwartzMap LineDeriv ComplexConjugate

noncomputable section

noncomputable local instance axisFintypeH3FourierDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Generic weak derivative → Fourier multiplier -/

/--
Fourier transform of an `L²` weak directional derivative, stated exactly at
the tempered-distribution level.

Both `𝓕 F` and `𝓕 G` on the displayed formula are the `L²` Fourier transforms,
then embedded into tempered distributions.
-/
theorem h3WeakLineDerivative_fourier_eq_distribution_multiplier
    {v : H3FourierPoint3}
    {F G : H3FourierComplexL2}
    (hWeak : H3WeakLineDerivative v F G) :
    (((𝓕 G : H3FourierComplexL2)) :
        𝓢'(H3FourierPoint3, ℂ))
      =
    (2 * Real.pi * Complex.I) •
      TemperedDistribution.smulLeftCLM ℂ
        (fun ξ : H3FourierPoint3 =>
          (inner ℝ ξ v : ℂ))
        ((((𝓕 F : H3FourierComplexL2)) :
          𝓢'(H3FourierPoint3, ℂ))) := by
  unfold H3WeakLineDerivative at hWeak
  calc
    (((𝓕 G : H3FourierComplexL2)) :
        𝓢'(H3FourierPoint3, ℂ))
        =
      𝓕 ((G : H3FourierComplexL2) :
        𝓢'(H3FourierPoint3, ℂ)) := by
          symm
          exact
            MeasureTheory.Lp.fourier_toTemperedDistribution_eq G
    _ =
      𝓕
        (∂_{v}
          ((F : H3FourierComplexL2) :
            𝓢'(H3FourierPoint3, ℂ))) := by
          rw [hWeak]
    _ =
      (2 * Real.pi * Complex.I) •
        TemperedDistribution.smulLeftCLM ℂ
          (fun ξ : H3FourierPoint3 =>
            (inner ℝ ξ v : ℂ))
          (𝓕
            ((F : H3FourierComplexL2) :
              𝓢'(H3FourierPoint3, ℂ))) := by
          simpa using
            (TemperedDistribution.fourier_lineDerivOp_eq
              ((F : H3FourierComplexL2) :
                𝓢'(H3FourierPoint3, ℂ))
              v)
    _ =
      (2 * Real.pi * Complex.I) •
        TemperedDistribution.smulLeftCLM ℂ
          (fun ξ : H3FourierPoint3 =>
            (inner ℝ ξ v : ℂ))
          ((((𝓕 F : H3FourierComplexL2)) :
            𝓢'(H3FourierPoint3, ℂ))) := by
          rw [
            MeasureTheory.Lp.fourier_toTemperedDistribution_eq
              F
          ]

/-! ## Coordinate directions -/

/--
The Euclidean inner product with a transported project-axis unit vector simply
selects that coordinate.
-/
theorem inner_h3FourierAxisDirection
    (ξ : H3FourierPoint3)
    (i : PrimeTensor.Axis Depth.three) :
    inner ℝ ξ (h3FourierAxisDirection i) = ξ i := by
  classical
  rw [PiLp.inner_apply]
  simp [
    h3FourierAxisDirection,
    axisDirection
  ]

/--
The coordinate function used by Mathlib's directional Fourier theorem agrees
with the coordinate used by PrimeTensor's explicit first-derivative symbol.
-/
theorem h3FourierDerivativeSymbol_eq_inner
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    h3FourierDerivativeSymbol i ξ
      =
    (2 * Real.pi * Complex.I) *
      (inner ℝ ξ
        (h3FourierAxisDirection
          (h3AxisOfFin3 i)) : ℂ) := by
  rw [
    inner_h3FourierAxisDirection
      ξ
      (h3AxisOfFin3 i)
  ]
  rfl

/-! ## PrimeTensor scalar derivatives -/

/--
One concrete PrimeTensor coordinate derivative becomes the expected coordinate
Fourier multiplier, at the tempered-distribution level.

This is the exact composition of

* the classical-to-weak bridge from `WeakDerivative`,
* the `Point3`/Euclidean calculus transport from `Transport`, and
* Mathlib's Fourier theorem for weak directional derivatives.
-/
theorem h3ScalarFourierL2_spatialDerivative_eq_distribution_multiplier
    {f : ScalarField3}
    (hfC1 : SpatialC1 f)
    (i : PrimeTensor.Axis Depth.three)
    (hf : MemLp f 2 volume)
    (hdi : MemLp (spatial3.d i f) 2 volume) :
    ((h3ScalarFourierL2
        (hdi.toLp (spatial3.d i f)) :
          H3FourierComplexL2) :
        𝓢'(H3FourierPoint3, ℂ))
      =
    (2 * Real.pi * Complex.I) •
      TemperedDistribution.smulLeftCLM ℂ
        (fun ξ : H3FourierPoint3 =>
          (inner ℝ ξ
            (h3FourierAxisDirection i) : ℂ))
        ((h3ScalarFourierL2
            (hf.toLp f) :
              H3FourierComplexL2) :
          𝓢'(H3FourierPoint3, ℂ)) := by
  have hWeak :
      H3WeakLineDerivative
        (h3FourierAxisDirection i)
        (h3ComplexifyFourierL2
          (h3ToFourierRealL2 (hf.toLp f)))
        (h3ComplexifyFourierL2
          (h3ToFourierRealL2
            (hdi.toLp (spatial3.d i f)))) :=
    h3ToFourierRealL2_spatialDerivative_weak
      hfC1 i hf hdi

  have hFourier :=
    h3WeakLineDerivative_fourier_eq_distribution_multiplier
      hWeak

  change
    (((MeasureTheory.Lp.fourierTransformₗᵢ
        H3FourierPoint3 ℂ)
        (h3ComplexifyFourierL2
          (h3ToFourierRealL2
            (hdi.toLp (spatial3.d i f)))) :
          H3FourierComplexL2) :
        𝓢'(H3FourierPoint3, ℂ))
      =
    (2 * Real.pi * Complex.I) •
      TemperedDistribution.smulLeftCLM ℂ
        (fun ξ : H3FourierPoint3 =>
          (inner ℝ ξ
            (h3FourierAxisDirection i) : ℂ))
        (((MeasureTheory.Lp.fourierTransformₗᵢ
            H3FourierPoint3 ℂ)
            (h3ComplexifyFourierL2
              (h3ToFourierRealL2
                (hf.toLp f))) :
              H3FourierComplexL2) :
            𝓢'(H3FourierPoint3, ℂ))
    at hFourier

  simpa [h3ScalarFourierL2] using hFourier

/--
Fin-indexed form of the preceding theorem, with the multiplier written using
the project's explicit `h3FourierDerivativeSymbol`.
-/
theorem h3ScalarFourierL2_spatialDerivative_fin_eq_distribution_multiplier
    {f : ScalarField3}
    (hfC1 : SpatialC1 f)
    (i : Fin 3)
    (hf : MemLp f 2 volume)
    (hdi :
      MemLp
        (spatial3.d (h3AxisOfFin3 i) f)
        2 volume) :
    ((h3ScalarFourierL2
        (hdi.toLp
          (spatial3.d (h3AxisOfFin3 i) f)) :
          H3FourierComplexL2) :
        𝓢'(H3FourierPoint3, ℂ))
      =
    TemperedDistribution.smulLeftCLM ℂ
      (fun ξ : H3FourierPoint3 =>
        h3FourierDerivativeSymbol i ξ)
      ((h3ScalarFourierL2
          (hf.toLp f) :
            H3FourierComplexL2) :
        𝓢'(H3FourierPoint3, ℂ)) := by
  have h :=
    h3ScalarFourierL2_spatialDerivative_eq_distribution_multiplier
      hfC1
      (h3AxisOfFin3 i)
      hf hdi

  rw [h]

  have hg :
      (fun ξ : H3FourierPoint3 =>
        (inner ℝ ξ
          (h3FourierAxisDirection
            (h3AxisOfFin3 i)) : ℂ)).HasTemperateGrowth := by
    fun_prop

  rw [← smul_apply]
  rw [
    ← TemperedDistribution.smulLeftCLM_smul
      hg
      (2 * Real.pi * Complex.I)
  ]

  have hSymbol :
      ((2 * Real.pi * Complex.I) •
          (fun ξ : H3FourierPoint3 =>
            (inner ℝ ξ
              (h3FourierAxisDirection
                (h3AxisOfFin3 i)) : ℂ)))
        =
      (fun ξ : H3FourierPoint3 =>
        h3FourierDerivativeSymbol i ξ) := by
    funext ξ
    simpa only [Pi.smul_apply, smul_eq_mul] using
      (h3FourierDerivativeSymbol_eq_inner i ξ).symm

  rw [hSymbol]

end

end Euclidean
end Bridge
end PrimeTensor
