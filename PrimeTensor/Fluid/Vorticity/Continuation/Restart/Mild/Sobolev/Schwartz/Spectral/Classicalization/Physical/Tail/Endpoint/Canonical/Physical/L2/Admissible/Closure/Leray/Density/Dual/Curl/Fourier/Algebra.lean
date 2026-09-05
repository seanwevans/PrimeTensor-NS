import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Dual.Curl.Fourier.Reduction
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Classicalization: Fourier divergence plus curl forces zero

`Fourier.Reduction` isolated two remaining parameter-free obligations for the
physical Leray-density theorem:

* weak physical curl-freeness implies Fourier curl-freeness;
* a spectral state that is both Fourier divergence-free and Fourier curl-free
  vanishes.

This file closes the second obligation.

At a nonzero frequency `ξ`, write the three real coordinates as `a,b,c` and
the three spectral amplitudes as `g₀,g₁,g₂`.  All project Fourier derivative
symbols contain the same nonzero factor `2πi`, so divergence and curl reduce to

    a g₀ + b g₁ + c g₂ = 0,
    b g₀ = a g₁,
    c g₀ = a g₂,
    c g₁ = b g₂.

Multiplying the divergence relation by `a`, `b`, and `c`, and using the curl
relations, yields

    (a²+b²+c²) gⱼ = 0

for each component.  Since `ξ ≠ 0`, the real sum of squares is strictly
positive, hence every `gⱼ` is zero.

The single frequency `ξ = 0` is negligible for Euclidean Lebesgue measure, so
the pointwise argument upgrades directly to equality of the three `L²`
classes.

No weak/distributional Fourier bridge is used here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2AdmissibleClosureLerayDensityDualCurlFourierAlgebra
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PhysicalL2AdmissibleClosureLerayDensityDualCurlFourierAlgebra :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Pointwise algebra away from zero frequency -/

/-- At one nonzero Fourier frequency, the divergence and curl multiplier
relations force all three spectral amplitudes to vanish. -/
theorem h3SpectralFin_pointwise_eq_zero_of_divergenceFree_of_curlFree
    (ξ : H3FourierPoint3)
    (hξ : ξ ≠ 0)
    (g : Fin 3 → ℂ)
    (hDiv :
      (∑ j : Fin 3,
        h3FourierDerivativeSymbol j ξ * g j)
        =
      0)
    (hCurl :
      h3FourierDerivativeSymbol 1 ξ * g 0
          -
          h3FourierDerivativeSymbol 0 ξ * g 1
        =
      0
      ∧
      h3FourierDerivativeSymbol 2 ξ * g 0
          -
          h3FourierDerivativeSymbol 0 ξ * g 2
        =
      0
      ∧
      h3FourierDerivativeSymbol 2 ξ * g 1
          -
          h3FourierDerivativeSymbol 1 ξ * g 2
        =
      0) :
    ∀ i : Fin 3, g i = 0 := by
  let a : ℝ :=
    ξ (h3AxisOfFin3 0)
  let b : ℝ :=
    ξ (h3AxisOfFin3 1)
  let c : ℝ :=
    ξ (h3AxisOfFin3 2)

  have hCommon :
      (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
    Complex.two_pi_I_ne_zero

  have hDiv' :
      (a : ℂ) * g 0
          +
          (b : ℂ) * g 1
          +
          (c : ℂ) * g 2
        =
      0 := by
    have hFactored :
        (2 * Real.pi * Complex.I : ℂ) *
            ((a : ℂ) * g 0
              +
              (b : ℂ) * g 1
              +
              (c : ℂ) * g 2)
          =
        0 := by
      calc
        (2 * Real.pi * Complex.I : ℂ) *
              ((a : ℂ) * g 0
                +
                (b : ℂ) * g 1
                +
                (c : ℂ) * g 2)
            =
          h3FourierDerivativeSymbol 0 ξ * g 0
            +
          h3FourierDerivativeSymbol 1 ξ * g 1
            +
          h3FourierDerivativeSymbol 2 ξ * g 2 := by
              simp only [
                h3FourierDerivativeSymbol,
                a, b, c
              ]
              ring
        _ = 0 := by
              simpa only [Fin.sum_univ_three] using hDiv

    exact
      (mul_eq_zero.mp hFactored).resolve_left hCommon

  have h01 :
      (b : ℂ) * g 0
        =
      (a : ℂ) * g 1 := by
    have hFactored :
        (2 * Real.pi * Complex.I : ℂ) *
            ((b : ℂ) * g 0
              -
              (a : ℂ) * g 1)
          =
        0 := by
      calc
        (2 * Real.pi * Complex.I : ℂ) *
              ((b : ℂ) * g 0
                -
                (a : ℂ) * g 1)
            =
          h3FourierDerivativeSymbol 1 ξ * g 0
            -
          h3FourierDerivativeSymbol 0 ξ * g 1 := by
              simp only [
                h3FourierDerivativeSymbol,
                a, b
              ]
              ring
        _ = 0 :=
          hCurl.1

    exact
      sub_eq_zero.mp
        ((mul_eq_zero.mp hFactored).resolve_left hCommon)

  have h02 :
      (c : ℂ) * g 0
        =
      (a : ℂ) * g 2 := by
    have hFactored :
        (2 * Real.pi * Complex.I : ℂ) *
            ((c : ℂ) * g 0
              -
              (a : ℂ) * g 2)
          =
        0 := by
      calc
        (2 * Real.pi * Complex.I : ℂ) *
              ((c : ℂ) * g 0
                -
                (a : ℂ) * g 2)
            =
          h3FourierDerivativeSymbol 2 ξ * g 0
            -
          h3FourierDerivativeSymbol 0 ξ * g 2 := by
              simp only [
                h3FourierDerivativeSymbol,
                a, c
              ]
              ring
        _ = 0 :=
          hCurl.2.1

    exact
      sub_eq_zero.mp
        ((mul_eq_zero.mp hFactored).resolve_left hCommon)

  have h12 :
      (c : ℂ) * g 1
        =
      (b : ℂ) * g 2 := by
    have hFactored :
        (2 * Real.pi * Complex.I : ℂ) *
            ((c : ℂ) * g 1
              -
              (b : ℂ) * g 2)
          =
        0 := by
      calc
        (2 * Real.pi * Complex.I : ℂ) *
              ((c : ℂ) * g 1
                -
                (b : ℂ) * g 2)
            =
          h3FourierDerivativeSymbol 2 ξ * g 1
            -
          h3FourierDerivativeSymbol 1 ξ * g 2 := by
              simp only [
                h3FourierDerivativeSymbol,
                b, c
              ]
              ring
        _ = 0 :=
          hCurl.2.2

    exact
      sub_eq_zero.mp
        ((mul_eq_zero.mp hFactored).resolve_left hCommon)

  have hSumSqPos :
      0 < a ^ 2 + b ^ 2 + c ^ 2 := by
    by_contra hNot

    have hSumSqNonpos :
        a ^ 2 + b ^ 2 + c ^ 2 ≤ 0 :=
      le_of_not_gt hNot

    have ha0 : a = 0 := by
      nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]

    have hb0 : b = 0 := by
      nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]

    have hc0 : c = 0 := by
      nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]

    have hξ0 :
        ξ = 0 := by
      ext k
      cases k with
      | first =>
          change ξ xAxis = 0
          simpa [a] using ha0
      | next k =>
          cases k with
          | first =>
              change ξ yAxis = 0
              simpa [b] using hb0
          | next k =>
              cases k with
              | first =>
                  change ξ zAxis = 0
                  simpa [c] using hc0

    exact
      hξ hξ0

  have hCoeff :
      ((a ^ 2 + b ^ 2 + c ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hSumSqPos.ne'

  have hCoeffExpand :
      ((a ^ 2 + b ^ 2 + c ^ 2 : ℝ) : ℂ)
        =
      (a : ℂ) ^ 2 + (b : ℂ) ^ 2 + (c : ℂ) ^ 2 := by
    simp only [
      Complex.ofReal_add,
      Complex.ofReal_pow
    ]

  have hg0 : g 0 = 0 := by
    have hMul :
        ((a ^ 2 + b ^ 2 + c ^ 2 : ℝ) : ℂ) * g 0
          =
        0 := by
      rw [hCoeffExpand]

      calc
        ((a : ℂ) ^ 2 + (b : ℂ) ^ 2 + (c : ℂ) ^ 2) * g 0
            =
          (a : ℂ) * ((a : ℂ) * g 0)
            +
          (b : ℂ) * ((b : ℂ) * g 0)
            +
          (c : ℂ) * ((c : ℂ) * g 0) := by
              ring
        _ =
          (a : ℂ) * ((a : ℂ) * g 0)
            +
          (b : ℂ) * ((a : ℂ) * g 1)
            +
          (c : ℂ) * ((a : ℂ) * g 2) := by
              rw [h01, h02]
        _ =
          (a : ℂ) *
            ((a : ℂ) * g 0
              +
              (b : ℂ) * g 1
              +
              (c : ℂ) * g 2) := by
              ring
        _ = 0 := by
              rw [hDiv', mul_zero]

    exact
      (mul_eq_zero.mp hMul).resolve_left hCoeff

  have hg1 : g 1 = 0 := by
    have hMul :
        ((a ^ 2 + b ^ 2 + c ^ 2 : ℝ) : ℂ) * g 1
          =
        0 := by
      rw [hCoeffExpand]

      calc
        ((a : ℂ) ^ 2 + (b : ℂ) ^ 2 + (c : ℂ) ^ 2) * g 1
            =
          (a : ℂ) * ((a : ℂ) * g 1)
            +
          (b : ℂ) * ((b : ℂ) * g 1)
            +
          (c : ℂ) * ((c : ℂ) * g 1) := by
              ring
        _ =
          (a : ℂ) * ((b : ℂ) * g 0)
            +
          (b : ℂ) * ((b : ℂ) * g 1)
            +
          (c : ℂ) * ((b : ℂ) * g 2) := by
              rw [h01.symm, h12]
        _ =
          (b : ℂ) *
            ((a : ℂ) * g 0
              +
              (b : ℂ) * g 1
              +
              (c : ℂ) * g 2) := by
              ring
        _ = 0 := by
              rw [hDiv', mul_zero]

    exact
      (mul_eq_zero.mp hMul).resolve_left hCoeff

  have hg2 : g 2 = 0 := by
    have hMul :
        ((a ^ 2 + b ^ 2 + c ^ 2 : ℝ) : ℂ) * g 2
          =
        0 := by
      rw [hCoeffExpand]

      calc
        ((a : ℂ) ^ 2 + (b : ℂ) ^ 2 + (c : ℂ) ^ 2) * g 2
            =
          (a : ℂ) * ((a : ℂ) * g 2)
            +
          (b : ℂ) * ((b : ℂ) * g 2)
            +
          (c : ℂ) * ((c : ℂ) * g 2) := by
              ring
        _ =
          (a : ℂ) * ((c : ℂ) * g 0)
            +
          (b : ℂ) * ((c : ℂ) * g 1)
            +
          (c : ℂ) * ((c : ℂ) * g 2) := by
              rw [h02.symm, h12.symm]
        _ =
          (c : ℂ) *
            ((a : ℂ) * g 0
              +
              (b : ℂ) * g 1
              +
              (c : ℂ) * g 2) := by
              ring
        _ = 0 := by
              rw [hDiv', mul_zero]

    exact
      (mul_eq_zero.mp hMul).resolve_left hCoeff

  intro i
  fin_cases i
  · exact hg0
  · exact hg1
  · exact hg2

/-! ## Almost-everywhere spectral uniqueness -/

/-- A three-component spectral `L²` state that is both Fourier
divergence-free and Fourier curl-free is the zero state.

The only excluded frequency in the pointwise argument is `0`; Euclidean
Lebesgue measure has null singletons, so this exclusion disappears at the
`L²` level. -/
theorem h3SpectralFin_eq_zero_of_divergenceFree_of_curlFree
    (G : H3SpectralFinVectorState)
    (hDiv :
      H3SpectralFinDivergenceFree G)
    (hCurl :
      H3SpectralFinCurlFree G) :
    G = 0 := by
  have hPoint3HyperplaneNull :
      (volume : Measure Point3)
          {x : Point3 | x xAxis = 0}
        =
      0 := by
    change
      Measure.pi
          (fun _ : PrimeTensor.Axis Depth.three =>
            (volume : Measure ℝ))
          {x : Point3 | x xAxis = 0}
        =
      0

    exact
      Measure.pi_hyperplane
        (fun _ : PrimeTensor.Axis Depth.three =>
          (volume : Measure ℝ))
        xAxis
        0

  have hFourierHyperplaneNull :
      (volume : Measure H3FourierPoint3)
          ((WithLp.ofLp :
              H3FourierPoint3 → Point3) ⁻¹'
            {x : Point3 | x xAxis = 0})
        =
      0 := by
    exact
      (PiLp.volume_preserving_ofLp
        (PrimeTensor.Axis Depth.three)).preimage_null
        hPoint3HyperplaneNull

  have hFourierZeroNull :
      (volume : Measure H3FourierPoint3)
          ({0} : Set H3FourierPoint3)
        =
      0 := by
    refine
      measure_mono_null
        ?_
        hFourierHyperplaneNull

    intro ξ hξ
    simp only [Set.mem_singleton_iff] at hξ
    subst ξ
    simp

  have hAeNe :
      ∀ᵐ ξ : H3FourierPoint3 ∂volume,
        ξ ≠ 0 := by
    rw [ae_iff]

    simpa using hFourierZeroNull

  have hPoint :
      ∀ᵐ ξ ∂volume,
        ∀ i : Fin 3,
          (G i : H3FourierPoint3 → ℂ) ξ = 0 := by
    filter_upwards [
      hDiv,
      hCurl,
      hAeNe
    ] with ξ hDivξ hCurlξ hξ

    exact
      h3SpectralFin_pointwise_eq_zero_of_divergenceFree_of_curlFree
        ξ
        hξ
        (fun i =>
          (G i : H3FourierPoint3 → ℂ) ξ)
        hDivξ
        hCurlξ

  funext i

  change G i = 0

  apply MeasureTheory.Lp.ext

  have hZero :=
    MeasureTheory.Lp.coeFn_zero
      ℂ
      (2 : ℝ≥0∞)
      (volume : Measure H3FourierPoint3)

  filter_upwards [hPoint, hZero] with ξ hPointξ hZeroξ

  rw [hPointξ i]

  simpa only [Pi.zero_apply] using hZeroξ.symm

/-- The pure spectral algebra frontier introduced in `Fourier.Reduction` is
therefore closed. -/
theorem H3SpectralFinDivergenceFreeCurlFreeTrivial_proved :
    H3SpectralFinDivergenceFreeCurlFreeTrivial := by
  intro G hDiv hCurl

  exact
    h3SpectralFin_eq_zero_of_divergenceFree_of_curlFree
      G
      hDiv
      hCurl

end

end Euclidean
end Bridge
end PrimeTensor
