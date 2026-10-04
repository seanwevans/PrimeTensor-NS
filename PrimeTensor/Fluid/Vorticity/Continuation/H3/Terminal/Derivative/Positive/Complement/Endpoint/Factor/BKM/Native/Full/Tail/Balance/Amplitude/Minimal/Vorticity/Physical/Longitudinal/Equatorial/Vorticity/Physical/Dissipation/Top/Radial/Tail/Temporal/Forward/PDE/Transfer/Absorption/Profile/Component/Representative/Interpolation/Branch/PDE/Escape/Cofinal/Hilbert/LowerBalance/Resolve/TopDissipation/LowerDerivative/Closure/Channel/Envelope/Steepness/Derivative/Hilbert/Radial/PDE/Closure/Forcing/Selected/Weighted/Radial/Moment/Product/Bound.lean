import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.PDE.Closure.Forcing.Selected.Weighted.Radial.Moment.Product
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Forcing.Radial.L2

/-!
# Quantitative radial L² bound for raw product convolution

The generic radial forcing layer already proves that sufficiently high raw
input moments imply

    |ξ|^m (F * G) ∈ L².

For the forcing time-product rule we need the quantitative version of that
statement, because the first input will be a difference quotient converging to
the genuine velocity derivative.

The existing membership proof contains the exact pointwise estimate

    (|ξ|^m |F*G|)^2
      ≤
    B(F,G) |ξ|^(2m) |F*G|,

where

    B(F,G) = ‖F̂‖₂ ‖Ĝ‖₂.

Integrating yields

    ‖ |ξ|^m(F*G) ‖₂²
      ≤
    B(F,G) M_{2m}(F*G).

The generic Young moment theorem already controls the convolution moment mass
`M_{2m}(F*G)` by the corresponding input moment masses.  This file packages
both inequalities.

The finite divergence and Leray-projection bounds can now be assembled from
this scalar estimate without repeating the convolution measure theory.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3RadialConvolutionL2Bound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1800000

/-! ## Local frequency-uniform convolution bound

`Radial/L2.lean` uses the same estimate internally, but its helper theorems are
private to that module.  Repackage the two elementary Hilbert-space facts here
under local names so the quantitative bound is self-contained.
-/

/-- Reflected translation preserves the raw Fourier `L²` norm. -/
private theorem norm_h3SpectralScalarRawFourierReflectedShiftL2_eq_bound
    (G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    ‖h3SpectralScalarRawFourierReflectedShiftL2 G ξ‖
      =
    ‖h3SpectralScalarRawFourierL2 G‖ := by

  unfold h3SpectralScalarRawFourierReflectedShiftL2

  exact
    MeasureTheory.Lp.norm_compMeasurePreserving
      (h3SpectralScalarRawFourierL2 G)
      (h3FourierSubLeftContinuousMapFamily_measurePreserving ξ)

/-- Raw product convolution is uniformly bounded by the two raw Fourier
`L²` norms. -/
private theorem norm_h3RawProductConvolution_le_rawL2Product_bound
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    ‖h3RawProductConvolution F G ξ‖
      ≤
    ‖h3SpectralScalarRawFourierConjL2 F‖ *
      ‖h3SpectralScalarRawFourierL2 G‖ := by

  rw [h3RawProductConvolution_eq_inner_conjRaw_shift]

  calc
    ‖inner ℂ
        (h3SpectralScalarRawFourierConjL2 F)
        (h3SpectralScalarRawFourierReflectedShiftL2 G ξ)‖
        ≤
      ‖h3SpectralScalarRawFourierConjL2 F‖ *
        ‖h3SpectralScalarRawFourierReflectedShiftL2 G ξ‖ :=
      norm_inner_le_norm _ _
    _ =
      ‖h3SpectralScalarRawFourierConjL2 F‖ *
        ‖h3SpectralScalarRawFourierL2 G‖ := by
      rw [
        norm_h3SpectralScalarRawFourierReflectedShiftL2_eq_bound
      ]

/--
Canonical order-`m` radial Fourier `L²` package of one raw product convolution.
-/
noncomputable def h3RawProductConvolutionRadialFourierL2
    (m : ℕ)
    (F G : H3SpectralScalarState)
    (hF :
      H3RawFourierMomentIntegrable
        (((2 * m : ℕ) : ℝ))
        F)
    (hG :
      H3RawFourierMomentIntegrable
        (((2 * m : ℕ) : ℝ))
        G) :
    H3FourierComplexL2 :=
  (
    h3RawProductConvolution_radialWeight_memLp2_of_doubleMoment
      m F G hF hG
  ).toLp
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ m : ℝ) : ℂ) *
        h3RawProductConvolution F G ξ)

/--
The radial convolution package has the literal weighted representative.
-/
theorem h3RawProductConvolutionRadialFourierL2_ae
    (m : ℕ)
    (F G : H3SpectralScalarState)
    (hF :
      H3RawFourierMomentIntegrable
        (((2 * m : ℕ) : ℝ))
        F)
    (hG :
      H3RawFourierMomentIntegrable
        (((2 * m : ℕ) : ℝ))
        G) :
    (
      (
        h3RawProductConvolutionRadialFourierL2
          m F G hF hG :
        H3FourierComplexL2
      ) :
      H3FourierPoint3 → ℂ
    )
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ m : ℝ) : ℂ) *
        h3RawProductConvolution F G ξ) := by

  unfold h3RawProductConvolutionRadialFourierL2

  exact
    MemLp.coeFn_toLp
      (
        h3RawProductConvolution_radialWeight_memLp2_of_doubleMoment
          m F G hF hG
      )

/--
Squared radial `L²` norm of a raw product convolution is bounded by the
unweighted convolution `L∞` envelope times the doubled radial moment mass.
-/
theorem norm_sq_h3RawProductConvolutionRadialFourierL2_le
    (m : ℕ)
    (F G : H3SpectralScalarState)
    (hF :
      H3RawFourierMomentIntegrable
        (((2 * m : ℕ) : ℝ))
        F)
    (hG :
      H3RawFourierMomentIntegrable
        (((2 * m : ℕ) : ℝ))
        G) :
    ‖h3RawProductConvolutionRadialFourierL2
        m F G hF hG‖ ^ 2
      ≤
    (
      ‖h3SpectralScalarRawFourierConjL2 F‖ *
        ‖h3SpectralScalarRawFourierL2 G‖
    )
      *
    h3RawProductConvolutionMomentMass
      (((2 * m : ℕ) : ℝ))
      F G := by

  let B : ℝ :=
    ‖h3SpectralScalarRawFourierConjL2 F‖ *
      ‖h3SpectralScalarRawFourierL2 G‖

  let H : H3FourierComplexL2 :=
    h3RawProductConvolutionRadialFourierL2
      m F G hF hG

  have hB0 :
      0 ≤ B := by
    dsimp only [B]
    positivity

  have hMomentGeneric :=
    h3RawProductConvolution_moment_integrable_of
      (q := (((2 * m : ℕ) : ℝ)))
      (by positivity)
      F G hF hG

  have hMoment :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ (2 * m) *
            ‖h3RawProductConvolution F G ξ‖)
        (volume : Measure H3FourierPoint3) := by
    simpa only [
      h3FourierMomentWeight_natCast
    ] using hMomentGeneric

  have hH :=
    h3RawProductConvolutionRadialFourierL2_ae
      m F G hF hG

  rw [
    h3FourierComplexL2_norm_sq_eq_integral_norm_sq
  ]

  have hPoint :
      ∀ᵐ ξ : H3FourierPoint3
        ∂(volume : Measure H3FourierPoint3),
        ‖H ξ‖ ^ 2
          ≤
        B *
          (
            ‖ξ‖ ^ (2 * m) *
              ‖h3RawProductConvolution F G ξ‖
          ) := by

    filter_upwards [hH] with ξ hHξ

    rw [hHξ]

    have hr0 :
        0 ≤ ‖ξ‖ :=
      norm_nonneg ξ

    have hrm0 :
        0 ≤ ‖ξ‖ ^ m :=
      pow_nonneg hr0 m

    have hConv0 :
        0 ≤ ‖h3RawProductConvolution F G ξ‖ :=
      norm_nonneg _

    have hBound :
        ‖h3RawProductConvolution F G ξ‖
          ≤
        B := by
      dsimp only [B]
      exact
        norm_h3RawProductConvolution_le_rawL2Product_bound
          F G ξ

    have hPow :
        (‖ξ‖ ^ m) ^ 2
          =
        ‖ξ‖ ^ (2 * m) := by
      rw [pow_two, ← pow_add]
      congr 1
      omega

    rw [
      norm_mul,
      Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg hrm0,
      mul_pow,
      hPow
    ]

    calc
      ‖ξ‖ ^ (2 * m) *
          ‖h3RawProductConvolution F G ξ‖ ^ 2
          =
        ‖ξ‖ ^ (2 * m) *
          (
            ‖h3RawProductConvolution F G ξ‖ *
              ‖h3RawProductConvolution F G ξ‖
          ) := by
        rw [pow_two]
      _ ≤
        ‖ξ‖ ^ (2 * m) *
          (
            B *
              ‖h3RawProductConvolution F G ξ‖
          ) := by
        exact
          mul_le_mul_of_nonneg_left
            (
              mul_le_mul_of_nonneg_right
                hBound hConv0
            )
            (pow_nonneg hr0 (2 * m))
      _ =
        B *
          (
            ‖ξ‖ ^ (2 * m) *
              ‖h3RawProductConvolution F G ξ‖
          ) := by
        ring

  have hLeftInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖H ξ‖ ^ 2)
        (volume : Measure H3FourierPoint3) :=
    (MeasureTheory.Lp.memLp H).norm.integrable_sq

  have hRightInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          B *
            (
              ‖ξ‖ ^ (2 * m) *
                ‖h3RawProductConvolution F G ξ‖
            ))
        (volume : Measure H3FourierPoint3) :=
    hMoment.const_mul B

  have hIntegral :=
    integral_mono_ae
      hLeftInt hRightInt hPoint

  change
    (∫ ξ : H3FourierPoint3,
      ‖H ξ‖ ^ 2)
      ≤
    B *
      h3RawProductConvolutionMomentMass
        (((2 * m : ℕ) : ℝ))
        F G

  rw [integral_const_mul] at hIntegral

  unfold h3RawProductConvolutionMomentMass

  simpa only [
    h3FourierMomentWeight_natCast
  ] using hIntegral

/--
Fully explicit Young-type bound for the squared radial convolution `L²` norm.
-/
theorem norm_sq_h3RawProductConvolutionRadialFourierL2_le_stateMasses
    (m : ℕ)
    (F G : H3SpectralScalarState)
    (hF :
      H3RawFourierMomentIntegrable
        (((2 * m : ℕ) : ℝ))
        F)
    (hG :
      H3RawFourierMomentIntegrable
        (((2 * m : ℕ) : ℝ))
        G) :
    ‖h3RawProductConvolutionRadialFourierL2
        m F G hF hG‖ ^ 2
      ≤
    (
      ‖h3SpectralScalarRawFourierConjL2 F‖ *
        ‖h3SpectralScalarRawFourierL2 G‖
    )
      *
    (
      h3FourierMomentSplitCoefficient
          (((2 * m : ℕ) : ℝ))
        *
      (
        h3SpectralScalarRawFourierMomentMass
            (((2 * m : ℕ) : ℝ))
            F
          *
        h3SpectralScalarRawFourierL1Mass G
        +
        h3SpectralScalarRawFourierL1Mass F
          *
        h3SpectralScalarRawFourierMomentMass
            (((2 * m : ℕ) : ℝ))
            G
      )
    ) := by

  have hL2 :=
    norm_sq_h3RawProductConvolutionRadialFourierL2_le
      m F G hF hG

  have hMass :=
    h3RawProductConvolutionMomentMass_le
      (q := (((2 * m : ℕ) : ℝ)))
      (by positivity)
      F G hF hG

  have hB0 :
      0 ≤
        ‖h3SpectralScalarRawFourierConjL2 F‖ *
          ‖h3SpectralScalarRawFourierL2 G‖ := by
    positivity

  exact
    hL2.trans
      (
        mul_le_mul_of_nonneg_left
          hMass hB0
      )

end

end Euclidean
end Bridge
end PrimeTensor
