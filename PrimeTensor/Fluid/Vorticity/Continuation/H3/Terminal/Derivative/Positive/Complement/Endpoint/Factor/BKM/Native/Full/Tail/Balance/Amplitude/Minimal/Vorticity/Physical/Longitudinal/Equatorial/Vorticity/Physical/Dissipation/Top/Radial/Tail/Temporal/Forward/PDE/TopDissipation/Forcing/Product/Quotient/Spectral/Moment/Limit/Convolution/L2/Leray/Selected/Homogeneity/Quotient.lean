import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Spectral.Moment.Limit.Convolution.L2.Leray.Selected.Homogeneity

/-!
# Exact quadratic Leray difference-quotient algebra

Let `B(U,V)` denote one coordinate of the raw finite Leray-divergence form.
For two states `U,V`, a difference quotient `D`, a candidate derivative `R`,
and slope error `E`, assume

    h⁻¹ • (V - U) = D,
    V - U = h • D,
    E = D - R.

Bilinearity then gives the exact identity

    h⁻¹ • (B(V,V) - B(U,U))
      - (B(R,U) + B(U,R))
      =
    B(E,U) + B(U,E) + h • B(D,D).

Thus the nonlinear product-rule error separates into the two slope-error
cross channels already controlled in the preceding files and one genuinely
quadratic remainder carrying an explicit factor `h`.

No estimate is used in this file.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3RawFinLerayQuotientAlgebra
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1400000

/-! ## Additivity of the finite raw forms -/

/--
Finite outer-product divergence is additive in its first vector input.
-/
theorem h3RawFinOuterProductDivergence_add_left
    (U V W : H3SpectralFinVectorState)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    h3RawFinOuterProductDivergence (U + V) W i ξ
      =
    h3RawFinOuterProductDivergence U W i ξ +
      h3RawFinOuterProductDivergence V W i ξ := by

  unfold h3RawFinOuterProductDivergence

  simp_rw [
    Pi.add_apply,
    h3RawProductConvolution_add_left,
    mul_add
  ]

  rw [Finset.sum_add_distrib]

/--
Finite outer-product divergence is additive in its second vector input.
-/
theorem h3RawFinOuterProductDivergence_add_right
    (U V W : H3SpectralFinVectorState)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    h3RawFinOuterProductDivergence U (V + W) i ξ
      =
    h3RawFinOuterProductDivergence U V i ξ +
      h3RawFinOuterProductDivergence U W i ξ := by

  unfold h3RawFinOuterProductDivergence

  simp_rw [
    Pi.add_apply,
    h3RawProductConvolution_add_right,
    mul_add
  ]

  rw [Finset.sum_add_distrib]

/--
The complete raw finite Leray-divergence forcing is additive in its first
vector input.
-/
theorem h3RawFinLerayOuterProductDivergence_add_left
    (U V W : H3SpectralFinVectorState)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    h3RawFinLerayOuterProductDivergence (U + V) W i ξ
      =
    h3RawFinLerayOuterProductDivergence U W i ξ +
      h3RawFinLerayOuterProductDivergence V W i ξ := by

  unfold h3RawFinLerayOuterProductDivergence

  simp_rw [
    h3RawFinOuterProductDivergence_add_left,
    mul_add
  ]

  rw [Finset.sum_add_distrib]

/--
The complete raw finite Leray-divergence forcing is additive in its second
vector input.
-/
theorem h3RawFinLerayOuterProductDivergence_add_right
    (U V W : H3SpectralFinVectorState)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    h3RawFinLerayOuterProductDivergence U (V + W) i ξ
      =
    h3RawFinLerayOuterProductDivergence U V i ξ +
      h3RawFinLerayOuterProductDivergence U W i ξ := by

  unfold h3RawFinLerayOuterProductDivergence

  simp_rw [
    h3RawFinOuterProductDivergence_add_right,
    mul_add
  ]

  rw [Finset.sum_add_distrib]

/-! ## Exact quadratic quotient identity -/

/--
Exact product-rule error identity for the raw finite Leray-divergence form.

The hypotheses deliberately separate the two equivalent quotient relations so
that later specializations can provide them from the concrete selected slope
definition without asking this algebra lemma to normalize real scalar inverses.
-/
theorem h3RawFinLerayOuterProductDivergence_differenceQuotient_productRule_error
    (h : ℝ)
    (U V D R E : H3SpectralFinVectorState)
    (i : Fin 3)
    (ξ : H3FourierPoint3)
    (hQuot :
      (h⁻¹ : ℝ) • (V - U) = D)
    (hStep :
      V - U = h • D)
    (hError :
      E = D - R) :
    (h⁻¹ : ℝ) •
          (
            h3RawFinLerayOuterProductDivergence V V i ξ -
              h3RawFinLerayOuterProductDivergence U U i ξ
          )
        -
      (
        h3RawFinLerayOuterProductDivergence R U i ξ +
          h3RawFinLerayOuterProductDivergence U R i ξ
      )
      =
    h3RawFinLerayOuterProductDivergence E U i ξ +
      h3RawFinLerayOuterProductDivergence U E i ξ +
      h •
        h3RawFinLerayOuterProductDivergence D D i ξ := by

  have hDifference :
      h3RawFinLerayOuterProductDivergence V V i ξ -
          h3RawFinLerayOuterProductDivergence U U i ξ
        =
      h3RawFinLerayOuterProductDivergence (V - U) V i ξ +
        h3RawFinLerayOuterProductDivergence U (V - U) i ξ := by

    rw [
      h3RawFinLerayOuterProductDivergence_sub_left,
      h3RawFinLerayOuterProductDivergence_sub_right
    ]

    ring

  have hScaleLeft :=
    h3RawFinLerayOuterProductDivergence_smul_left_real
      (h⁻¹ : ℝ) (V - U) V i ξ

  have hScaleRight :=
    h3RawFinLerayOuterProductDivergence_smul_right_real
      (h⁻¹ : ℝ) U (V - U) i ξ

  have hV :
      V = h • D + U := by
    exact sub_eq_iff_eq_add.mp hStep

  rw [hDifference, smul_add]

  simp only [Complex.real_smul]

  rw [← hScaleLeft, ← hScaleRight]

  rw [hQuot]

  rw [
    hV,
    h3RawFinLerayOuterProductDivergence_add_right,
    h3RawFinLerayOuterProductDivergence_smul_right_real
  ]

  rw [
    hError,
    h3RawFinLerayOuterProductDivergence_sub_left,
    h3RawFinLerayOuterProductDivergence_sub_right
  ]

  ring

end

end Euclidean
end Bridge
end PrimeTensor
