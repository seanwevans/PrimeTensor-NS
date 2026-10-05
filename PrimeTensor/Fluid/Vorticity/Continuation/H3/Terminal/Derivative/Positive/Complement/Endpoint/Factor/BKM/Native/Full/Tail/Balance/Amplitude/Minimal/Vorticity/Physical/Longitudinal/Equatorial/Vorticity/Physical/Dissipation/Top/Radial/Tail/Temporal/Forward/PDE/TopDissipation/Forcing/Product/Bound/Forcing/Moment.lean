import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Bound.Forcing
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Spectral.L1

/-!
# Raw Fourier moments from two neighboring radial L² levels

The radial Leray forcing estimate is expressed using raw `L¹` moments of its
inputs.  For the selected forcing difference quotient we do not want to assume
those moments independently: the preceding arbitrary-radial temporal theorem
already gives strong `L²` control at every natural order.

This file provides the bridge.

The standard inverse Bessel weight

    b(ξ) = (1 + ‖ξ‖²)⁻¹

belongs to `L²(R³)`.  For every natural `p`,

    ‖ξ‖^p
      =
    b(ξ) * (‖ξ‖^p + ‖ξ‖^(p+2)).

Hence, if `G_p` and `G_{p+2}` are Fourier `L²` representatives of

    ‖ξ‖^p F(ξ)
and
    ‖ξ‖^(p+2) F(ξ),

then Cauchy--Schwarz gives

    ∫ ‖ξ‖^p ‖F(ξ)‖
      ≤
    C_Bessel * ‖G_p + G_{p+2}‖₂
      ≤
    C_Bessel * (‖G_p‖₂ + ‖G_{p+2}‖₂).

The same factorization also proves raw moment integrability directly.

For the forthcoming nonlinear difference quotient this is exactly the needed
topology: convergence at radial orders `p` and `p+2` implies convergence of
the raw `p`-moment mass.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3RawMomentFromRadialL2
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1800000

/-! ## Fixed inverse-Bessel constant -/

/-- Complex-valued copy of the standard inverse Bessel weight. -/
def h3StandardInverseBesselWeightComplex
    (ξ : H3FourierPoint3) : ℂ :=
  h3StandardInverseBesselWeight ξ

/-- The complex standard inverse Bessel weight belongs to Fourier `L²`. -/
theorem h3StandardInverseBesselWeightComplex_memLp2 :
    MemLp
      h3StandardInverseBesselWeightComplex
      2
      (volume : Measure H3FourierPoint3) := by
  exact
    h3StandardInverseBesselWeight_memLp2.ofReal

/--
Numerical `L²` factor of the standard inverse Bessel weight.
-/
noncomputable def h3StandardInverseBesselWeightL2Factor : ℝ :=
  Real.sqrt
    (
      ∫ ξ : H3FourierPoint3,
        h3StandardInverseBesselWeight ξ ^ 2
      ∂volume
    )

theorem h3StandardInverseBesselWeightL2Factor_nonneg :
    0 ≤ h3StandardInverseBesselWeightL2Factor :=
  Real.sqrt_nonneg _

/-! ## Exact Bessel factorization -/

/--
The standard inverse Bessel weight converts the sum of the `p` and `p+2`
radial powers exactly back to the `p` radial power.
-/
theorem h3StandardInverseBesselWeight_mul_radial_add_two
    (p : ℕ)
    (ξ : H3FourierPoint3) :
    h3StandardInverseBesselWeight ξ
        *
      (‖ξ‖ ^ p + ‖ξ‖ ^ (p + 2))
      =
    ‖ξ‖ ^ p := by

  let r : ℝ := ‖ξ‖

  have hr0 :
      0 ≤ r := by
    dsimp only [r]
    exact norm_nonneg ξ

  have hden :
      1 + r ^ 2 ≠ 0 := by
    positivity

  unfold h3StandardInverseBesselWeight
  dsimp only [r] at hden ⊢

  rw [pow_add]

  change
    (1 + ‖ξ‖ ^ 2)⁻¹ *
        (‖ξ‖ ^ p + ‖ξ‖ ^ p * ‖ξ‖ ^ 2)
      =
    ‖ξ‖ ^ p

  calc
    (1 + ‖ξ‖ ^ 2)⁻¹ *
        (‖ξ‖ ^ p + ‖ξ‖ ^ p * ‖ξ‖ ^ 2)
        =
      (1 + ‖ξ‖ ^ 2)⁻¹ *
        (‖ξ‖ ^ p * (1 + ‖ξ‖ ^ 2)) := by
      ring
    _ =
      (
        (1 + ‖ξ‖ ^ 2)⁻¹ *
          (1 + ‖ξ‖ ^ 2)
      ) *
        ‖ξ‖ ^ p := by
      ring
    _ =
      ‖ξ‖ ^ p := by
      rw [inv_mul_cancel₀ hden]
      simp

/-! ## Moment integrability from two radial L² representatives -/

/--
If `G_p` and `G_{p+2}` represent the `p` and `p+2` radial weights of a raw
Fourier amplitude `F`, then its raw `p`-moment is integrable.
-/
theorem h3RawFourier_natMoment_integrable_of_two_radialL2
    (p : ℕ)
    (F : H3FourierPoint3 → ℂ)
    (Gp Gp2 : H3FourierComplexL2)
    (hGp :
      ((Gp : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ p : ℝ) : ℂ) * F ξ))
    (hGp2 :
      ((Gp2 : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ (p + 2) : ℝ) : ℂ) * F ξ)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ p * ‖F ξ‖)
      (volume : Measure H3FourierPoint3) := by

  let H : H3FourierComplexL2 :=
    Gp + Gp2

  have hH2 :
      MemLp
        (fun ξ : H3FourierPoint3 =>
          H ξ)
        2
        (volume : Measure H3FourierPoint3) :=
    MeasureTheory.Lp.memLp H

  have hB2 :
      MemLp
        h3StandardInverseBesselWeightComplex
        2
        (volume : Measure H3FourierPoint3) :=
    h3StandardInverseBesselWeightComplex_memLp2

  have hProduct :
      MemLp
        (fun ξ : H3FourierPoint3 =>
          h3StandardInverseBesselWeightComplex ξ *
            H ξ)
        1
        (volume : Measure H3FourierPoint3) :=
    hH2.mul' hB2

  have hProductInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3StandardInverseBesselWeightComplex ξ *
            H ξ)
        (volume : Measure H3FourierPoint3) :=
    MeasureTheory.memLp_one_iff_integrable.mp
      hProduct

  have hHadd :=
    MeasureTheory.Lp.coeFn_add
      Gp Gp2

  have hNormEq :
      (fun ξ : H3FourierPoint3 =>
        ‖h3StandardInverseBesselWeightComplex ξ *
          H ξ‖)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ p * ‖F ξ‖) := by

    filter_upwards [hHadd, hGp, hGp2]
      with ξ hHξ hGpxi hGp2xi

    rw [hHξ]
    simp only [Pi.add_apply]
    rw [hGpxi, hGp2xi]

    have hrp0 :
        0 ≤ ‖ξ‖ ^ p :=
      pow_nonneg (norm_nonneg ξ) p

    have hrp20 :
        0 ≤ ‖ξ‖ ^ (p + 2) :=
      pow_nonneg (norm_nonneg ξ) (p + 2)

    have hsum0 :
        0 ≤ ‖ξ‖ ^ p + ‖ξ‖ ^ (p + 2) :=
      add_nonneg hrp0 hrp20

    have hB0 :
        0 ≤ h3StandardInverseBesselWeight ξ := by
      unfold h3StandardInverseBesselWeight
      positivity

    unfold h3StandardInverseBesselWeightComplex

    rw [← add_mul]

    simp only [
      ← Complex.ofReal_add,
      norm_mul,
      Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg hsum0,
      abs_of_nonneg hB0
    ]

    calc
      h3StandardInverseBesselWeight ξ *
          (
            (‖ξ‖ ^ p + ‖ξ‖ ^ (p + 2)) *
              ‖F ξ‖
          )
          =
        (
          h3StandardInverseBesselWeight ξ *
            (‖ξ‖ ^ p + ‖ξ‖ ^ (p + 2))
        ) *
          ‖F ξ‖ := by
        ring
      _ =
        ‖ξ‖ ^ p * ‖F ξ‖ := by
        rw [
          h3StandardInverseBesselWeight_mul_radial_add_two
        ]

  exact
    hProductInt.norm.congr
      hNormEq

/-! ## Quantitative Cauchy--Schwarz estimate -/

/--
Quantitative raw-moment bound in terms of the two neighboring radial `L²`
states.
-/
theorem integral_h3RawFourier_natMoment_le_bessel_mul_norm_add
    (p : ℕ)
    (F : H3FourierPoint3 → ℂ)
    (Gp Gp2 : H3FourierComplexL2)
    (hGp :
      ((Gp : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ p : ℝ) : ℂ) * F ξ))
    (hGp2 :
      ((Gp2 : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ (p + 2) : ℝ) : ℂ) * F ξ)) :
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ p * ‖F ξ‖
      ∂volume)
      ≤
    h3StandardInverseBesselWeightL2Factor
      *
    ‖Gp + Gp2‖ := by

  let H : H3FourierComplexL2 :=
    Gp + Gp2

  let f : H3FourierPoint3 → ℝ :=
    h3StandardInverseBesselWeight

  let g : H3FourierPoint3 → ℝ :=
    fun ξ => ‖H ξ‖

  have hf :
      MemLp f 2
        (volume : Measure H3FourierPoint3) := by
    dsimp only [f]
    exact
      h3StandardInverseBesselWeight_memLp2

  have hg :
      MemLp g 2
        (volume : Measure H3FourierPoint3) := by
    dsimp only [g]
    exact
      (MeasureTheory.Lp.memLp H).norm

  have hf0 :
      0 ≤ᵐ[(volume : Measure H3FourierPoint3)] f := by
    filter_upwards with ξ
    dsimp only [f]
    unfold h3StandardInverseBesselWeight
    positivity

  have hg0 :
      0 ≤ᵐ[(volume : Measure H3FourierPoint3)] g := by
    filter_upwards with ξ
    dsimp only [g]
    exact norm_nonneg _

  have hTwo :
      ENNReal.ofReal (2 : ℝ)
        =
      (2 : ℝ≥0∞) := by
    norm_num

  have hf' :
      MemLp f (ENNReal.ofReal (2 : ℝ))
        (volume : Measure H3FourierPoint3) := by
    simpa [hTwo] using hf

  have hg' :
      MemLp g (ENNReal.ofReal (2 : ℝ))
        (volume : Measure H3FourierPoint3) := by
    simpa [hTwo] using hg

  have hCauchy :=
    MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := (volume : Measure H3FourierPoint3))
      (p := (2 : ℝ))
      (q := (2 : ℝ))
      (f := f)
      (g := g)
      Real.HolderConjugate.two_two
      hf0 hg0 hf' hg'

  have hHadd :=
    MeasureTheory.Lp.coeFn_add
      Gp Gp2

  have hLeft :
      (∫ ξ : H3FourierPoint3,
        f ξ * g ξ
        ∂volume)
        =
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ p * ‖F ξ‖
        ∂volume := by

    apply integral_congr_ae

    filter_upwards [hHadd, hGp, hGp2]
      with ξ hHξ hGpxi hGp2xi

    dsimp only [f, g, H] at hHξ ⊢

    rw [hHξ]
    simp only [Pi.add_apply]
    rw [hGpxi, hGp2xi]

    have hrp0 :
        0 ≤ ‖ξ‖ ^ p :=
      pow_nonneg (norm_nonneg ξ) p

    have hrp20 :
        0 ≤ ‖ξ‖ ^ (p + 2) :=
      pow_nonneg (norm_nonneg ξ) (p + 2)

    have hsum0 :
        0 ≤ ‖ξ‖ ^ p + ‖ξ‖ ^ (p + 2) :=
      add_nonneg hrp0 hrp20

    rw [← add_mul]

    simp only [
      ← Complex.ofReal_add,
      norm_mul,
      Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg hsum0
    ]

    calc
      h3StandardInverseBesselWeight ξ *
          (
            (‖ξ‖ ^ p + ‖ξ‖ ^ (p + 2)) *
              ‖F ξ‖
          )
          =
        (
          h3StandardInverseBesselWeight ξ *
            (‖ξ‖ ^ p + ‖ξ‖ ^ (p + 2))
        ) *
          ‖F ξ‖ := by
        ring
      _ =
        ‖ξ‖ ^ p * ‖F ξ‖ := by
        rw [
          h3StandardInverseBesselWeight_mul_radial_add_two
        ]

  have hRightBessel :
      (
        ∫ ξ : H3FourierPoint3,
          f ξ ^ (2 : ℝ)
        ∂volume
      ) ^ (1 / (2 : ℝ))
        =
      h3StandardInverseBesselWeightL2Factor := by

    dsimp only [
      f,
      h3StandardInverseBesselWeightL2Factor
    ]

    rw [← Real.sqrt_eq_rpow]

    congr 1

    apply integral_congr_ae
    filter_upwards with ξ

    exact
      Real.rpow_natCast
        (h3StandardInverseBesselWeight ξ)
        2

  have hRightH :
      (
        ∫ ξ : H3FourierPoint3,
          g ξ ^ (2 : ℝ)
        ∂volume
      ) ^ (1 / (2 : ℝ))
        =
      ‖H‖ := by

    have hSq :
        (∫ ξ : H3FourierPoint3,
          ‖H ξ‖ ^ 2
          ∂volume)
          =
        ‖H‖ ^ 2 := by
      exact
        (
          h3FourierComplexL2_norm_sq_eq_integral_norm_sq
            H
        ).symm

    dsimp only [g]

    rw [← Real.sqrt_eq_rpow]

    have hInt :
        (∫ ξ : H3FourierPoint3,
          ‖H ξ‖ ^ (2 : ℝ)
          ∂volume)
          =
        ‖H‖ ^ 2 := by
      calc
        (∫ ξ : H3FourierPoint3,
          ‖H ξ‖ ^ (2 : ℝ)
          ∂volume)
            =
          ∫ ξ : H3FourierPoint3,
            ‖H ξ‖ ^ 2
            ∂volume := by
          apply integral_congr_ae
          filter_upwards with ξ
          exact
            Real.rpow_natCast
              ‖H ξ‖
              2
        _ =
          ‖H‖ ^ 2 :=
          hSq

    rw [hInt]

    simpa only [
      Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg H)
    ]

  rw [
    hLeft,
    hRightBessel,
    hRightH
  ] at hCauchy

  simpa only [H] using hCauchy

/--
A triangle-inequality version convenient for convergence arguments.
-/
theorem integral_h3RawFourier_natMoment_le_bessel_mul_norms
    (p : ℕ)
    (F : H3FourierPoint3 → ℂ)
    (Gp Gp2 : H3FourierComplexL2)
    (hGp :
      ((Gp : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ p : ℝ) : ℂ) * F ξ))
    (hGp2 :
      ((Gp2 : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ (p + 2) : ℝ) : ℂ) * F ξ)) :
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ p * ‖F ξ‖
      ∂volume)
      ≤
    h3StandardInverseBesselWeightL2Factor
      *
    (‖Gp‖ + ‖Gp2‖) := by

  have hBase :=
    integral_h3RawFourier_natMoment_le_bessel_mul_norm_add
      p F Gp Gp2 hGp hGp2

  exact
    hBase.trans
      (
        mul_le_mul_of_nonneg_left
          (norm_add_le Gp Gp2)
          h3StandardInverseBesselWeightL2Factor_nonneg
      )

end

end Euclidean
end Bridge
end PrimeTensor
