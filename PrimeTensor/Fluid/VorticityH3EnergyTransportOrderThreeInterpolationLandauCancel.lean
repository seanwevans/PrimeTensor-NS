import PrimeTensor.Fluid.VorticityH3EnergyTransportOrderThreeInterpolationLandauCauchy

/-!
# Third-order H³ interpolation: Landau cancellation

The preceding files have proved the analytic chain

    ∫ g⁴
      ≤
    3 h *
      (∫ (|g|²)²)^(1/2) *
      (∫ |dg|²)^(1/2).

This file performs only normalization and scalar cancellation.

For nonnegative integrals,

    ((∫ g⁴)^(1/2))² = ∫ g⁴.

Hence, after identifying `( |g|² )² = g⁴`, the common half-power can be
cancelled (with a separate zero case) to obtain the actual Landau estimate

    (∫ g⁴)^(1/2)
      ≤
    3 h * (∫ dg²)^(1/2).

This is precisely `‖g‖₄² ≤ 3 h ‖dg‖₂`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory
open scoped ENNReal NNReal

noncomputable local instance axisFintypeH3LandauCancel
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3EnergyDerivative d

noncomputable local instance point3MeasureSpaceH3LandauCancel :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (axisFintypeH3EnergyDerivative Depth.three)
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Pointwise normalization -/

lemma abs_sq_rpow_two_eq_pow_four
    (a : ℝ) :
    (abs a ^ 2) ^ (2 : ℝ) = a ^ 4 := by
  calc
    (abs a ^ 2) ^ (2 : ℝ)
        =
      (abs a ^ 2) ^ (2 : ℕ) := by
        exact Real.rpow_natCast (abs a ^ 2) 2
    _ =
      (a ^ 2) ^ (2 : ℕ) := by
        rw [sq_abs]
    _ = a ^ 4 := by
      ring

lemma abs_rpow_two_eq_sq
    (a : ℝ) :
    (abs a) ^ (2 : ℝ) = a ^ 2 := by
  calc
    (abs a) ^ (2 : ℝ)
        =
      (abs a) ^ (2 : ℕ) := by
        exact Real.rpow_natCast (abs a) 2
    _ = a ^ 2 :=
      sq_abs a

/-! ## Root-form norms used by the Landau cancellation -/

/--
The square of the scalar `L⁴` norm, written in the exact half-power form
produced by Mathlib's real Hölder inequality.
-/
noncomputable def landauL4Squared
    (g : ScalarField3) : ℝ :=
  (
    ∫ x : Point3,
      (g x) ^ 4
  ) ^ (1 / (2 : ℝ))

/--
The scalar `L²` norm, again written in the exact half-power form produced by
Mathlib's real Hölder inequality.
-/
noncomputable def landauL2
    (g : ScalarField3) : ℝ :=
  (
    ∫ x : Point3,
      (g x) ^ 2
  ) ^ (1 / (2 : ℝ))

lemma quartic_integral_nonneg
    (g : ScalarField3) :
    0 ≤
      ∫ x : Point3,
        (g x) ^ 4 := by
  exact
    MeasureTheory.integral_nonneg
      (fun x : Point3 => by positivity)

lemma square_integral_nonneg
    (g : ScalarField3) :
    0 ≤
      ∫ x : Point3,
        (g x) ^ 2 := by
  exact
    MeasureTheory.integral_nonneg
      (fun x : Point3 => by positivity)

lemma landauL4Squared_nonneg
    (g : ScalarField3) :
    0 ≤ landauL4Squared g := by
  unfold landauL4Squared
  exact
    Real.rpow_nonneg
      (quartic_integral_nonneg g)
      _

lemma landauL2_nonneg
    (g : ScalarField3) :
    0 ≤ landauL2 g := by
  unfold landauL2
  exact
    Real.rpow_nonneg
      (square_integral_nonneg g)
      _

lemma landauL4Squared_mul_self
    (g : ScalarField3) :
    landauL4Squared g * landauL4Squared g
      =
    ∫ x : Point3,
      (g x) ^ 4 := by

  have hI :
      0 ≤
        ∫ x : Point3,
          (g x) ^ 4 :=
    quartic_integral_nonneg g

  unfold landauL4Squared

  rw [
    ← Real.rpow_add_of_nonneg
        hI
        (by norm_num : 0 ≤ (1 / (2 : ℝ)))
        (by norm_num : 0 ≤ (1 / (2 : ℝ)))
  ]

  norm_num

/-! ## Normalized Cauchy and quartic bounds -/

theorem landau_cauchy_integral_le_normalized
    {g dg : ScalarField3}
    (hLp : LandauCauchyMemLp g dg) :
    (
      ∫ x : Point3,
        abs (g x) ^ 2 * abs (dg x)
    )
      ≤
    landauL4Squared g * landauL2 dg := by

  have h :=
    landau_cauchy_integral_le
      (g := g)
      (dg := dg)
      hLp

  unfold landauL4Squared landauL2

  simpa only [
    abs_sq_rpow_two_eq_pow_four,
    abs_rpow_two_eq_sq
  ] using h

theorem landau_quartic_integral_le_normalized
    {v g dg : ScalarField3}
    {h : ℝ}
    (hIBP : LandauQuarticIntegrationByParts v g dg)
    (hEnv : LandauScalarEnvelope v h)
    (hInt : LandauQuarticEnvelopeIntegrable v g dg h)
    (hLp : LandauCauchyMemLp g dg) :
    (
      ∫ x : Point3,
        (g x) ^ 4
    )
      ≤
    3 * h * (landauL4Squared g * landauL2 dg) := by

  have hRaw :=
    landau_quartic_integral_le_cauchy_product
      (v := v)
      (g := g)
      (dg := dg)
      (h := h)
      hIBP hEnv hInt hLp

  unfold landauL4Squared landauL2

  simpa only [
    abs_sq_rpow_two_eq_pow_four,
    abs_rpow_two_eq_sq
  ] using hRaw

/-!
The actual one-coordinate Landau inequality.

The proof does not divide by `landauL4Squared g`.  It splits on whether that
quantity is zero, and in the nonzero case uses positivity to cancel it from
both sides.
-/
theorem landau_L4_sq_le_three_mul_envelope_mul_L2
    {v g dg : ScalarField3}
    {h : ℝ}
    (hIBP : LandauQuarticIntegrationByParts v g dg)
    (hEnv : LandauScalarEnvelope v h)
    (hInt : LandauQuarticEnvelopeIntegrable v g dg h)
    (hLp : LandauCauchyMemLp g dg) :
    landauL4Squared g
      ≤
    3 * h * landauL2 dg := by

  have hRaw :
      (
        ∫ x : Point3,
          (g x) ^ 4
      )
        ≤
      3 * h * (landauL4Squared g * landauL2 dg) :=
    landau_quartic_integral_le_normalized
      hIBP hEnv hInt hLp

  have hSquare :
      landauL4Squared g * landauL4Squared g
        =
      ∫ x : Point3,
        (g x) ^ 4 :=
    landauL4Squared_mul_self g

  have hMain :
      landauL4Squared g * landauL4Squared g
        ≤
      3 * h * (landauL4Squared g * landauL2 dg) := by
    rw [hSquare]
    exact hRaw

  have hXnonneg :
      0 ≤ landauL4Squared g :=
    landauL4Squared_nonneg g

  have hYnonneg :
      0 ≤ landauL2 dg :=
    landauL2_nonneg dg

  have hh :
      0 ≤ h :=
    hEnv.1

  by_cases hXzero :
      landauL4Squared g = 0

  · rw [hXzero]
    positivity

  · have hXpos :
        0 < landauL4Squared g :=
      lt_of_le_of_ne
        hXnonneg
        (Ne.symm hXzero)

    have hFactored :
        landauL4Squared g * landauL4Squared g
          ≤
        landauL4Squared g * (3 * h * landauL2 dg) := by
      calc
        landauL4Squared g * landauL4Squared g
            ≤
          3 * h * (landauL4Squared g * landauL2 dg) :=
          hMain
        _ =
          landauL4Squared g * (3 * h * landauL2 dg) := by
          ring

    nlinarith [hFactored]

end Euclidean
end Bridge
end PrimeTensor
