import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Holder.Landau

/-!
# Third-order H³ interpolation: Landau scalar algebra

This file contains the purely real-variable inequality needed after the analytic
Landau estimates have been established.

If

    G² ≤ 3 h B
    Q² ≤ 3 h C

and the three third-derivative L² magnitudes satisfy

    A² + B² + C² ≤ E,

then

    2 A G Q ≤ 3 h E.

The proof deliberately avoids square roots.  It uses only the elementary
inequalities `2 G Q ≤ G² + Q²` and `2 A B ≤ A² + B²`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/--
Pure scalar closure of the two Landau `L⁴` estimates and the three-factor
Hölder product.
-/
theorem landau_three_factor_algebra
    {A B C G Q h E : ℝ}
    (hA : 0 ≤ A)
    (hB : 0 ≤ B)
    (hC : 0 ≤ C)
    (hG : 0 ≤ G)
    (hQ : 0 ≤ Q)
    (hh : 0 ≤ h)
    (hG2 : G ^ 2 ≤ 3 * h * B)
    (hQ2 : Q ^ 2 ≤ 3 * h * C)
    (hEnergy : A ^ 2 + B ^ 2 + C ^ 2 ≤ E) :
    2 * A * G * Q ≤ 3 * h * E := by

  have hGQ :
      2 * G * Q ≤ 3 * h * (B + C) := by

    have hYoungGQ :
        2 * G * Q ≤ G ^ 2 + Q ^ 2 := by
      nlinarith [sq_nonneg (G - Q)]

    have hSum :
        G ^ 2 + Q ^ 2
          ≤
        3 * h * B + 3 * h * C :=
      add_le_add hG2 hQ2

    calc
      2 * G * Q
          ≤ G ^ 2 + Q ^ 2 :=
        hYoungGQ
      _ ≤ 3 * h * B + 3 * h * C :=
        hSum
      _ = 3 * h * (B + C) := by
        ring

  have hAB :
      2 * A * B ≤ A ^ 2 + B ^ 2 := by
    nlinarith [sq_nonneg (A - B)]

  have hAC :
      2 * A * C ≤ A ^ 2 + C ^ 2 := by
    nlinarith [sq_nonneg (A - C)]

  have hABC :
      A * (B + C) ≤ E := by

    have hTwice :
        2 * A * (B + C)
          ≤
        2 * A ^ 2 + B ^ 2 + C ^ 2 := by
      nlinarith [hAB, hAC]

    have hEnergyNonneg :
        0 ≤ A ^ 2 + B ^ 2 + C ^ 2 := by
      positivity

    have hUpper :
        2 * A ^ 2 + B ^ 2 + C ^ 2
          ≤
        2 * E := by
      nlinarith [hEnergy, hEnergyNonneg]

    nlinarith [hTwice, hUpper]

  have hScaleGQ :
      2 * A * G * Q
        ≤
      3 * h * (A * (B + C)) := by

    have hMul :=
      mul_le_mul_of_nonneg_left
        hGQ
        hA

    nlinarith [hMul]

  have hScaleEnergy :
      3 * h * (A * (B + C))
        ≤
      3 * h * E :=
    mul_le_mul_of_nonneg_left
      hABC
      (mul_nonneg (by norm_num) hh)

  exact
    le_trans
      hScaleGQ
      hScaleEnergy

end Euclidean
end Bridge
end PrimeTensor
