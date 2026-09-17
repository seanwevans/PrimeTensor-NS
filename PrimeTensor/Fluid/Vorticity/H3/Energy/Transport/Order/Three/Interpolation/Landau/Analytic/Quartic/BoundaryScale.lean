import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Landau.Analytic.Quartic.BoundaryReal

/-!
# Scale normalization for the quartic cutoff boundary derivative

The real `L⁴` estimate from `BoundaryReal` is

    ‖Dχ_R eₐ‖₄
      ≤ (C / R) · volume(closedBall 0 (2R))^(1/4).

The Haar scaling identity proved in `BoundaryNorm` turns the ball factor into
an explicit three-dimensional power.  This file performs only that algebra and
packages the estimate in the scale-normalized form

    ‖Dχ_R eₐ‖₄ ≤ K · R^(-1/4).

The following increment can then send the right-hand side to zero at infinity
without reopening any measure-theoretic bookkeeping.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Function MeasureTheory Filter
open scoped ENNReal NNReal Topology ContDiff

noncomputable section

noncomputable local instance axisFintypeH3LandauQuarticBoundaryScale
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The inverse radius multiplied by its `3/4` power is the expected
`-1/4` power. -/
theorem inv_mul_three_quarter_rpow_eq_neg_quarter_rpow
    {R : ℝ}
    (hR : 0 < R) :
    R⁻¹ * R ^ ((3 : ℝ) / 4)
      =
    R ^ (-(1 : ℝ) / 4) := by
  calc
    R⁻¹ * R ^ ((3 : ℝ) / 4)
        =
      R ^ (-(1 : ℝ)) * R ^ ((3 : ℝ) / 4) := by
        rw [Real.rpow_neg_one]

    _ =
      R ^ (-(1 : ℝ) + (3 : ℝ) / 4) := by
        rw [Real.rpow_add hR]

    _ =
      R ^ (-(1 : ℝ) / 4) := by
        congr 1
        ring

/-- A cubic ordinary power followed by a quarter real power is the `3/4`
real power on a nonnegative base. -/
theorem pow_three_rpow_quarter_eq_rpow_three_quarter
    {R : ℝ}
    (hR : 0 ≤ R) :
    (R ^ 3) ^ ((1 : ℝ) / 4)
      =
    R ^ ((3 : ℝ) / 4) := by
  calc
    (R ^ 3) ^ ((1 : ℝ) / 4)
        =
      (R ^ (3 : ℝ)) ^ ((1 : ℝ) / 4) := by
        congr 1
        exact
          (Real.rpow_natCast R 3).symm

    _ =
      R ^ ((3 : ℝ) * ((1 : ℝ) / 4)) := by
        rw [← Real.rpow_mul hR]

    _ =
      R ^ ((3 : ℝ) / 4) := by
        congr 1
        ring

/-- The quantitative real `L⁴` cutoff derivative estimate has exactly
`R^(-1/4)` decay in dimension three. -/
theorem exists_uniform_lpNorm_four_fderiv_h3LandauCutoffBump_axisDirection_le_rpow :
    ∃ K : ℝ,
      0 ≤ K
        ∧
      ∀ {R : ℝ}
        (hR : 0 < R)
        (a : Axis Depth.three),
        lpNorm
            (fun x : Point3 =>
              fderiv ℝ
                  (fun y : Point3 =>
                    h3LandauCutoffBump R hR y)
                  x
                  (axisDirection a))
            4
            volume
          ≤
        K * R ^ (-(1 : ℝ) / 4) := by
  obtain ⟨C, hC⟩ :=
    exists_uniform_lpNorm_four_fderiv_h3LandauCutoffBump_axisDirection_le

  let V : ℝ :=
    (
      volume
        (
          Metric.closedBall
            (0 : Point3)
            1
        )
    ).toReal

  let K : ℝ :=
    (C : ℝ)
      *
    (2 : ℝ) ^ ((3 : ℝ) / 4)
      *
    V ^ ((1 : ℝ) / 4)

  have hV :
      0 ≤ V := by
    dsimp [V]
    exact ENNReal.toReal_nonneg

  have hK :
      0 ≤ K := by
    dsimp [K]
    exact
      mul_nonneg
        (
          mul_nonneg
            C.coe_nonneg
            (Real.rpow_nonneg (by norm_num) _)
        )
        (Real.rpow_nonneg hV _)

  refine ⟨K, hK, ?_⟩

  intro R hR a

  have hBound :=
    hC hR a

  rw [
    volume_closedBall_point3_two_mul hR
  ] at hBound

  have hTwoR :
      0 ≤ 2 * R := by
    positivity

  have hCube :
      0 ≤ (2 * R) ^ 3 :=
    pow_nonneg hTwoR 3

  rw [
    ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hCube
  ] at hBound

  have hPow :
      ((2 * R) ^ 3) ^ ((1 : ℝ) / 4)
        =
      (2 * R) ^ ((3 : ℝ) / 4) :=
    pow_three_rpow_quarter_eq_rpow_three_quarter
      hTwoR

  have hSplit :
      (2 * R) ^ ((3 : ℝ) / 4)
        =
      (2 : ℝ) ^ ((3 : ℝ) / 4)
        *
      R ^ ((3 : ℝ) / 4) := by
    exact
      Real.mul_rpow
        (by norm_num)
        hR.le

  have hInv :
      R⁻¹ * R ^ ((3 : ℝ) / 4)
        =
      R ^ (-(1 : ℝ) / 4) :=
    inv_mul_three_quarter_rpow_eq_neg_quarter_rpow
      hR

  have hScale :
      ((C : ℝ) / R)
          *
        (
          ((2 * R) ^ 3) * V
        ) ^ ((1 : ℝ) / 4)
        =
      K * R ^ (-(1 : ℝ) / 4) := by
    rw [
      Real.mul_rpow
        hCube
        hV,
      hPow,
      hSplit,
      div_eq_mul_inv
    ]

    dsimp [K]

    calc
      (C : ℝ)
            * R⁻¹
            *
          (
            (2 : ℝ) ^ ((3 : ℝ) / 4)
              *
            R ^ ((3 : ℝ) / 4)
              *
            V ^ ((1 : ℝ) / 4)
          )
          =
        (
          (C : ℝ)
            *
          (2 : ℝ) ^ ((3 : ℝ) / 4)
            *
          V ^ ((1 : ℝ) / 4)
        )
          *
        (
          R⁻¹ * R ^ ((3 : ℝ) / 4)
        ) := by
          ring

      _ =
        (
          (C : ℝ)
            *
          (2 : ℝ) ^ ((3 : ℝ) / 4)
            *
          V ^ ((1 : ℝ) / 4)
        )
          *
        R ^ (-(1 : ℝ) / 4) := by
          rw [hInv]

  have hBound' :
      lpNorm
          (fun x : Point3 =>
            fderiv ℝ
                (fun y : Point3 =>
                  h3LandauCutoffBump R hR y)
                x
                (axisDirection a))
          4
          volume
        ≤
      ((C : ℝ) / R)
        *
      (
        ((2 * R) ^ 3) * V
      ) ^ ((1 : ℝ) / 4) := by
    simpa [V] using
      hBound

  exact
    hBound'.trans_eq
      hScale

end

end Euclidean
end Bridge
end PrimeTensor
