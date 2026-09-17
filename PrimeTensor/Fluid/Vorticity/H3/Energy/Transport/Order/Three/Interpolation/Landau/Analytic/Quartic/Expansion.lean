import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Landau.Analytic.Quartic.CutoffIBP

/-!
# Expansion of the compact-cutoff quartic Landau identity

The raw cutoff integration-by-parts theorem works with Fréchet derivatives.
Here we identify those derivatives with the concrete Landau quantities.

For `g = ∂ₐv`,

    Dₐ(g³) = 3 g² ∂ₐg

and

    Dₐ(χ_R v) = χ_R g + v Dₐχ_R.

Substitution into the raw compact-support identity gives

    ∫ χ_R g⁴
      =
    -3 ∫ (χ_R v) (g² ∂ₐg)
      - ∫ (Dₐχ_R) (v g³).

The last integral is the sole cutoff boundary error.  The next step is to
show it tends to zero as `R → ∞`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Function MeasureTheory
open scoped ENNReal NNReal Topology ContDiff

noncomputable section

noncomputable local instance axisFintypeH3LandauQuarticExpansion
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Directional derivative of the cubic Landau factor. -/
theorem fderiv_h3LandauQuarticCube_axisDirection
    {g : ScalarField3}
    (hg : SpatialC1 g)
    (a : Axis Depth.three)
    (x : Point3) :
    fderiv ℝ
        (h3LandauQuarticCube g)
        x
        (axisDirection a)
      =
    3 * (g x) ^ 2
      * (spatial3.d a g x) := by
  unfold h3LandauQuarticCube

  rw [
    fderiv_fun_pow
      3
      (hg.differentiable_one.differentiableAt)
  ]

  have hPartial :=
    hg.partialDeriv_eq_fderiv_axisDirection
      x a

  simpa [
    nsmul_eq_mul,
    smul_eq_mul,
    spatial3,
    spatial,
    hPartial,
    mul_assoc
  ]

/-- Directional derivative of the cutoff product. -/
theorem fderiv_h3LandauQuarticCutoffFactor_axisDirection
    {R : ℝ}
    (hR : 0 < R)
    {v : ScalarField3}
    (hv : SpatialC1 v)
    (a : Axis Depth.three)
    (x : Point3) :
    fderiv ℝ
        (h3LandauQuarticCutoffFactor R hR v)
        x
        (axisDirection a)
      =
    h3LandauCutoffBump R hR x
        * (spatial3.d a v x)
      +
    v x
        *
    fderiv ℝ
        (fun y : Point3 =>
          h3LandauCutoffBump R hR y)
        x
        (axisDirection a) := by
  unfold h3LandauQuarticCutoffFactor

  have hCutoffDiff :
      DifferentiableAt ℝ
        (fun y : Point3 =>
          h3LandauCutoffBump R hR y)
        x :=
    (h3LandauCutoffBump_spatialC1 hR).differentiable_one.differentiableAt

  have hVDiff :
      DifferentiableAt ℝ v x :=
    hv.differentiable_one.differentiableAt

  rw [
    fderiv_fun_mul
      hCutoffDiff
      hVDiff
  ]

  have hPartial :=
    hv.partialDeriv_eq_fderiv_axisDirection
      x a

  simpa [
    smul_eq_mul,
    spatial3,
    spatial,
    hPartial,
    mul_assoc
  ]

/-- Explicit compact-cutoff quartic identity.  The final integral is the only
boundary error created by the cutoff. -/
theorem h3LandauQuarticCutoff_expandedIBP
    {R : ℝ}
    (hR : 0 < R)
    {v g : ScalarField3}
    (hv : SpatialC1 v)
    (hg : SpatialC1 g)
    (a : Axis Depth.three)
    (hvg :
      ∀ x : Point3,
        spatial3.d a v x = g x) :
    (
      ∫ x : Point3,
        h3LandauCutoffBump R hR x
          *
        (g x) ^ 4
    )
      =
    -3 *
      (
        ∫ x : Point3,
          (
            h3LandauCutoffBump R hR x
              *
            v x
          )
            *
          (
            (g x) ^ 2
              *
            spatial3.d a g x
          )
      )
      -
    (
      ∫ x : Point3,
        fderiv ℝ
            (fun y : Point3 =>
              h3LandauCutoffBump R hR y)
            x
            (axisDirection a)
          *
        (
          v x * (g x) ^ 3
        )
    ) := by
  have hRaw :=
    h3LandauQuarticCutoff_rawIBP
      hR hv hg a

  simp_rw [
    fderiv_h3LandauQuarticCube_axisDirection
      hg a,
    fderiv_h3LandauQuarticCutoffFactor_axisDirection
      hR hv a
  ] at hRaw

  simp only [
    h3LandauQuarticCutoffFactor,
    h3LandauQuarticCube
  ] at hRaw

  simp_rw [hvg] at hRaw

  have hLeft :
      (
        ∫ x : Point3,
          (
            h3LandauCutoffBump R hR x
              *
            v x
          )
            *
          (
            3 * (g x) ^ 2
              *
            spatial3.d a g x
          )
      )
        =
      3 *
        (
          ∫ x : Point3,
            (
              h3LandauCutoffBump R hR x
                *
              v x
            )
              *
            (
              (g x) ^ 2
                *
              spatial3.d a g x
            )
        ) := by
    rw [← MeasureTheory.integral_const_mul]

    apply integral_congr_ae

    filter_upwards with x

    ring

  have hQuarticInt :
      MeasureTheory.Integrable
        (fun x : Point3 =>
          h3LandauCutoffBump R hR x
            *
          (g x) ^ 4)
        volume := by
    exact
      (
        (h3LandauCutoffBump_spatialC1 hR).continuous.mul
          (hg.continuous.pow 4)
      ).integrable_of_hasCompactSupport
        (
          (h3LandauCutoffBump_hasCompactSupport hR).mul_right
        )

  have hDChiContinuous :
      Continuous
        (fun x : Point3 =>
          fderiv ℝ
              (fun y : Point3 =>
                h3LandauCutoffBump R hR y)
              x
              (axisDirection a)) :=
    (
      (h3LandauCutoffBump_spatialC1 hR).continuous_fderiv
        (by norm_num)
    ).clm_apply
      continuous_const

  have hDChiSupport :
      HasCompactSupport
        (fun x : Point3 =>
          fderiv ℝ
              (fun y : Point3 =>
                h3LandauCutoffBump R hR y)
              x
              (axisDirection a)) :=
    hasCompactSupport_fderiv_apply
      (h3LandauCutoffBump_hasCompactSupport hR)
      (axisDirection a)

  have hBoundaryInt :
      MeasureTheory.Integrable
        (fun x : Point3 =>
          fderiv ℝ
              (fun y : Point3 =>
                h3LandauCutoffBump R hR y)
              x
              (axisDirection a)
            *
          (
            v x * (g x) ^ 3
          ))
        volume := by
    exact
      (
        hDChiContinuous.mul
          (
            hv.continuous.mul
              (hg.continuous.pow 3)
          )
      ).integrable_of_hasCompactSupport
        hDChiSupport.mul_right

  have hRight :
      (
        ∫ x : Point3,
          (
            h3LandauCutoffBump R hR x
                *
              g x
              +
            v x
                *
              fderiv ℝ
                  (fun y : Point3 =>
                    h3LandauCutoffBump R hR y)
                  x
                  (axisDirection a)
          )
            *
          (g x) ^ 3
      )
        =
      (
        ∫ x : Point3,
          h3LandauCutoffBump R hR x
            *
          (g x) ^ 4
      )
        +
      (
        ∫ x : Point3,
          fderiv ℝ
              (fun y : Point3 =>
                h3LandauCutoffBump R hR y)
              x
              (axisDirection a)
            *
          (
            v x * (g x) ^ 3
          )
      ) := by
    calc
      (
        ∫ x : Point3,
          (
            h3LandauCutoffBump R hR x
                *
              g x
              +
            v x
                *
              fderiv ℝ
                  (fun y : Point3 =>
                    h3LandauCutoffBump R hR y)
                  x
                  (axisDirection a)
          )
            *
          (g x) ^ 3
      )
          =
        ∫ x : Point3,
          (
            h3LandauCutoffBump R hR x
              *
            (g x) ^ 4
          )
            +
          (
            fderiv ℝ
                (fun y : Point3 =>
                  h3LandauCutoffBump R hR y)
                x
                (axisDirection a)
              *
            (
              v x * (g x) ^ 3
            )
          ) := by
            apply integral_congr_ae

            filter_upwards with x

            ring

      _ =
        (
          ∫ x : Point3,
            h3LandauCutoffBump R hR x
              *
            (g x) ^ 4
        )
          +
        (
          ∫ x : Point3,
            fderiv ℝ
                (fun y : Point3 =>
                  h3LandauCutoffBump R hR y)
                x
                (axisDirection a)
              *
            (
              v x * (g x) ^ 3
            )
        ) := by
          exact
            MeasureTheory.integral_add
              hQuarticInt
              hBoundaryInt

  rw [
    hLeft,
    hRight
  ] at hRaw

  linarith

end

end Euclidean
end Bridge
end PrimeTensor
