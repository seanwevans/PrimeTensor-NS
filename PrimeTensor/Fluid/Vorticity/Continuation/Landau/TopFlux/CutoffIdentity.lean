import PrimeTensor.Fluid.Vorticity.Continuation.Landau.TopFlux.CoordinateIntegrability
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Landau.Analytic.Quartic.BoundaryNorm
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongPoint3DerivativeIntegral

/-!
# Compact-cutoff identity for an integrable three-dimensional divergence

Let `F = (Fₓ,Fᵧ,F_z)` be a spatially `C¹` vector flux whose three scalar
coordinates are integrable, and suppose its total divergence

    ∂ₓFₓ + ∂ᵧFᵧ + ∂_zF_z

is integrable.

For the smooth Landau cutoff `χ_R`, every product `χ_R Fᵢ` is compactly
supported and `C¹`, so its coordinate derivative has zero whole-space
integral.  Summing the three identities and applying the product rule gives

    ∫ χ_R div F
      =
    - ∫ [
        (∂ₓχ_R) Fₓ
          + (∂ᵧχ_R) Fᵧ
          + (∂_zχ_R) F_z
      ].

The important point is that no individual `∂ᵢFᵢ ∈ L¹` assumption appears.
Only the already-recombined total divergence is required to be integrable.
This is the mechanism that avoids a fourth spatial derivative in the
top-order H³ transport flux argument.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set Function
open scoped ENNReal NNReal Topology ContDiff

noncomputable section

noncomputable local instance axisFintypeLandauTopFluxCutoffIdentity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceLandauTopFluxCutoffIdentity :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/--
Compact-cutoff divergence identity on `Point3`.

No coordinate derivative of the uncut flux is assumed integrable
individually.
-/
theorem h3LandauCutoff_integral_divergence_eq_neg_boundary
    {Fx Fy Fz : ScalarField3}
    (hFxC1 : SpatialC1 Fx)
    (hFyC1 : SpatialC1 Fy)
    (hFzC1 : SpatialC1 Fz)
    (hFx : Integrable Fx (volume : Measure Point3))
    (hFy : Integrable Fy (volume : Measure Point3))
    (hFz : Integrable Fz (volume : Measure Point3))
    (hDiv :
      Integrable
        (fun x : Point3 =>
          spatial3.d xAxis Fx x
            +
          (
            spatial3.d yAxis Fy x
              +
            spatial3.d zAxis Fz x
          ))
        (volume : Measure Point3))
    {R : ℝ}
    (hR : 0 < R) :
    (
      ∫ x : Point3,
        h3LandauCutoffBump R hR x
          *
        (
          spatial3.d xAxis Fx x
            +
          (
            spatial3.d yAxis Fy x
              +
            spatial3.d zAxis Fz x
          )
        )
        ∂volume
    )
      =
    -
    (
      ∫ x : Point3,
        (
          spatial3.d
              xAxis
              (fun y : Point3 =>
                h3LandauCutoffBump R hR y)
              x
            *
          Fx x
        )
          +
        (
          (
            spatial3.d
                yAxis
                (fun y : Point3 =>
                  h3LandauCutoffBump R hR y)
                x
              *
            Fy x
          )
            +
          (
            spatial3.d
                zAxis
                (fun y : Point3 =>
                  h3LandauCutoffBump R hR y)
                x
              *
            Fz x
          )
        )
        ∂volume
    ) := by

  let χ : ScalarField3 :=
    fun x : Point3 =>
      h3LandauCutoffBump R hR x

  have hχC1 :
      SpatialC1 χ := by
    dsimp only [χ]
    exact h3LandauCutoffBump_spatialC1 hR

  have hχBound :
      ∀ x : Point3,
        ‖χ x‖ ≤ (1 : ℝ) := by
    intro x
    dsimp only [χ]
    rw [
      Real.norm_eq_abs,
      abs_of_nonneg
        (h3LandauCutoffBump_nonneg hR x)
    ]
    exact
      h3LandauCutoffBump_le_one hR x

  obtain ⟨C, hC⟩ :=
    exists_uniform_norm_fderiv_h3LandauCutoffBump_axisDirection_le_div

  have hDχBound :
      ∀
        (a : Axis Depth.three)
        (x : Point3),
          ‖spatial3.d a χ x‖
            ≤
          (C : ℝ) / R := by
    intro a x

    change
      ‖partialDeriv a χ x‖
        ≤
      (C : ℝ) / R

    rw [
      hχC1.partialDeriv_eq_fderiv_axisDirection
        x a
    ]

    dsimp only [χ]

    exact hC hR a x

  have hDχMeas :
      ∀ a : Axis Depth.three,
        AEStronglyMeasurable
          (spatial3.d a χ)
          (volume : Measure Point3) := by
    intro a
    exact
      (
        h3SpatialC1_spatial3_d_continuous_weakPressure
          hχC1 a
      ).aestronglyMeasurable

  have hBoundaryInt
      (a : Axis Depth.three)
      (F : ScalarField3)
      (hF : Integrable F (volume : Measure Point3)) :
      Integrable
        (fun x : Point3 =>
          spatial3.d a χ x * F x)
        (volume : Measure Point3) := by
    exact
      hF.bdd_mul
        (hDχMeas a)
        (
          Filter.Eventually.of_forall
            (hDχBound a)
        )

  have hBulkInt
      (a : Axis Depth.three)
      (F : ScalarField3)
      (hFC1 : SpatialC1 F) :
      Integrable
        (fun x : Point3 =>
          χ x * spatial3.d a F x)
        (volume : Measure Point3) := by
    have hDFContinuous :
        Continuous
          (spatial3.d a F) :=
      h3SpatialC1_spatial3_d_continuous_weakPressure
        hFC1 a

    exact
      (
        hχC1.continuous.mul
          hDFContinuous
      ).integrable_of_hasCompactSupport
        (
          (h3LandauCutoffBump_hasCompactSupport hR).mul_right
        )

  have hCutoffInt
      (F : ScalarField3)
      (hF : Integrable F (volume : Measure Point3)) :
      Integrable
        (fun x : Point3 =>
          χ x * F x)
        (volume : Measure Point3) := by
    exact
      hF.bdd_mul
        hχC1.continuous.aestronglyMeasurable
        (
          Filter.Eventually.of_forall
            hχBound
        )

  have hCutoffDerivInt
      (a : Axis Depth.three)
      (F : ScalarField3)
      (hFC1 : SpatialC1 F)
      (hF : Integrable F (volume : Measure Point3)) :
      Integrable
        (
          spatial3.d
            a
            (fun x : Point3 =>
              χ x * F x)
        )
        (volume : Measure Point3) := by

    have hBoundary :=
      hBoundaryInt a F hF

    have hBulk :=
      hBulkInt a F hFC1

    have hRhs :
        Integrable
          (fun x : Point3 =>
            spatial3.d a χ x * F x
              +
            χ x * spatial3.d a F x)
          (volume : Measure Point3) :=
      hBoundary.add hBulk

    have hPointwise :
        spatial3.d
            a
            (fun x : Point3 =>
              χ x * F x)
          =
        fun x : Point3 =>
          spatial3.d a χ x * F x
            +
          χ x * spatial3.d a F x := by
      funext x
      exact
        SpatialC1.spatial3_d_mul
          hχC1 hFC1 x a

    rw [hPointwise]

    exact hRhs

  have hZero
      (a : Axis Depth.three)
      (F : ScalarField3)
      (hFC1 : SpatialC1 F)
      (hF : Integrable F (volume : Measure Point3)) :
      (
        ∫ x : Point3,
          spatial3.d
            a
            (fun y : Point3 =>
              χ y * F y)
            x
          ∂volume
      )
        =
      0 := by

    have hProductC1 :
        SpatialC1
          (fun x : Point3 =>
            χ x * F x) :=
      hχC1.mul hFC1

    exact
      integral_spatial3_d_eq_zero_of_integrable
        hProductC1
        a
        (hCutoffInt F hF)
        (hCutoffDerivInt a F hFC1 hF)

  have hZeroX :=
    hZero xAxis Fx hFxC1 hFx

  have hZeroY :=
    hZero yAxis Fy hFyC1 hFy

  have hZeroZ :=
    hZero zAxis Fz hFzC1 hFz

  have hDX :=
    hCutoffDerivInt xAxis Fx hFxC1 hFx

  have hDY :=
    hCutoffDerivInt yAxis Fy hFyC1 hFy

  have hDZ :=
    hCutoffDerivInt zAxis Fz hFzC1 hFz

  have hDerivativeSum :
      Integrable
        (fun x : Point3 =>
          spatial3.d
              xAxis
              (fun y : Point3 =>
                χ y * Fx y)
              x
            +
          (
            spatial3.d
                yAxis
                (fun y : Point3 =>
                  χ y * Fy y)
                x
              +
            spatial3.d
                zAxis
                (fun y : Point3 =>
                  χ y * Fz y)
                x
          ))
        (volume : Measure Point3) :=
    hDX.add (hDY.add hDZ)

  have hYZIntegral :
      (
        ∫ x : Point3,
          spatial3.d
              yAxis
              (fun y : Point3 =>
                χ y * Fy y)
              x
            +
          spatial3.d
              zAxis
              (fun y : Point3 =>
                χ y * Fz y)
              x
          ∂volume
      )
        =
      (
        ∫ x : Point3,
          spatial3.d
            yAxis
            (fun y : Point3 =>
              χ y * Fy y)
            x
          ∂volume
      )
        +
      (
        ∫ x : Point3,
          spatial3.d
            zAxis
            (fun y : Point3 =>
              χ y * Fz y)
            x
          ∂volume
      ) := by
    simpa only [Pi.add_apply] using
      (MeasureTheory.integral_add hDY hDZ)

  have hXYZIntegral :
      (
        ∫ x : Point3,
          spatial3.d
              xAxis
              (fun y : Point3 =>
                χ y * Fx y)
              x
            +
          (
            spatial3.d
                yAxis
                (fun y : Point3 =>
                  χ y * Fy y)
                x
              +
            spatial3.d
                zAxis
                (fun y : Point3 =>
                  χ y * Fz y)
                x
          )
          ∂volume
      )
        =
      (
        ∫ x : Point3,
          spatial3.d
            xAxis
            (fun y : Point3 =>
              χ y * Fx y)
            x
          ∂volume
      )
        +
      (
        ∫ x : Point3,
          spatial3.d
              yAxis
              (fun y : Point3 =>
                χ y * Fy y)
              x
            +
          spatial3.d
              zAxis
              (fun y : Point3 =>
                χ y * Fz y)
              x
          ∂volume
      ) := by
    simpa only [Pi.add_apply] using
      (MeasureTheory.integral_add
        hDX
        (hDY.add hDZ))

  have hDerivativeSumIntegral :
      (
        ∫ x : Point3,
          spatial3.d
              xAxis
              (fun y : Point3 =>
                χ y * Fx y)
              x
            +
          (
            spatial3.d
                yAxis
                (fun y : Point3 =>
                  χ y * Fy y)
                x
              +
            spatial3.d
                zAxis
                (fun y : Point3 =>
                  χ y * Fz y)
                x
          )
          ∂volume
      )
        =
      0 := by
    rw [
      hXYZIntegral,
      hYZIntegral,
      hZeroX,
      hZeroY,
      hZeroZ
    ]
    ring

  have hBoundaryX :=
    hBoundaryInt xAxis Fx hFx

  have hBoundaryY :=
    hBoundaryInt yAxis Fy hFy

  have hBoundaryZ :=
    hBoundaryInt zAxis Fz hFz

  have hBoundarySum :
      Integrable
        (fun x : Point3 =>
          spatial3.d xAxis χ x * Fx x
            +
          (
            spatial3.d yAxis χ x * Fy x
              +
            spatial3.d zAxis χ x * Fz x
          ))
        (volume : Measure Point3) :=
    hBoundaryX.add
      (hBoundaryY.add hBoundaryZ)

  have hWeightedDiv :
      Integrable
        (fun x : Point3 =>
          χ x
            *
          (
            spatial3.d xAxis Fx x
              +
            (
              spatial3.d yAxis Fy x
                +
              spatial3.d zAxis Fz x
            )
          ))
        (volume : Measure Point3) :=
    hDiv.bdd_mul
      hχC1.continuous.aestronglyMeasurable
      (
        Filter.Eventually.of_forall
          hχBound
      )

  have hExpansion :
      (
        fun x : Point3 =>
          spatial3.d
              xAxis
              (fun y : Point3 =>
                χ y * Fx y)
              x
            +
          (
            spatial3.d
                yAxis
                (fun y : Point3 =>
                  χ y * Fy y)
                x
              +
            spatial3.d
                zAxis
                (fun y : Point3 =>
                  χ y * Fz y)
                x
          )
      )
        =
      (
        fun x : Point3 =>
          χ x
            *
          (
            spatial3.d xAxis Fx x
              +
            (
              spatial3.d yAxis Fy x
                +
              spatial3.d zAxis Fz x
            )
          )
            +
          (
            spatial3.d xAxis χ x * Fx x
              +
            (
              spatial3.d yAxis χ x * Fy x
                +
              spatial3.d zAxis χ x * Fz x
            )
          )
      ) := by
    funext x

    rw [
      SpatialC1.spatial3_d_mul
        hχC1 hFxC1 x xAxis,
      SpatialC1.spatial3_d_mul
        hχC1 hFyC1 x yAxis,
      SpatialC1.spatial3_d_mul
        hχC1 hFzC1 x zAxis
    ]

    ring

  have hDerivativeSumIntegral' :
      (
        ∫ x : Point3,
          χ x
            *
          (
            spatial3.d xAxis Fx x
              +
            (
              spatial3.d yAxis Fy x
                +
              spatial3.d zAxis Fz x
            )
          )
            +
          (
            spatial3.d xAxis χ x * Fx x
              +
            (
              spatial3.d yAxis χ x * Fy x
                +
              spatial3.d zAxis χ x * Fz x
            )
          )
          ∂volume
      )
        =
      0 := by
    calc
      (
        ∫ x : Point3,
          χ x
            *
          (
            spatial3.d xAxis Fx x
              +
            (
              spatial3.d yAxis Fy x
                +
              spatial3.d zAxis Fz x
            )
          )
            +
          (
            spatial3.d xAxis χ x * Fx x
              +
            (
              spatial3.d yAxis χ x * Fy x
                +
              spatial3.d zAxis χ x * Fz x
            )
          )
          ∂volume
      )
          =
        ∫ x : Point3,
          spatial3.d
              xAxis
              (fun y : Point3 =>
                χ y * Fx y)
              x
            +
          (
            spatial3.d
                yAxis
                (fun y : Point3 =>
                  χ y * Fy y)
                x
              +
            spatial3.d
                zAxis
                (fun y : Point3 =>
                  χ y * Fz y)
                x
          )
          ∂volume := by
            apply integral_congr_ae
            exact
              Filter.Eventually.of_forall
                (fun x =>
                  (congrFun hExpansion x).symm)

      _ = 0 :=
        hDerivativeSumIntegral

  rw [
    MeasureTheory.integral_add
      hWeightedDiv
      hBoundarySum
  ] at hDerivativeSumIntegral'

  dsimp only [χ] at hDerivativeSumIntegral' ⊢

  linarith

end

end Euclidean
end Bridge
end PrimeTensor
