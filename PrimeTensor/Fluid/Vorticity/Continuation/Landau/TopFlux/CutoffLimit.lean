import PrimeTensor.Fluid.Vorticity.Continuation.Landau.TopFlux.CutoffIdentity
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Landau.Analytic.Quartic.CutoffLimit

/-!
# Removing the top-flux cutoff at infinity

`CutoffIdentity` proved, for every positive radius,

    ∫ χ_R div F = -∫ ∇χ_R · F,

under only

    Fₓ,Fᵧ,F_z ∈ C¹ ∩ L¹,
    div F ∈ L¹.

This file sends the canonical radii `Rₙ = n+1` to infinity.

The left side converges to `∫ div F` by the repository's generic dominated
convergence theorem for the Landau cutoff.

For each boundary coordinate,

    |(∂ᵢχ_R) Fᵢ|
      ≤ (C/R) |Fᵢ|,

and `Fᵢ ∈ L¹`.  Dominated convergence therefore sends every boundary
coordinate integral to zero.  Uniqueness of limits yields

    ∫ div F = 0.

No individual derivative `∂ᵢFᵢ` is assumed integrable.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set Function
open scoped ENNReal NNReal Topology ContDiff

noncomputable section

noncomputable local instance axisFintypeLandauTopFluxCutoffLimit
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/--
One coordinate of the cutoff-gradient boundary term tends to zero against any
integrable scalar field.
-/
theorem tendsto_h3LandauTopFluxBoundaryCoordinateIntegral_zero
    {F : ScalarField3}
    (hF : Integrable F (volume : Measure Point3))
    (a : Axis Depth.three) :
    Tendsto
      (
        fun n : ℕ =>
          ∫ x : Point3,
            spatial3.d
                a
                (
                  fun y : Point3 =>
                    h3LandauCutoffBump
                      (h3LandauQuarticRadius n)
                      (h3LandauQuarticRadius_pos n)
                      y
                )
                x
              *
            F x
          ∂volume
      )
      atTop
      (𝓝 0) := by

  obtain ⟨C, hC⟩ :=
    exists_uniform_norm_fderiv_h3LandauCutoffBump_axisDirection_le_div

  let B : ℕ → Point3 → ℝ :=
    fun n x =>
      spatial3.d
          a
          (
            fun y : Point3 =>
              h3LandauCutoffBump
                (h3LandauQuarticRadius n)
                (h3LandauQuarticRadius_pos n)
                y
          )
          x
        *
      F x

  have hDerivativeBound :
      ∀ (n : ℕ) (x : Point3),
        ‖spatial3.d
            a
            (
              fun y : Point3 =>
                h3LandauCutoffBump
                  (h3LandauQuarticRadius n)
                  (h3LandauQuarticRadius_pos n)
                  y
            )
            x‖
          ≤
        (C : ℝ) / h3LandauQuarticRadius n := by
    intro n x

    have hC1 :
        SpatialC1
          (
            fun y : Point3 =>
              h3LandauCutoffBump
                (h3LandauQuarticRadius n)
                (h3LandauQuarticRadius_pos n)
                y
          ) :=
      h3LandauCutoffBump_spatialC1
        (h3LandauQuarticRadius_pos n)

    change
      ‖partialDeriv
          a
          (
            fun y : Point3 =>
              h3LandauCutoffBump
                (h3LandauQuarticRadius n)
                (h3LandauQuarticRadius_pos n)
                y
          )
          x‖
        ≤
      (C : ℝ) / h3LandauQuarticRadius n

    rw [
      hC1.partialDeriv_eq_fderiv_axisDirection
        x a
    ]

    exact
      hC
        (h3LandauQuarticRadius_pos n)
        a x

  have hDerivativeBoundUniform :
      ∀ (n : ℕ) (x : Point3),
        ‖spatial3.d
            a
            (
              fun y : Point3 =>
                h3LandauCutoffBump
                  (h3LandauQuarticRadius n)
                  (h3LandauQuarticRadius_pos n)
                  y
            )
            x‖
          ≤
        (C : ℝ) := by
    intro n x

    have hRadiusOne :
        1 ≤ h3LandauQuarticRadius n := by
      unfold h3LandauQuarticRadius

      have hn :
          0 ≤ (n : ℝ) := by
        positivity

      linarith

    exact
      (hDerivativeBound n x).trans
        (
          div_le_self
            C.coe_nonneg
            hRadiusOne
        )

  have hBMeas :
      ∀ n : ℕ,
        AEStronglyMeasurable
          (B n)
          (volume : Measure Point3) := by
    intro n

    have hC1 :
        SpatialC1
          (
            fun y : Point3 =>
              h3LandauCutoffBump
                (h3LandauQuarticRadius n)
                (h3LandauQuarticRadius_pos n)
                y
          ) :=
      h3LandauCutoffBump_spatialC1
        (h3LandauQuarticRadius_pos n)

    have hDerivativeMeas :
        AEStronglyMeasurable
          (
            spatial3.d
              a
              (
                fun y : Point3 =>
                  h3LandauCutoffBump
                    (h3LandauQuarticRadius n)
                    (h3LandauQuarticRadius_pos n)
                    y
              )
          )
          (volume : Measure Point3) :=
      (
        h3SpatialC1_spatial3_d_continuous_weakPressure
          hC1 a
      ).aestronglyMeasurable

    dsimp only [B]

    exact
      hDerivativeMeas.mul
        hF.aestronglyMeasurable

  have hMajorant :
      Integrable
        (
          fun x : Point3 =>
            (C : ℝ) * ‖F x‖
        )
        (volume : Measure Point3) :=
    hF.norm.const_mul (C : ℝ)

  have hBound :
      ∀ n : ℕ,
        ∀ᵐ x : Point3 ∂(volume : Measure Point3),
          ‖B n x‖
            ≤
          (C : ℝ) * ‖F x‖ := by
    intro n

    exact
      Filter.Eventually.of_forall
        (fun x => by
          dsimp only [B]

          rw [norm_mul]

          exact
            mul_le_mul_of_nonneg_right
              (hDerivativeBoundUniform n x)
              (norm_nonneg (F x)))

  have hInv :
      Tendsto
        (
          fun n : ℕ =>
            (1 : ℝ) / (((n + 1 : ℕ) : ℝ))
        )
        atTop
        (𝓝 0) := by
    simpa only [
      Nat.cast_add,
      Nat.cast_one
    ] using
      tendsto_one_div_add_atTop_nhds_zero_nat

  have hCoeff :
      Tendsto
        (
          fun n : ℕ =>
            (C : ℝ)
              *
            (
              (1 : ℝ) / (((n + 1 : ℕ) : ℝ))
            )
        )
        atTop
        (𝓝 0) := by
    have hConst :
        Tendsto
          (fun _n : ℕ => (C : ℝ))
          atTop
          (𝓝 (C : ℝ)) :=
      tendsto_const_nhds

    simpa only [mul_zero] using
      hConst.mul hInv

  have hPointwise :
      ∀ᵐ x : Point3 ∂(volume : Measure Point3),
        Tendsto
          (fun n : ℕ =>
            B n x)
          atTop
          (𝓝 0) := by
    filter_upwards with x

    rw [tendsto_zero_iff_norm_tendsto_zero]

    have hUpper :
        Tendsto
          (
            fun n : ℕ =>
              (
                (C : ℝ)
                  *
                (
                  (1 : ℝ) / (((n + 1 : ℕ) : ℝ))
                )
              )
                *
              ‖F x‖
          )
          atTop
          (𝓝 0) := by
      have hConst :
          Tendsto
            (fun _n : ℕ => ‖F x‖)
            atTop
            (𝓝 ‖F x‖) :=
        tendsto_const_nhds

      simpa only [zero_mul] using
        hCoeff.mul hConst

    apply
      squeeze_zero'
        (Filter.Eventually.of_forall
          (fun n =>
            norm_nonneg (B n x)))
        ?_
        hUpper

    exact
      Filter.Eventually.of_forall
        (fun n => by
          dsimp only [B]

          rw [norm_mul]

          have hD :=
            hDerivativeBound n x

          have hD' :
              ‖spatial3.d
                  a
                  (
                    fun y : Point3 =>
                      h3LandauCutoffBump
                        (h3LandauQuarticRadius n)
                        (h3LandauQuarticRadius_pos n)
                        y
                  )
                  x‖
                ≤
              (C : ℝ)
                *
              (
                (1 : ℝ) / (((n + 1 : ℕ) : ℝ))
              ) := by
            simpa only [
              h3LandauQuarticRadius,
              Nat.cast_add,
              Nat.cast_one,
              div_eq_mul_inv,
              one_div,
              one_mul
            ] using
              hD

          exact
            mul_le_mul_of_nonneg_right
              hD'
              (norm_nonneg (F x)))

  have hDCT :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := (volume : Measure Point3))
      (l := atTop)
      (F := B)
      (f := fun _x : Point3 => (0 : ℝ))
      (bound := fun x : Point3 =>
        (C : ℝ) * ‖F x‖)
      (Filter.Eventually.of_forall hBMeas)
      (Filter.Eventually.of_forall hBound)
      hMajorant
      hPointwise

  simpa only [
    B,
    integral_zero
  ] using
    hDCT

/--
An integrable `C¹` vector flux with integrable total divergence has zero
whole-space divergence integral.

This is the cutoff-at-infinity theorem needed by the top-order H³ transport
flux.  The theorem does not require the three coordinate derivatives of the
flux to be integrable separately.
-/
theorem integral_divergence_eq_zero_of_integrable_flux_coordinates
    {Fx Fy Fz : ScalarField3}
    (hFxC1 : SpatialC1 Fx)
    (hFyC1 : SpatialC1 Fy)
    (hFzC1 : SpatialC1 Fz)
    (hFx : Integrable Fx (volume : Measure Point3))
    (hFy : Integrable Fy (volume : Measure Point3))
    (hFz : Integrable Fz (volume : Measure Point3))
    (hDiv :
      Integrable
        (
          fun x : Point3 =>
            spatial3.d xAxis Fx x
              +
            (
              spatial3.d yAxis Fy x
                +
              spatial3.d zAxis Fz x
            )
        )
        (volume : Measure Point3)) :
    (
      ∫ x : Point3,
        spatial3.d xAxis Fx x
          +
        (
          spatial3.d yAxis Fy x
            +
          spatial3.d zAxis Fz x
        )
        ∂volume
    )
      =
    0 := by

  let divF : ScalarField3 :=
    fun x : Point3 =>
      spatial3.d xAxis Fx x
        +
      (
        spatial3.d yAxis Fy x
          +
        spatial3.d zAxis Fz x
      )

  let BX : ℕ → ℝ :=
    fun n =>
      ∫ x : Point3,
        spatial3.d
            xAxis
            (
              fun y : Point3 =>
                h3LandauCutoffBump
                  (h3LandauQuarticRadius n)
                  (h3LandauQuarticRadius_pos n)
                  y
            )
            x
          *
        Fx x
        ∂volume

  let BY : ℕ → ℝ :=
    fun n =>
      ∫ x : Point3,
        spatial3.d
            yAxis
            (
              fun y : Point3 =>
                h3LandauCutoffBump
                  (h3LandauQuarticRadius n)
                  (h3LandauQuarticRadius_pos n)
                  y
            )
            x
          *
        Fy x
        ∂volume

  let BZ : ℕ → ℝ :=
    fun n =>
      ∫ x : Point3,
        spatial3.d
            zAxis
            (
              fun y : Point3 =>
                h3LandauCutoffBump
                  (h3LandauQuarticRadius n)
                  (h3LandauQuarticRadius_pos n)
                  y
            )
            x
          *
        Fz x
        ∂volume

  let B : ℕ → ℝ :=
    fun n =>
      ∫ x : Point3,
        (
          spatial3.d
              xAxis
              (
                fun y : Point3 =>
                  h3LandauCutoffBump
                    (h3LandauQuarticRadius n)
                    (h3LandauQuarticRadius_pos n)
                    y
              )
              x
            *
          Fx x
        )
          +
        (
          (
            spatial3.d
                yAxis
                (
                  fun y : Point3 =>
                    h3LandauCutoffBump
                      (h3LandauQuarticRadius n)
                      (h3LandauQuarticRadius_pos n)
                      y
                )
                x
              *
            Fy x
          )
            +
          (
            spatial3.d
                zAxis
                (
                  fun y : Point3 =>
                    h3LandauCutoffBump
                      (h3LandauQuarticRadius n)
                      (h3LandauQuarticRadius_pos n)
                      y
                )
                x
              *
            Fz x
          )
        )
        ∂volume

  have hBX :
      Tendsto BX atTop (𝓝 0) := by
    dsimp only [BX]

    exact
      tendsto_h3LandauTopFluxBoundaryCoordinateIntegral_zero
        hFx xAxis

  have hBY :
      Tendsto BY atTop (𝓝 0) := by
    dsimp only [BY]

    exact
      tendsto_h3LandauTopFluxBoundaryCoordinateIntegral_zero
        hFy yAxis

  have hBZ :
      Tendsto BZ atTop (𝓝 0) := by
    dsimp only [BZ]

    exact
      tendsto_h3LandauTopFluxBoundaryCoordinateIntegral_zero
        hFz zAxis

  have hBoundarySeparate :
      Tendsto
        (fun n : ℕ =>
          BX n + (BY n + BZ n))
        atTop
        (𝓝 0) := by
    have hYZ :=
      hBY.add hBZ

    have hXYZ :=
      hBX.add hYZ

    simpa only [
      zero_add
    ] using
      hXYZ

  have hBoundaryEq :
      B
        =
      fun n : ℕ =>
        BX n + (BY n + BZ n) := by
    funext n

    let χ : ScalarField3 :=
      fun y : Point3 =>
        h3LandauCutoffBump
          (h3LandauQuarticRadius n)
          (h3LandauQuarticRadius_pos n)
          y

    have hχC1 :
        SpatialC1 χ := by
      dsimp only [χ]
      exact
        h3LandauCutoffBump_spatialC1
          (h3LandauQuarticRadius_pos n)

    obtain ⟨C, hC⟩ :=
      exists_uniform_norm_fderiv_h3LandauCutoffBump_axisDirection_le_div

    have hBoundaryInt
        (a : Axis Depth.three)
        (F : ScalarField3)
        (hF0 : Integrable F (volume : Measure Point3)) :
        Integrable
          (
            fun x : Point3 =>
              spatial3.d a χ x * F x
          )
          (volume : Measure Point3) := by

      have hDMeas :
          AEStronglyMeasurable
            (spatial3.d a χ)
            (volume : Measure Point3) :=
        (
          h3SpatialC1_spatial3_d_continuous_weakPressure
            hχC1 a
        ).aestronglyMeasurable

      have hDBound :
          ∀ x : Point3,
            ‖spatial3.d a χ x‖
              ≤
            (C : ℝ)
              /
            h3LandauQuarticRadius n := by
        intro x

        change
          ‖partialDeriv a χ x‖
            ≤
          (C : ℝ)
            /
          h3LandauQuarticRadius n

        rw [
          hχC1.partialDeriv_eq_fderiv_axisDirection
            x a
        ]

        dsimp only [χ]

        exact
          hC
            (h3LandauQuarticRadius_pos n)
            a x

      exact
        hF0.bdd_mul
          hDMeas
          (
            Filter.Eventually.of_forall
              hDBound
          )

    have hIX :=
      hBoundaryInt xAxis Fx hFx

    have hIY :=
      hBoundaryInt yAxis Fy hFy

    have hIZ :=
      hBoundaryInt zAxis Fz hFz

    have hYZIntegral :
        (
          ∫ x : Point3,
            spatial3.d yAxis χ x * Fy x
              +
            spatial3.d zAxis χ x * Fz x
            ∂volume
        )
          =
        (
          ∫ x : Point3,
            spatial3.d yAxis χ x * Fy x
            ∂volume
        )
          +
        (
          ∫ x : Point3,
            spatial3.d zAxis χ x * Fz x
            ∂volume
        ) := by
      simpa only [Pi.add_apply] using
        (MeasureTheory.integral_add hIY hIZ)

    have hXYZIntegral :
        (
          ∫ x : Point3,
            spatial3.d xAxis χ x * Fx x
              +
            (
              spatial3.d yAxis χ x * Fy x
                +
              spatial3.d zAxis χ x * Fz x
            )
            ∂volume
        )
          =
        (
          ∫ x : Point3,
            spatial3.d xAxis χ x * Fx x
            ∂volume
        )
          +
        (
          ∫ x : Point3,
            spatial3.d yAxis χ x * Fy x
              +
            spatial3.d zAxis χ x * Fz x
            ∂volume
        ) := by
      simpa only [Pi.add_apply] using
        (
          MeasureTheory.integral_add
            hIX
            (hIY.add hIZ)
        )

    dsimp only [B, BX, BY, BZ, χ]

    rw [
      hXYZIntegral,
      hYZIntegral
    ]

  have hBoundary :
      Tendsto
        B
        atTop
        (𝓝 0) := by
    rw [hBoundaryEq]

    exact hBoundarySeparate

  have hWeighted :
      Tendsto
        (h3LandauQuarticCutoffIntegral divF)
        atTop
        (
          𝓝
            (
              ∫ x : Point3,
                divF x
                ∂volume
            )
        ) :=
    tendsto_h3LandauQuarticCutoffIntegral
      hDiv

  have hIdentity :
      h3LandauQuarticCutoffIntegral divF
        =
      fun n : ℕ =>
        -(B n) := by
    funext n

    have hCutoff :=
      h3LandauCutoff_integral_divergence_eq_neg_boundary
        hFxC1
        hFyC1
        hFzC1
        hFx
        hFy
        hFz
        hDiv
        (h3LandauQuarticRadius_pos n)

    dsimp only [
      h3LandauQuarticCutoffIntegral,
      divF,
      B
    ]

    exact hCutoff

  have hWeightedZero :
      Tendsto
        (h3LandauQuarticCutoffIntegral divF)
        atTop
        (𝓝 0) := by
    rw [hIdentity]

    simpa only [neg_zero] using
      hBoundary.neg

  have hUnique :
      (
        ∫ x : Point3,
          divF x
          ∂volume
      )
        =
      0 :=
    tendsto_nhds_unique
      hWeighted
      hWeightedZero

  simpa only [divF] using
    hUnique

end

end Euclidean
end Bridge
end PrimeTensor
