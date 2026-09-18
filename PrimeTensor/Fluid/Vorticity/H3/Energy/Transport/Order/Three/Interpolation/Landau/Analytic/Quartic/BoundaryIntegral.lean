import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Landau.Analytic.Quartic.BoundaryDecay
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Hölder bound for the quartic cutoff boundary integral

For positive radius, the quartic cutoff boundary error is

    ∫ (Dₐχ_R) (v g³).

The previous files supply the complementary spaces

    Dₐχ_R ∈ L⁴,
    v g³ ∈ L^(4/3).

This file packages the resulting Hölder estimate directly in terms of
`lpNorm`, matching the radius-decay theorem already proved for the first
factor.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Function MeasureTheory Filter
open scoped ENNReal NNReal Topology ContDiff

noncomputable section

noncomputable local instance axisFintypeH3LandauQuarticBoundaryIntegral
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- `4` and `4/3` are Hölder conjugates. -/
theorem real_holderConjugate_four_fourThirds :
    Real.HolderConjugate
      (4 : ℝ)
      (4 / 3 : ℝ) := by
  rw [Real.holderConjugate_iff]
  norm_num

/-- Hölder bounds the quartic cutoff boundary integral by the product of the
`L⁴` cutoff derivative norm and the fixed `L^(4/3)` partner norm. -/
theorem abs_integral_fderiv_h3LandauCutoffBump_mul_boundedCube_le_lpNorm :
    ∀ {R : ℝ}
      (hR : 0 < R)
      {v g : ScalarField3}
      {h : ℝ}
      (hv : SpatialC1 v)
      (hg : SpatialC1 g)
      (hEnv : LandauScalarEnvelope v h)
      (hg4 :
        MeasureTheory.MemLp
          g
          (ENNReal.ofReal 4)
          volume)
      (a : Axis Depth.three),
      abs
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
        )
        ≤
      lpNorm
          (fun x : Point3 =>
            fderiv ℝ
                (fun y : Point3 =>
                  h3LandauCutoffBump R hR y)
                x
                (axisDirection a))
          (ENNReal.ofReal 4)
          volume
        *
      lpNorm
          (fun x : Point3 =>
            v x * (g x) ^ 3)
          (ENNReal.ofReal (4 / 3 : ℝ))
          volume := by
  intro R hR v g h hv hg hEnv hg4 a

  let dχ : Point3 → ℝ :=
    fun x : Point3 =>
      fderiv ℝ
          (fun y : Point3 =>
            h3LandauCutoffBump R hR y)
          x
          (axisDirection a)

  let partner : Point3 → ℝ :=
    fun x : Point3 =>
      v x * (g x) ^ 3

  have hdχContinuous :
      Continuous dχ := by
    dsimp [dχ]

    exact
      (
        (h3LandauCutoffBump_spatialC1 hR).continuous_fderiv
          (by norm_num)
      ).clm_apply
        continuous_const

  have hdχSupport :
      HasCompactSupport dχ := by
    dsimp [dχ]

    exact
      hasCompactSupport_fderiv_apply
        (h3LandauCutoffBump_hasCompactSupport hR)
        (axisDirection a)

  have hdχ4 :
      MeasureTheory.MemLp
        dχ
        (ENNReal.ofReal 4)
        volume :=
    hdχContinuous.memLp_of_hasCompactSupport
      hdχSupport

  have hVMeas :
      MeasureTheory.AEStronglyMeasurable
        v
        volume :=
    hv.continuous.aestronglyMeasurable

  have hPartner :
      MeasureTheory.MemLp
        partner
        (ENNReal.ofReal (4 / 3 : ℝ))
        volume := by
    dsimp [partner]

    exact
      memLp_four_thirds_bounded_cube
        hVMeas
        hEnv
        hg4

  have hHolder :=
    MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
      (μ := volume)
      real_holderConjugate_four_fourThirds
      hdχ4
      hPartner

  have hdχLp :
      lpNorm
          dχ
          (ENNReal.ofReal 4)
          volume
        =
      (
        ∫ x : Point3,
          ‖dχ x‖ ^ (4 : ℝ)
      ) ^ (1 / (4 : ℝ)) := by
    have hRaw :=
      MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
        (p := ENNReal.ofReal 4)
        (f := dχ)
        (μ := volume)
        (by norm_num)
        (by norm_num)
        hdχ4.aestronglyMeasurable

    norm_num at hRaw ⊢
    exact hRaw

  have hPartnerLp :
      lpNorm
          partner
          (ENNReal.ofReal (4 / 3 : ℝ))
          volume
        =
      (
        ∫ x : Point3,
          ‖partner x‖ ^ (4 / 3 : ℝ)
      ) ^ (1 / (4 / 3 : ℝ)) := by
    have hRaw :=
      MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
        (p := ENNReal.ofReal (4 / 3 : ℝ))
        (f := partner)
        (μ := volume)
        (by norm_num)
        (by norm_num)
        hPartner.aestronglyMeasurable

    norm_num at hRaw ⊢
    exact hRaw

  have hNormIntegral :
      abs
        (
          ∫ x : Point3,
            dχ x * partner x
        )
        ≤
      ∫ x : Point3,
        ‖dχ x‖ * ‖partner x‖ := by
    calc
      abs
          (
            ∫ x : Point3,
              dχ x * partner x
          )
          ≤
        ∫ x : Point3,
          ‖dχ x * partner x‖ := by
            simpa only [Real.norm_eq_abs] using
              (
                MeasureTheory.norm_integral_le_integral_norm
                  (f :=
                    fun x : Point3 =>
                      dχ x * partner x)
              )

      _ =
        ∫ x : Point3,
          ‖dχ x‖ * ‖partner x‖ := by
            apply integral_congr_ae
            filter_upwards with x
            exact norm_mul _ _

  have hLpProduct :
      (
        ∫ x : Point3,
          ‖dχ x‖ ^ (4 : ℝ)
      ) ^ (1 / (4 : ℝ))
        *
      (
        ∫ x : Point3,
          ‖partner x‖ ^ (4 / 3 : ℝ)
      ) ^ (1 / (4 / 3 : ℝ))
        =
      lpNorm
          dχ
          (ENNReal.ofReal 4)
          volume
        *
      lpNorm
          partner
          (ENNReal.ofReal (4 / 3 : ℝ))
          volume := by
    rw [
      ← hdχLp,
      ← hPartnerLp
    ]

  have hMain :
      abs
        (
          ∫ x : Point3,
            dχ x * partner x
        )
        ≤
      lpNorm
          dχ
          (ENNReal.ofReal 4)
          volume
        *
      lpNorm
          partner
          (ENNReal.ofReal (4 / 3 : ℝ))
          volume := by
    calc
      abs
          (
            ∫ x : Point3,
              dχ x * partner x
          )
          ≤
        ∫ x : Point3,
          ‖dχ x‖ * ‖partner x‖ :=
            hNormIntegral

      _ ≤
        (
          ∫ x : Point3,
            ‖dχ x‖ ^ (4 : ℝ)
        ) ^ (1 / (4 : ℝ))
          *
        (
          ∫ x : Point3,
            ‖partner x‖ ^ (4 / 3 : ℝ)
        ) ^ (1 / (4 / 3 : ℝ)) :=
            hHolder

      _ =
        lpNorm
            dχ
            (ENNReal.ofReal 4)
            volume
          *
        lpNorm
            partner
            (ENNReal.ofReal (4 / 3 : ℝ))
            volume :=
              hLpProduct

  simpa [dχ, partner] using
    hMain

end

end Euclidean
end Bridge
end PrimeTensor
