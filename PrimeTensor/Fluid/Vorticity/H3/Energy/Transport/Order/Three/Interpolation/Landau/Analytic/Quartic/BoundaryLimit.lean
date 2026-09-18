import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Landau.Analytic.Quartic.BoundaryIntegral

/-!
# Vanishing of the quartic cutoff boundary error

For positive cutoff radius `R`, the signed boundary error is

    ∫ (Dₐχ_R) (v g³).

`BoundaryIntegral` bounds its absolute value by

    ‖Dₐχ_R‖₄ · ‖v g³‖_(4/3),

and `BoundaryDecay` proves that the first factor tends to zero.  The second
factor is independent of `R`.  Hence the full boundary error vanishes as
`R → ∞`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Function MeasureTheory Filter
open scoped ENNReal NNReal Topology ContDiff

noncomputable section

noncomputable local instance axisFintypeH3LandauQuarticBoundaryLimit
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Totalized signed quartic cutoff boundary error.  It agrees with the
literal boundary integral at positive radius and is set to zero otherwise. -/
noncomputable def h3LandauQuarticBoundaryError
    (v g : ScalarField3)
    (a : Axis Depth.three)
    (R : ℝ) : ℝ :=
  if hR : 0 < R then
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
  else
    0

/-- On positive radii the totalized error is the literal boundary integral. -/
theorem h3LandauQuarticBoundaryError_eq
    (v g : ScalarField3)
    (a : Axis Depth.three)
    {R : ℝ}
    (hR : 0 < R) :
    h3LandauQuarticBoundaryError v g a R
      =
    ∫ x : Point3,
      fderiv ℝ
          (fun y : Point3 =>
            h3LandauCutoffBump R hR y)
          x
          (axisDirection a)
        *
      (
        v x * (g x) ^ 3
      ) := by
  unfold h3LandauQuarticBoundaryError
  exact dite_eq_left hR

/-- The quartic cutoff boundary error vanishes as the cutoff radius tends to
infinity. -/
theorem tendsto_h3LandauQuarticBoundaryError_zero
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
    (a : Axis Depth.three) :
    Tendsto
      (h3LandauQuarticBoundaryError v g a)
      atTop
      (𝓝 0) := by
  let partnerNorm : ℝ :=
    lpNorm
      (fun x : Point3 =>
        v x * (g x) ^ 3)
      (ENNReal.ofReal (4 / 3 : ℝ))
      volume

  have hCutoff :
      Tendsto
        (h3LandauCutoffBoundaryLpNorm a)
        atTop
        (𝓝 0) :=
    tendsto_h3LandauCutoffBoundaryLpNorm_zero
      a

  have hPartnerConst :
      Tendsto
        (fun _ : ℝ =>
          partnerNorm)
        atTop
        (𝓝 partnerNorm) :=
    tendsto_const_nhds

  have hUpper :
      Tendsto
        (fun R : ℝ =>
          h3LandauCutoffBoundaryLpNorm a R
            *
          partnerNorm)
        atTop
        (𝓝 0) := by
    have hMul :
        Tendsto
          (fun R : ℝ =>
            h3LandauCutoffBoundaryLpNorm a R
              *
            partnerNorm)
          atTop
          (𝓝 (0 * partnerNorm)) :=
      hCutoff.mul hPartnerConst

    simpa only [zero_mul] using
      hMul

  have hAbsNonneg :
      ∀ᶠ R : ℝ in atTop,
        0 ≤
          abs
            (h3LandauQuarticBoundaryError
              v g a R) :=
    Filter.Eventually.of_forall
      (fun R =>
        abs_nonneg
          (h3LandauQuarticBoundaryError
            v g a R))

  have hAbsUpper :
      ∀ᶠ R : ℝ in atTop,
        abs
            (h3LandauQuarticBoundaryError
              v g a R)
          ≤
        h3LandauCutoffBoundaryLpNorm a R
          *
        partnerNorm := by
    filter_upwards [
      eventually_gt_atTop (0 : ℝ)
    ] with R hR

    rw [
      h3LandauQuarticBoundaryError_eq
        v g a hR
    ]

    have hBound :=
      abs_integral_fderiv_h3LandauCutoffBump_mul_boundedCube_le_lpNorm
        hR
        hv
        hg
        hEnv
        hg4
        a

    have hCutoffEq :=
      h3LandauCutoffBoundaryLpNorm_eq
        a hR

    rw [hCutoffEq]

    simpa [partnerNorm] using
      hBound

  have hAbs :
      Tendsto
        (fun R : ℝ =>
          abs
            (h3LandauQuarticBoundaryError
              v g a R))
        atTop
        (𝓝 0) :=
    squeeze_zero'
      hAbsNonneg
      hAbsUpper
      hUpper

  rw [
    tendsto_zero_iff_norm_tendsto_zero
  ]

  simpa only [Real.norm_eq_abs] using
    hAbs

end

end Euclidean
end Bridge
end PrimeTensor
