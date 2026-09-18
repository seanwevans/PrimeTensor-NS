import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Landau.Analytic.Quartic.BoundaryScale
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Vanishing of the quartic cutoff boundary derivative

The previous increments established the uniform estimate

    ‖Dχ_R eₐ‖₄ ≤ K R^(-1/4).

This file turns that quantitative estimate into the actual `R → ∞` limit.

Because `h3LandauCutoffBump R hR` carries the proof `hR : 0 < R`, the
real-valued norm is totalized by setting it to zero at nonpositive radii.
That choice is irrelevant at `atTop` and gives an ordinary function `ℝ → ℝ`
to which the standard squeeze theorem applies.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Function MeasureTheory Filter
open scoped ENNReal NNReal Topology ContDiff

noncomputable section

noncomputable local instance axisFintypeH3LandauQuarticBoundaryDecay
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Totalized real `L⁴` norm of the coordinate cutoff derivative.  At positive
radius this is the actual norm; at nonpositive radius it is set to zero. -/
noncomputable def h3LandauCutoffBoundaryLpNorm
    (a : Axis Depth.three)
    (R : ℝ) : ℝ :=
  if hR : 0 < R then
    lpNorm
      (fun x : Point3 =>
        fderiv ℝ
            (fun y : Point3 =>
              h3LandauCutoffBump R hR y)
            x
            (axisDirection a))
      4
      volume
  else
    0

/-- On positive radii, the totalized boundary norm is the literal cutoff
derivative `L⁴` norm. -/
theorem h3LandauCutoffBoundaryLpNorm_eq
    (a : Axis Depth.three)
    {R : ℝ}
    (hR : 0 < R) :
    h3LandauCutoffBoundaryLpNorm a R
      =
    lpNorm
      (fun x : Point3 =>
        fderiv ℝ
            (fun y : Point3 =>
              h3LandauCutoffBump R hR y)
            x
            (axisDirection a))
      4
      volume := by
  simp only [
    h3LandauCutoffBoundaryLpNorm,
    dif_pos hR
  ]

/-- The coordinate cutoff derivative vanishes in `L⁴` as the cutoff radius
tends to infinity. -/
theorem tendsto_h3LandauCutoffBoundaryLpNorm_zero
    (a : Axis Depth.three) :
    Tendsto
      (h3LandauCutoffBoundaryLpNorm a)
      atTop
      (𝓝 0) := by
  obtain ⟨K, hK, hBound⟩ :=
    exists_uniform_lpNorm_four_fderiv_h3LandauCutoffBump_axisDirection_le_rpow

  have hPow :
      Tendsto
        (fun R : ℝ =>
          R ^ (-(1 : ℝ) / 4))
        atTop
        (𝓝 0) := by
    simpa only [neg_div] using
      (
        tendsto_rpow_neg_atTop
          (show 0 < (1 : ℝ) / 4 by norm_num)
      )

  have hUpper :
      Tendsto
        (fun R : ℝ =>
          K * R ^ (-(1 : ℝ) / 4))
        atTop
        (𝓝 0) := by
    have hConst :
        Tendsto
          (fun _ : ℝ => K)
          atTop
          (𝓝 K) :=
      tendsto_const_nhds

    have hMul :
        Tendsto
          (fun R : ℝ =>
            K * R ^ (-(1 : ℝ) / 4))
          atTop
          (𝓝 (K * 0)) :=
      hConst.mul hPow

    simpa only [mul_zero] using
      hMul

  apply
    squeeze_zero'

  · exact
      Filter.Eventually.of_forall
        (fun R => by
          by_cases hR : 0 < R
          · rw [
              h3LandauCutoffBoundaryLpNorm_eq
                a hR
            ]
            exact lpNorm_nonneg
          · simp [
              h3LandauCutoffBoundaryLpNorm,
              hR
            ])

  · filter_upwards [
      eventually_gt_atTop (0 : ℝ)
    ] with R hR

    rw [
      h3LandauCutoffBoundaryLpNorm_eq
        a hR
    ]

    exact
      hBound hR a

  · exact
      hUpper

end

end Euclidean
end Bridge
end PrimeTensor
