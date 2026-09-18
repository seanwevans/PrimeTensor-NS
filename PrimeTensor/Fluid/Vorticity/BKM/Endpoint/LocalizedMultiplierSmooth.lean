import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.LocalizedMultiplier
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Transport
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
# BKM endpoint: smooth localized Biot--Savart multiplier

The dyadic shell kills an entire neighborhood of the singular frequency.  This
makes the localized coordinate multiplier globally smooth.

The key implementation choice is to keep the raw rational multiplier real:

    rᵢₖ(ξ) = ξᵢ ξₖ / |ξ|² ∈ ℝ,

prove that `C∞` over the real Fourier carrier away from `ξ = 0`, and only then
complexify with `Complex.ofRealCLM`.

This avoids asking Lean to interpret the real Fourier carrier as a complex
normed space when applying the smooth-division API.

At `ξ = 0`, the localized multiplier is identically zero on the whole
radius-`R` ball, hence locally constant and smooth.

Combining the two cases proves global `C∞` regularity.  Together with the
compact-support theorem from `LocalizedMultiplier`, this packages the symbol
as a complex Schwartz function.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Function Filter
open scoped Topology ContDiff SchwartzMap

noncomputable section

noncomputable local instance axisFintypeBKMEndpointLocalizedMultiplierSmooth
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Coordinate evaluation on the Fourier Euclidean carrier as a real
continuous-linear functional. -/
noncomputable def h3BKMFourierCoordinateCLM
    (a : PrimeTensor.Axis Depth.three) :
    H3FourierPoint3 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj a : Point3 →L[ℝ] ℝ).comp
    h3FourierToPoint3CLM

@[simp]
theorem h3BKMFourierCoordinateCLM_apply
    (a : PrimeTensor.Axis Depth.three)
    (ξ : H3FourierPoint3) :
    h3BKMFourierCoordinateCLM a ξ = ξ a := by
  rfl

/-- Every Fourier coordinate is globally `C∞` as a real-valued function. -/
theorem h3BKMFourierCoordinate_contDiff
    (i : Fin 3) :
    ContDiff ℝ ∞
      (fun ξ : H3FourierPoint3 =>
        ξ (h3AxisOfFin3 i)) := by

  change
    ContDiff ℝ ∞
      (h3BKMFourierCoordinateCLM
        (h3AxisOfFin3 i))

  exact
    (h3BKMFourierCoordinateCLM
      (h3AxisOfFin3 i)).contDiff

/-- The real squared Fourier radius is globally smooth. -/
theorem h3BKMFourierRadiusSqReal_contDiff :
    ContDiff ℝ ∞
      h3BKMFourierRadiusSqReal := by

  unfold h3BKMFourierRadiusSqReal

  exact
    (
      (
        (h3BKMFourierCoordinate_contDiff 0).pow 2
      ).add
        (
          (h3BKMFourierCoordinate_contDiff 1).pow 2
        )
    ).add
      (
        (h3BKMFourierCoordinate_contDiff 2).pow 2
      )

/-- Real raw coordinate multiplier, used away from the zero frequency. -/
noncomputable def h3BKMRawCoordinateMultiplierReal
    (i k : Fin 3)
    (ξ : H3FourierPoint3) : ℝ :=
  (
    ξ (h3AxisOfFin3 i)
      *
    ξ (h3AxisOfFin3 k)
  )
    /
  h3BKMFourierRadiusSqReal ξ

/-- The real raw multiplier is smooth at every nonzero frequency. -/
theorem h3BKMRawCoordinateMultiplierReal_contDiffAt
    (i k : Fin 3)
    {ξ : H3FourierPoint3}
    (hξ : ξ ≠ 0) :
    ContDiffAt ℝ ∞
      (h3BKMRawCoordinateMultiplierReal i k)
      ξ := by

  change
    ContDiffAt ℝ ∞
      (fun η : H3FourierPoint3 =>
        h3BKMFourierCoordinateCLM
            (h3AxisOfFin3 i) η
          *
        h3BKMFourierCoordinateCLM
            (h3AxisOfFin3 k) η
          /
        h3BKMFourierRadiusSqReal η)
      ξ

  have hI :
      ContDiffAt ℝ ∞
        (h3BKMFourierCoordinateCLM
          (h3AxisOfFin3 i))
        ξ :=
    (h3BKMFourierCoordinateCLM
      (h3AxisOfFin3 i)).contDiff.contDiffAt

  have hK :
      ContDiffAt ℝ ∞
        (h3BKMFourierCoordinateCLM
          (h3AxisOfFin3 k))
        ξ :=
    (h3BKMFourierCoordinateCLM
      (h3AxisOfFin3 k)).contDiff.contDiffAt

  have hDen :
      ContDiffAt ℝ ∞
        h3BKMFourierRadiusSqReal
        ξ :=
    h3BKMFourierRadiusSqReal_contDiff.contDiffAt

  have hDenNe :
      h3BKMFourierRadiusSqReal ξ ≠ 0 :=
    (
      h3BKMFourierRadiusSqReal_pos
        ξ hξ
    ).ne'

  exact
    (hI.mul hK).div
      hDen hDenNe

/-- Complexification of the real raw multiplier. -/
noncomputable def h3BKMRawCoordinateMultiplier
    (i k : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  (
    h3BKMRawCoordinateMultiplierReal i k ξ :
    ℂ
  )

/-- The complexified raw multiplier remains smooth over the real Fourier
carrier. -/
theorem h3BKMRawCoordinateMultiplier_contDiffAt
    (i k : Fin 3)
    {ξ : H3FourierPoint3}
    (hξ : ξ ≠ 0) :
    ContDiffAt ℝ ∞
      (h3BKMRawCoordinateMultiplier i k)
      ξ := by

  unfold h3BKMRawCoordinateMultiplier

  exact
    ContDiffAt.fun_comp
      ξ
      Complex.ofRealCLM.contDiff.contDiffAt
      (
        h3BKMRawCoordinateMultiplierReal_contDiffAt
          i k hξ
      )

/-- At every nonzero frequency, the totalized coordinate coefficient is exactly
the complexification of the real rational symbol. -/
theorem h3BKMCoordinateCoefficient_eq_raw
    (i k : Fin 3)
    {ξ : H3FourierPoint3}
    (hξ : ξ ≠ 0) :
    h3BKMCoordinateCoefficient ξ i k
      =
    h3BKMRawCoordinateMultiplier i k ξ := by

  have hRadius :
      h3BKMFourierRadiusSqReal ξ ≠ 0 :=
    (
      h3BKMFourierRadiusSqReal_pos
        ξ hξ
    ).ne'

  unfold
    h3BKMCoordinateCoefficient
    h3BKMRawCoordinateMultiplier
    h3BKMRawCoordinateMultiplierReal

  rw [
    dif_neg hRadius,
    h3BKMFourierRadiusSq_eq_ofReal,
    ← Complex.ofReal_mul,
    ← Complex.ofReal_div
  ]

/-- Away from zero, the totalized coordinate coefficient agrees in a whole
neighborhood with the ordinary rational formula. -/
theorem h3BKMCoordinateCoefficient_eventuallyEq_raw
    (i k : Fin 3)
    {ξ : H3FourierPoint3}
    (hξ : ξ ≠ 0) :
    (fun η : H3FourierPoint3 =>
      h3BKMCoordinateCoefficient η i k)
      =ᶠ[𝓝 ξ]
    h3BKMRawCoordinateMultiplier i k := by

  filter_upwards [
    continuousAt_id.eventually_ne hξ
  ] with η hη

  exact
    h3BKMCoordinateCoefficient_eq_raw
      i k hη

/-- The complexified dyadic shell is globally smooth. -/
theorem h3BKMFrequencyShell_complex_contDiff
    {R : ℝ}
    (hR : 0 < R) :
    ContDiff ℝ ∞
      (fun ξ : H3FourierPoint3 =>
        (h3BKMFrequencyShell R hR ξ : ℂ)) := by

  exact
    Complex.ofRealCLM.contDiff.comp
      (h3BKMFrequencyShell_contDiff hR)

/-- At every nonzero frequency, the localized multiplier is smooth. -/
theorem h3BKMLocalizedCoordinateMultiplier_contDiffAt_of_ne_zero
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3)
    {ξ : H3FourierPoint3}
    (hξ : ξ ≠ 0) :
    ContDiffAt ℝ ∞
      (h3BKMLocalizedCoordinateMultiplier
        R hR i k)
      ξ := by

  have hProduct :
      ContDiffAt ℝ ∞
        (fun η : H3FourierPoint3 =>
          (h3BKMFrequencyShell R hR η : ℂ)
            *
          h3BKMRawCoordinateMultiplier i k η)
        ξ :=
    (h3BKMFrequencyShell_complex_contDiff hR).contDiffAt.mul
      (
        h3BKMRawCoordinateMultiplier_contDiffAt
          i k hξ
      )

  apply
    hProduct.congr_of_eventuallyEq

  filter_upwards [
    h3BKMCoordinateCoefficient_eventuallyEq_raw
      i k hξ
  ] with η hCoeff

  unfold h3BKMLocalizedCoordinateMultiplier

  rw [hCoeff]

/-- At zero frequency, the localized multiplier is locally the constant zero
function because the shell vanishes on the entire inner ball. -/
theorem h3BKMLocalizedCoordinateMultiplier_contDiffAt_zero
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    ContDiffAt ℝ ∞
      (h3BKMLocalizedCoordinateMultiplier
        R hR i k)
      (0 : H3FourierPoint3) := by

  have hConst :
      ContDiffAt ℝ ∞
        (fun _ : H3FourierPoint3 => (0 : ℂ))
        (0 : H3FourierPoint3) :=
    contDiffAt_const

  apply
    hConst.congr_of_eventuallyEq

  filter_upwards [
    Metric.ball_mem_nhds
      (0 : H3FourierPoint3)
      hR
  ] with η hη

  have hNorm :
      ‖η‖ ≤ R := by
    have hLt :
        ‖η‖ < R := by
      simpa only [
        Metric.mem_ball,
        dist_zero_right
      ] using hη

    exact hLt.le

  exact
    h3BKMLocalizedCoordinateMultiplier_eq_zero_of_norm_le
      hR i k hNorm

/-- Every localized Biot--Savart coordinate symbol is globally `C∞`. -/
theorem h3BKMLocalizedCoordinateMultiplier_contDiff
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    ContDiff ℝ ∞
      (h3BKMLocalizedCoordinateMultiplier
        R hR i k) := by

  rw [contDiff_iff_contDiffAt]

  intro ξ

  by_cases hξ : ξ = 0

  · subst ξ

    exact
      h3BKMLocalizedCoordinateMultiplier_contDiffAt_zero
        hR i k

  · exact
      h3BKMLocalizedCoordinateMultiplier_contDiffAt_of_ne_zero
        hR i k hξ

/-- The localized coordinate multiplier packaged as a complex Schwartz
function. -/
noncomputable def h3BKMLocalizedCoordinateMultiplierSchwartz
    (R : ℝ)
    (hR : 0 < R)
    (i k : Fin 3) :
    𝓢(H3FourierPoint3, ℂ) :=
  (
    h3BKMLocalizedCoordinateMultiplier_hasCompactSupport
      hR i k
  ).toSchwartzMap
    (
      h3BKMLocalizedCoordinateMultiplier_contDiff
        hR i k
    )

@[simp]
theorem h3BKMLocalizedCoordinateMultiplierSchwartz_apply
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3)
    (ξ : H3FourierPoint3) :
    h3BKMLocalizedCoordinateMultiplierSchwartz
        R hR i k ξ
      =
    h3BKMLocalizedCoordinateMultiplier
      R hR i k ξ := by
  rfl

/-- The Schwartz multiplier retains the uniform pointwise norm bound. -/
theorem norm_h3BKMLocalizedCoordinateMultiplierSchwartz_le_one
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3)
    (ξ : H3FourierPoint3) :
    ‖h3BKMLocalizedCoordinateMultiplierSchwartz
        R hR i k ξ‖
      ≤
    1 := by

  rw [
    h3BKMLocalizedCoordinateMultiplierSchwartz_apply
  ]

  exact
    norm_h3BKMLocalizedCoordinateMultiplier_le_one
      hR i k ξ

end

end Euclidean
end Bridge
end PrimeTensor
