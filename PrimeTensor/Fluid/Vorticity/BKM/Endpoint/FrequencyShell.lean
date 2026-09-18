import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.PhysicalKernel
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# BKM endpoint: smooth dyadic frequency shell

The physical kernel estimate is ready.  The next harmonic-analysis object is a
smooth frequency band which stays away from the singular frequency `ξ = 0`.

For every `R > 0`, let `χ_R` be the standard smooth radial bump which is one on
the radius-`R` ball and compactly supported in the radius-`2R` ball.  Define

    ψ_R(ξ) = χ_{2R}(ξ) (1 - χ_R(ξ)).

Thus `ψ_R`

* is `C∞`;
* has compact support;
* is nonnegative;
* vanishes identically on `‖ξ‖ ≤ R`.

The shell is therefore a Schwartz function supported away from the singularity
of the degree-zero Biot--Savart multiplier.  The later localized-multiplier
file can multiply by `ξᵢ ξₖ / |ξ|²` without introducing any singular behavior
at the origin.

This file also records the exact dilation identity for the low-pass bump.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Function
open scoped Topology ContDiff SchwartzMap

noncomputable section

noncomputable local instance axisFintypeBKMEndpointFrequencyShell
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Smooth Fourier cutoff equal to one through radius `R` and supported through
radius `2R`. -/
noncomputable def h3BKMFrequencyCutoffBump
    (R : ℝ)
    (hR : 0 < R) :
    ContDiffBump (0 : H3FourierPoint3) where
  rIn := R
  rOut := 2 * R
  rIn_pos := hR
  rIn_lt_rOut := by
    nlinarith

@[simp]
theorem h3BKMFrequencyCutoffBump_rIn
    {R : ℝ}
    (hR : 0 < R) :
    (h3BKMFrequencyCutoffBump R hR).rIn = R := by
  rfl

@[simp]
theorem h3BKMFrequencyCutoffBump_rOut
    {R : ℝ}
    (hR : 0 < R) :
    (h3BKMFrequencyCutoffBump R hR).rOut = 2 * R := by
  rfl

theorem h3BKMFrequencyCutoffBump_nonneg
    {R : ℝ}
    (hR : 0 < R)
    (ξ : H3FourierPoint3) :
    0 ≤ h3BKMFrequencyCutoffBump R hR ξ := by
  exact
    (h3BKMFrequencyCutoffBump R hR).nonneg

theorem h3BKMFrequencyCutoffBump_le_one
    {R : ℝ}
    (hR : 0 < R)
    (ξ : H3FourierPoint3) :
    h3BKMFrequencyCutoffBump R hR ξ ≤ 1 := by
  exact
    (h3BKMFrequencyCutoffBump R hR).le_one

theorem h3BKMFrequencyCutoffBump_contDiff
    {R : ℝ}
    (hR : 0 < R) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (h3BKMFrequencyCutoffBump R hR :
        H3FourierPoint3 → ℝ) := by
  simpa using
    ((h3BKMFrequencyCutoffBump R hR).contDiff
      (n := (⊤ : ℕ∞)))

theorem h3BKMFrequencyCutoffBump_hasCompactSupport
    {R : ℝ}
    (hR : 0 < R) :
    HasCompactSupport
      (h3BKMFrequencyCutoffBump R hR :
        H3FourierPoint3 → ℝ) := by
  exact
    (h3BKMFrequencyCutoffBump R hR).hasCompactSupport

/-- The cutoff is one on its inner closed ball. -/
theorem h3BKMFrequencyCutoffBump_eq_one_of_norm_le
    {R : ℝ}
    (hR : 0 < R)
    {ξ : H3FourierPoint3}
    (hξ : ‖ξ‖ ≤ R) :
    h3BKMFrequencyCutoffBump R hR ξ = 1 := by

  apply
    (h3BKMFrequencyCutoffBump R hR).one_of_mem_closedBall

  simpa only [
    Metric.mem_closedBall,
    dist_zero_right,
    h3BKMFrequencyCutoffBump_rIn
  ] using hξ

/--
Every positive-radius Fourier cutoff is the unit cutoff evaluated at the
rescaled frequency `R⁻¹ ξ`.
-/
theorem h3BKMFrequencyCutoffBump_eq_unit_smul
    {R : ℝ}
    (hR : 0 < R)
    (ξ : H3FourierPoint3) :
    h3BKMFrequencyCutoffBump R hR ξ
      =
    h3BKMFrequencyCutoffBump
      (1 : ℝ)
      zero_lt_one
      (R⁻¹ • ξ) := by

  rw [
    ContDiffBump.apply,
    ContDiffBump.apply
  ]

  simp [
    h3BKMFrequencyCutoffBump,
    hR.ne',
    div_eq_mul_inv
  ]

/--
Smooth shell which removes the singular inner ball while retaining compact
frequency support.
-/
noncomputable def h3BKMFrequencyShell
    (R : ℝ)
    (hR : 0 < R)
    (ξ : H3FourierPoint3) : ℝ :=
  h3BKMFrequencyCutoffBump
      (2 * R)
      (mul_pos (by norm_num) hR)
      ξ
    *
  (
    1
      -
    h3BKMFrequencyCutoffBump
      R hR ξ
  )

/-- The frequency shell is nonnegative. -/
theorem h3BKMFrequencyShell_nonneg
    {R : ℝ}
    (hR : 0 < R)
    (ξ : H3FourierPoint3) :
    0 ≤ h3BKMFrequencyShell R hR ξ := by

  unfold h3BKMFrequencyShell

  exact
    mul_nonneg
      (h3BKMFrequencyCutoffBump_nonneg
        (mul_pos (by norm_num) hR)
        ξ)
      (
        sub_nonneg.mpr
          (h3BKMFrequencyCutoffBump_le_one
            hR ξ)
      )

/-- The shell vanishes throughout its radius-`R` inner ball. -/
theorem h3BKMFrequencyShell_eq_zero_of_norm_le
    {R : ℝ}
    (hR : 0 < R)
    {ξ : H3FourierPoint3}
    (hξ : ‖ξ‖ ≤ R) :
    h3BKMFrequencyShell R hR ξ = 0 := by

  unfold h3BKMFrequencyShell

  rw [
    h3BKMFrequencyCutoffBump_eq_one_of_norm_le
      hR hξ
  ]

  ring

/-- The shell is `C∞`. -/
theorem h3BKMFrequencyShell_contDiff
    {R : ℝ}
    (hR : 0 < R) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (h3BKMFrequencyShell R hR) := by

  unfold h3BKMFrequencyShell

  exact
    (
      h3BKMFrequencyCutoffBump_contDiff
        (mul_pos (by norm_num) hR)
    ).mul
      (
        contDiff_const.sub
          (h3BKMFrequencyCutoffBump_contDiff hR)
      )

/-- The shell has compact support because its outer cutoff does. -/
theorem h3BKMFrequencyShell_hasCompactSupport
    {R : ℝ}
    (hR : 0 < R) :
    HasCompactSupport
      (h3BKMFrequencyShell R hR) := by

  unfold h3BKMFrequencyShell

  exact
    (
      h3BKMFrequencyCutoffBump_hasCompactSupport
        (mul_pos (by norm_num) hR)
    ).mul_right

/-- The smooth compact shell packaged as a real Schwartz function. -/
noncomputable def h3BKMFrequencyShellSchwartz
    (R : ℝ)
    (hR : 0 < R) :
    𝓢(H3FourierPoint3, ℝ) :=
  (h3BKMFrequencyShell_hasCompactSupport hR).toSchwartzMap
    (h3BKMFrequencyShell_contDiff hR)

@[simp]
theorem h3BKMFrequencyShellSchwartz_apply
    {R : ℝ}
    (hR : 0 < R)
    (ξ : H3FourierPoint3) :
    h3BKMFrequencyShellSchwartz R hR ξ
      =
    h3BKMFrequencyShell R hR ξ := by
  rfl

/-- The Schwartz shell also vanishes on the inner ball. -/
theorem h3BKMFrequencyShellSchwartz_eq_zero_of_norm_le
    {R : ℝ}
    (hR : 0 < R)
    {ξ : H3FourierPoint3}
    (hξ : ‖ξ‖ ≤ R) :
    h3BKMFrequencyShellSchwartz R hR ξ = 0 := by

  rw [
    h3BKMFrequencyShellSchwartz_apply,
    h3BKMFrequencyShell_eq_zero_of_norm_le
      hR hξ
  ]

end

end Euclidean
end Bridge
end PrimeTensor
