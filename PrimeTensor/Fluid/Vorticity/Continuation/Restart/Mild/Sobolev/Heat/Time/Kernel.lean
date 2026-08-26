import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Heat.Divergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Time integration of the H³ heat-divergence singular kernel

`HeatDivergence` closes the one-time estimate

    ‖e^{νtΔ} div F‖_{H³}
      ≤ 3 (sqrt (ν t))⁻¹ ‖F‖_{H³},

and, after inserting the antisymmetric vorticity flux,

    ‖Nν(t; U, Ω)‖_{H³}
      ≤ 96 C_deweight (sqrt (ν t))⁻¹ ‖U‖ ‖Ω‖.

The remaining scalar time singularity is integrable.  This file proves the
exact identities

    ∫₀ᵗ (sqrt (t-s))⁻¹ ds = 2 sqrt t

and, for positive viscosity,

    ∫₀ᵗ (sqrt (ν (t-s)))⁻¹ ds
      = 2 (sqrt ν)⁻¹ sqrt t.

This is deliberately kept separate from the path-space Duhamel construction.
The newer spectral flux layer is indexed by `Axis Depth.three`, whereas the
older normalized path API is indexed by `Fin 3`.  The next rung will insert
that finite-index equivalence and then use the scalar identity proved here to
build the actual Bochner Duhamel path.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory
open scoped Interval

noncomputable section

/-- Reciprocal square root as the real power `x ^ (-1/2)` on nonnegative inputs. -/
theorem h3_inv_sqrt_eq_rpow_neg_half
    {x : ℝ}
    (hx : 0 ≤ x) :
    (Real.sqrt x)⁻¹ = x ^ (-(1 / 2 : ℝ)) := by
  rw [Real.sqrt_eq_rpow]
  exact (Real.rpow_neg hx (1 / 2 : ℝ)).symm

/--
The non-viscous mild singularity integrates exactly to `2 sqrt t`.
-/
theorem h3_timeSingularKernel_integral
    {t : ℝ}
    (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t,
        (Real.sqrt (t - s))⁻¹)
      =
    2 * Real.sqrt t := by
  have hpoint :
      ∀ s ∈ Set.uIcc (0 : ℝ) t,
        (Real.sqrt (t - s))⁻¹
          =
        (t - s) ^ (-(1 / 2 : ℝ)) := by
    intro s hs
    rw [Set.uIcc_of_le ht] at hs
    exact
      h3_inv_sqrt_eq_rpow_neg_half
        (sub_nonneg.mpr hs.2)

  calc
    (∫ s in (0 : ℝ)..t,
        (Real.sqrt (t - s))⁻¹)
        =
      ∫ s in (0 : ℝ)..t,
        (t - s) ^ (-(1 / 2 : ℝ)) := by
          exact intervalIntegral.integral_congr hpoint
    _ =
      ∫ x in (0 : ℝ)..t,
        x ^ (-(1 / 2 : ℝ)) := by
          simpa using
            (intervalIntegral.integral_comp_sub_left
              (a := (0 : ℝ))
              (b := t)
              (fun x : ℝ => x ^ (-(1 / 2 : ℝ)))
              t)
    _ =
      (t ^ ((-(1 / 2 : ℝ)) + 1) -
          (0 : ℝ) ^ ((-(1 / 2 : ℝ)) + 1)) /
        ((-(1 / 2 : ℝ)) + 1) := by
          exact
            integral_rpow
              (a := (0 : ℝ))
              (b := t)
              (r := (-(1 / 2 : ℝ)))
              (Or.inl (by norm_num))
    _ = 2 * Real.sqrt t := by
          rw [show (-(1 / 2 : ℝ)) + 1 = 1 / 2 by ring]
          rw [Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0)]
          rw [← Real.sqrt_eq_rpow]
          ring

/--
Positive viscosity separates from the time singularity exactly.
-/
theorem h3_viscousTimeSingularKernel_integral
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t,
        (Real.sqrt (ν * (t - s)))⁻¹)
      =
    2 * (Real.sqrt ν)⁻¹ * Real.sqrt t := by
  have hpoint :
      ∀ s ∈ Set.uIcc (0 : ℝ) t,
        (Real.sqrt (ν * (t - s)))⁻¹
          =
        (Real.sqrt ν)⁻¹ *
          (Real.sqrt (t - s))⁻¹ := by
    intro s _hs
    rw [Real.sqrt_mul hν.le]
    simp [mul_comm]

  calc
    (∫ s in (0 : ℝ)..t,
        (Real.sqrt (ν * (t - s)))⁻¹)
        =
      ∫ s in (0 : ℝ)..t,
        (Real.sqrt ν)⁻¹ *
          (Real.sqrt (t - s))⁻¹ := by
          exact intervalIntegral.integral_congr hpoint
    _ =
      (Real.sqrt ν)⁻¹ *
        (∫ s in (0 : ℝ)..t,
          (Real.sqrt (t - s))⁻¹) := by
          rw [intervalIntegral.integral_const_mul]
    _ =
      (Real.sqrt ν)⁻¹ *
        (2 * Real.sqrt t) := by
          rw [h3_timeSingularKernel_integral ht]
    _ =
      2 * (Real.sqrt ν)⁻¹ * Real.sqrt t := by
          ring

/--
The scalar coefficient obtained after integrating the complete one-time
vorticity kernel from `HeatDivergence`.
-/
def h3VorticityDuhamelCoefficient
    (ν : ℝ) : ℝ :=
  192 * h3SobolevDeweightingConstant *
    (Real.sqrt ν)⁻¹

/-- The concrete Duhamel coefficient is nonnegative at positive viscosity. -/
theorem h3VorticityDuhamelCoefficient_nonneg
    {ν : ℝ}
    (hν : 0 < ν) :
    0 ≤ h3VorticityDuhamelCoefficient ν := by
  unfold h3VorticityDuhamelCoefficient
  positivity [h3SobolevDeweightingConstant_nonneg]

/--
Scalar integration of the complete `96 C_deweight` heat-divergence envelope.
-/
theorem h3_vorticityKernelEnvelope_integral
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t,
        96 * h3SobolevDeweightingConstant *
          (Real.sqrt (ν * (t - s)))⁻¹)
      =
    h3VorticityDuhamelCoefficient ν *
      Real.sqrt t := by
  calc
    (∫ s in (0 : ℝ)..t,
        96 * h3SobolevDeweightingConstant *
          (Real.sqrt (ν * (t - s)))⁻¹)
        =
      (96 * h3SobolevDeweightingConstant) *
        (∫ s in (0 : ℝ)..t,
          (Real.sqrt (ν * (t - s)))⁻¹) := by
            rw [intervalIntegral.integral_const_mul]
    _ =
      (96 * h3SobolevDeweightingConstant) *
        (2 * (Real.sqrt ν)⁻¹ * Real.sqrt t) := by
          rw [h3_viscousTimeSingularKernel_integral hν ht]
    _ =
      h3VorticityDuhamelCoefficient ν *
        Real.sqrt t := by
          unfold h3VorticityDuhamelCoefficient
          ring

end

end Euclidean
end Bridge
end PrimeTensor
