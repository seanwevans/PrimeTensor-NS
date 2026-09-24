import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Dyadic.Shell.Count

/-!
# BKM endpoint: convert dyadic shell width into a logarithm

The middle-frequency shell estimate is now written with the exact natural
cardinality

    hi + 1 - lo.

This file identifies that count with the logarithmic width of the corresponding
dyadic radii.  Since

    Rₙ = 2ⁿ,

we have

    log Rₙ = n log 2

and therefore, for `lo ≤ hi`,

    (hi + 1 - lo) log 2
      = log 2 + log R_hi - log R_lo.

Dividing by the positive constant `log 2` gives the exact logarithmic shell
factor used by the middle-frequency BKM estimate.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointDyadicShellLog
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceBKMEndpointDyadicShellLog :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The real logarithm of the standard dyadic radius `2ⁿ`. -/
theorem h3BKMDyadicRadius_log
    (n : ℕ) :
    Real.log (h3BKMDyadicRadius n)
      =
    (n : ℝ) * Real.log 2 := by

  unfold h3BKMDyadicRadius

  simpa using
    (Real.log_pow (2 : ℝ) n)

/-- Cast the exact middle-shell count into the reals. -/
theorem h3BKMMiddleDyadicShellCount_cast
    {lo hi : ℕ}
    (hlohi : lo ≤ hi) :
    ((hi + 1 - lo : ℕ) : ℝ)
      =
    1 + (hi : ℝ) - (lo : ℝ) := by

  rw [
    Nat.cast_sub
      (show lo ≤ hi + 1 by omega)
  ]

  push_cast
  ring

/--
The middle dyadic shell count times `log 2` is exactly the logarithmic width
between the endpoint radii, with the one-shell offset made explicit.
-/
theorem h3BKMMiddleDyadicShellCount_mul_log_two
    {lo hi : ℕ}
    (hlohi : lo ≤ hi) :
    ((hi + 1 - lo : ℕ) : ℝ) * Real.log 2
      =
    Real.log 2
      + Real.log (h3BKMDyadicRadius hi)
      - Real.log (h3BKMDyadicRadius lo) := by

  rw [
    h3BKMMiddleDyadicShellCount_cast hlohi,
    h3BKMDyadicRadius_log hi,
    h3BKMDyadicRadius_log lo
  ]

  ring

/--
Exact logarithmic form of the middle dyadic shell count.
-/
theorem h3BKMMiddleDyadicShellCount_eq_log_width
    {lo hi : ℕ}
    (hlohi : lo ≤ hi) :
    ((hi + 1 - lo : ℕ) : ℝ)
      =
    (
      Real.log 2
        + Real.log (h3BKMDyadicRadius hi)
        - Real.log (h3BKMDyadicRadius lo)
    ) / Real.log 2 := by

  apply
    (eq_div_iff
      (ne_of_gt
        (Real.log_pos
          (by norm_num : (1 : ℝ) < 2)))).2

  exact
    h3BKMMiddleDyadicShellCount_mul_log_two
      hlohi

/--
The generic middle-frequency dyadic convolution estimate with its shell count
replaced by the exact logarithmic width.
-/
theorem norm_h3BKMMiddleDyadicShellSum_le_log_width_mul
    {lo hi : ℕ}
    (hlohi : lo ≤ hi)
    (i k : Fin 3)
    (f : Point3 → ℂ)
    (M : ℝ)
    (hM : 0 ≤ M)
    (hf : ∀ z : Point3, ‖f z‖ ≤ M)
    (x : Point3) :
    ‖h3BKMMiddleDyadicShellSum lo hi i k f x‖
      ≤
    (
      (
        Real.log 2
          + Real.log (h3BKMDyadicRadius hi)
          - Real.log (h3BKMDyadicRadius lo)
      ) / Real.log 2
    )
      * (M * h3BKMDyadicKernelUnitMassConstant) := by

  rw [
    ← h3BKMMiddleDyadicShellCount_eq_log_width
      hlohi
  ]

  exact
    norm_h3BKMMiddleDyadicShellSum_le_shellCount_mul
      lo hi i k f M hM hf x

/-- X-vorticity middle-frequency estimate in exact logarithmic form. -/
theorem norm_h3BKMMiddleDyadicShellSum_vorticityX_le_log_width_mul
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    {lo hi : ℕ}
    (hlohi : lo ≤ hi)
    (hEnvelope : VorticityEnvelope u g t)
    (i k : Fin 3)
    (x : Point3) :
    ‖h3BKMMiddleDyadicShellSum
        lo hi i k (h3BKMPhysicalVorticityX u t) x‖
      ≤
    (
      (
        Real.log 2
          + Real.log (h3BKMDyadicRadius hi)
          - Real.log (h3BKMDyadicRadius lo)
      ) / Real.log 2
    )
      * (g t * h3BKMDyadicKernelUnitMassConstant) := by

  exact
    norm_h3BKMMiddleDyadicShellSum_le_log_width_mul
      hlohi
      i
      k
      (h3BKMPhysicalVorticityX u t)
      (g t)
      (h3BKM_vorticityEnvelope_nonneg hEnvelope)
      (norm_h3BKMPhysicalVorticityX_le hEnvelope)
      x

/-- Y-vorticity middle-frequency estimate in exact logarithmic form. -/
theorem norm_h3BKMMiddleDyadicShellSum_vorticityY_le_log_width_mul
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    {lo hi : ℕ}
    (hlohi : lo ≤ hi)
    (hEnvelope : VorticityEnvelope u g t)
    (i k : Fin 3)
    (x : Point3) :
    ‖h3BKMMiddleDyadicShellSum
        lo hi i k (h3BKMPhysicalVorticityY u t) x‖
      ≤
    (
      (
        Real.log 2
          + Real.log (h3BKMDyadicRadius hi)
          - Real.log (h3BKMDyadicRadius lo)
      ) / Real.log 2
    )
      * (g t * h3BKMDyadicKernelUnitMassConstant) := by

  exact
    norm_h3BKMMiddleDyadicShellSum_le_log_width_mul
      hlohi
      i
      k
      (h3BKMPhysicalVorticityY u t)
      (g t)
      (h3BKM_vorticityEnvelope_nonneg hEnvelope)
      (norm_h3BKMPhysicalVorticityY_le hEnvelope)
      x

/-- Z-vorticity middle-frequency estimate in exact logarithmic form. -/
theorem norm_h3BKMMiddleDyadicShellSum_vorticityZ_le_log_width_mul
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    {lo hi : ℕ}
    (hlohi : lo ≤ hi)
    (hEnvelope : VorticityEnvelope u g t)
    (i k : Fin 3)
    (x : Point3) :
    ‖h3BKMMiddleDyadicShellSum
        lo hi i k (h3BKMPhysicalVorticityZ u t) x‖
      ≤
    (
      (
        Real.log 2
          + Real.log (h3BKMDyadicRadius hi)
          - Real.log (h3BKMDyadicRadius lo)
      ) / Real.log 2
    )
      * (g t * h3BKMDyadicKernelUnitMassConstant) := by

  exact
    norm_h3BKMMiddleDyadicShellSum_le_log_width_mul
      hlohi
      i
      k
      (h3BKMPhysicalVorticityZ u t)
      (g t)
      (h3BKM_vorticityEnvelope_nonneg hEnvelope)
      (norm_h3BKMPhysicalVorticityZ_le hEnvelope)
      x

end

end Euclidean
end Bridge
end PrimeTensor
