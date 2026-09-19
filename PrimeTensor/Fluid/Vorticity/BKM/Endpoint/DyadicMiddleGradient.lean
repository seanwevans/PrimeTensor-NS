import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.DyadicShellLog

/-!
# BKM endpoint: middle-frequency gradient proxies

The middle dyadic convolution estimate is now in exact logarithmic form.  This
file packages the three two-vorticity combinations dictated by the
Biot--Savart identities.

The Fourier curl amplitudes are

    C₀₁ = -ω_z,
    C₀₂ =  ω_y,
    C₁₂ = -ω_x.

Consequently the three localized velocity-gradient components are represented
by the sign patterns

    j = 0 : -Kᵢ₁ * ω_z + Kᵢ₂ * ω_y,
    j = 1 :  Kᵢ₀ * ω_z - Kᵢ₂ * ω_x,
    j = 2 : -Kᵢ₀ * ω_y + Kᵢ₁ * ω_x.

Each constituent shell sum is bounded by the same logarithmic width times the
physical vorticity envelope and the universal dyadic kernel constant.  A
triangle inequality therefore costs only a factor of two.

This is the middle-frequency gradient estimate, still separated from the low-
and high-frequency tails.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointDyadicMiddleGradient
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceBKMEndpointDyadicMiddleGradient :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Exact logarithmic width of the dyadic middle-frequency window. -/
noncomputable def h3BKMMiddleDyadicLogWidth
    (lo hi : ℕ) : ℝ :=
  (
    Real.log 2
      + Real.log (h3BKMDyadicRadius hi)
      - Real.log (h3BKMDyadicRadius lo)
  ) / Real.log 2

/-- The logarithmic width is exactly the real-valued shell count. -/
theorem h3BKMMiddleDyadicLogWidth_eq_shellCount
    {lo hi : ℕ}
    (hlohi : lo ≤ hi) :
    h3BKMMiddleDyadicLogWidth lo hi
      =
    ((hi + 1 - lo : ℕ) : ℝ) := by

  unfold h3BKMMiddleDyadicLogWidth

  exact
    (h3BKMMiddleDyadicShellCount_eq_log_width
      hlohi).symm

/-- The middle-frequency logarithmic width is nonnegative. -/
theorem h3BKMMiddleDyadicLogWidth_nonneg
    {lo hi : ℕ}
    (hlohi : lo ≤ hi) :
    0 ≤ h3BKMMiddleDyadicLogWidth lo hi := by

  rw [
    h3BKMMiddleDyadicLogWidth_eq_shellCount
      hlohi
  ]

  positivity

/--
Middle-frequency proxy for the gradient of target velocity component `0`.
-/
noncomputable def h3BKMMiddleDyadicGradientComponent0
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (lo hi : ℕ)
    (i : Fin 3)
    (x : Point3) : ℂ :=
  -
    h3BKMMiddleDyadicShellSum
      lo hi i 1
      (h3BKMPhysicalVorticityZ u t)
      x
    +
    h3BKMMiddleDyadicShellSum
      lo hi i 2
      (h3BKMPhysicalVorticityY u t)
      x

/--
Middle-frequency proxy for the gradient of target velocity component `1`.
-/
noncomputable def h3BKMMiddleDyadicGradientComponent1
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (lo hi : ℕ)
    (i : Fin 3)
    (x : Point3) : ℂ :=
  h3BKMMiddleDyadicShellSum
      lo hi i 0
      (h3BKMPhysicalVorticityZ u t)
      x
    -
  h3BKMMiddleDyadicShellSum
      lo hi i 2
      (h3BKMPhysicalVorticityX u t)
      x

/--
Middle-frequency proxy for the gradient of target velocity component `2`.
-/
noncomputable def h3BKMMiddleDyadicGradientComponent2
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (lo hi : ℕ)
    (i : Fin 3)
    (x : Point3) : ℂ :=
  -
    h3BKMMiddleDyadicShellSum
      lo hi i 0
      (h3BKMPhysicalVorticityY u t)
      x
    +
    h3BKMMiddleDyadicShellSum
      lo hi i 1
      (h3BKMPhysicalVorticityX u t)
      x

/-- Component `0` middle-frequency gradient bound. -/
theorem norm_h3BKMMiddleDyadicGradientComponent0_le
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    {lo hi : ℕ}
    (hlohi : lo ≤ hi)
    (hEnvelope : VorticityEnvelope u g t)
    (i : Fin 3)
    (x : Point3) :
    ‖h3BKMMiddleDyadicGradientComponent0
        u t lo hi i x‖
      ≤
    2
      * h3BKMMiddleDyadicLogWidth lo hi
      * (g t * h3BKMDyadicKernelUnitMassConstant) := by

  have hZ :
      ‖h3BKMMiddleDyadicShellSum
          lo hi i 1
          (h3BKMPhysicalVorticityZ u t)
          x‖
        ≤
      h3BKMMiddleDyadicLogWidth lo hi
        * (g t * h3BKMDyadicKernelUnitMassConstant) := by
    simpa [h3BKMMiddleDyadicLogWidth] using
      norm_h3BKMMiddleDyadicShellSum_vorticityZ_le_log_width_mul
        hlohi hEnvelope i 1 x

  have hY :
      ‖h3BKMMiddleDyadicShellSum
          lo hi i 2
          (h3BKMPhysicalVorticityY u t)
          x‖
        ≤
      h3BKMMiddleDyadicLogWidth lo hi
        * (g t * h3BKMDyadicKernelUnitMassConstant) := by
    simpa [h3BKMMiddleDyadicLogWidth] using
      norm_h3BKMMiddleDyadicShellSum_vorticityY_le_log_width_mul
        hlohi hEnvelope i 2 x

  unfold h3BKMMiddleDyadicGradientComponent0

  calc
    ‖-
        h3BKMMiddleDyadicShellSum
          lo hi i 1
          (h3BKMPhysicalVorticityZ u t)
          x
      +
        h3BKMMiddleDyadicShellSum
          lo hi i 2
          (h3BKMPhysicalVorticityY u t)
          x‖
        ≤
      ‖-
        h3BKMMiddleDyadicShellSum
          lo hi i 1
          (h3BKMPhysicalVorticityZ u t)
          x‖
        +
      ‖h3BKMMiddleDyadicShellSum
          lo hi i 2
          (h3BKMPhysicalVorticityY u t)
          x‖ :=
      norm_add_le _ _

    _ =
      ‖h3BKMMiddleDyadicShellSum
          lo hi i 1
          (h3BKMPhysicalVorticityZ u t)
          x‖
        +
      ‖h3BKMMiddleDyadicShellSum
          lo hi i 2
          (h3BKMPhysicalVorticityY u t)
          x‖ := by
      rw [norm_neg]

    _ ≤
      h3BKMMiddleDyadicLogWidth lo hi
          * (g t * h3BKMDyadicKernelUnitMassConstant)
        +
      h3BKMMiddleDyadicLogWidth lo hi
          * (g t * h3BKMDyadicKernelUnitMassConstant) :=
      add_le_add hZ hY

    _ =
      2
        * h3BKMMiddleDyadicLogWidth lo hi
        * (g t * h3BKMDyadicKernelUnitMassConstant) := by
      ring

/-- Component `1` middle-frequency gradient bound. -/
theorem norm_h3BKMMiddleDyadicGradientComponent1_le
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    {lo hi : ℕ}
    (hlohi : lo ≤ hi)
    (hEnvelope : VorticityEnvelope u g t)
    (i : Fin 3)
    (x : Point3) :
    ‖h3BKMMiddleDyadicGradientComponent1
        u t lo hi i x‖
      ≤
    2
      * h3BKMMiddleDyadicLogWidth lo hi
      * (g t * h3BKMDyadicKernelUnitMassConstant) := by

  have hZ :
      ‖h3BKMMiddleDyadicShellSum
          lo hi i 0
          (h3BKMPhysicalVorticityZ u t)
          x‖
        ≤
      h3BKMMiddleDyadicLogWidth lo hi
        * (g t * h3BKMDyadicKernelUnitMassConstant) := by
    simpa [h3BKMMiddleDyadicLogWidth] using
      norm_h3BKMMiddleDyadicShellSum_vorticityZ_le_log_width_mul
        hlohi hEnvelope i 0 x

  have hX :
      ‖h3BKMMiddleDyadicShellSum
          lo hi i 2
          (h3BKMPhysicalVorticityX u t)
          x‖
        ≤
      h3BKMMiddleDyadicLogWidth lo hi
        * (g t * h3BKMDyadicKernelUnitMassConstant) := by
    simpa [h3BKMMiddleDyadicLogWidth] using
      norm_h3BKMMiddleDyadicShellSum_vorticityX_le_log_width_mul
        hlohi hEnvelope i 2 x

  unfold h3BKMMiddleDyadicGradientComponent1

  calc
    ‖h3BKMMiddleDyadicShellSum
          lo hi i 0
          (h3BKMPhysicalVorticityZ u t)
          x
      -
        h3BKMMiddleDyadicShellSum
          lo hi i 2
          (h3BKMPhysicalVorticityX u t)
          x‖
        ≤
      ‖h3BKMMiddleDyadicShellSum
          lo hi i 0
          (h3BKMPhysicalVorticityZ u t)
          x‖
        +
      ‖h3BKMMiddleDyadicShellSum
          lo hi i 2
          (h3BKMPhysicalVorticityX u t)
          x‖ :=
      norm_sub_le _ _

    _ ≤
      h3BKMMiddleDyadicLogWidth lo hi
          * (g t * h3BKMDyadicKernelUnitMassConstant)
        +
      h3BKMMiddleDyadicLogWidth lo hi
          * (g t * h3BKMDyadicKernelUnitMassConstant) :=
      add_le_add hZ hX

    _ =
      2
        * h3BKMMiddleDyadicLogWidth lo hi
        * (g t * h3BKMDyadicKernelUnitMassConstant) := by
      ring

/-- Component `2` middle-frequency gradient bound. -/
theorem norm_h3BKMMiddleDyadicGradientComponent2_le
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    {lo hi : ℕ}
    (hlohi : lo ≤ hi)
    (hEnvelope : VorticityEnvelope u g t)
    (i : Fin 3)
    (x : Point3) :
    ‖h3BKMMiddleDyadicGradientComponent2
        u t lo hi i x‖
      ≤
    2
      * h3BKMMiddleDyadicLogWidth lo hi
      * (g t * h3BKMDyadicKernelUnitMassConstant) := by

  have hY :
      ‖h3BKMMiddleDyadicShellSum
          lo hi i 0
          (h3BKMPhysicalVorticityY u t)
          x‖
        ≤
      h3BKMMiddleDyadicLogWidth lo hi
        * (g t * h3BKMDyadicKernelUnitMassConstant) := by
    simpa [h3BKMMiddleDyadicLogWidth] using
      norm_h3BKMMiddleDyadicShellSum_vorticityY_le_log_width_mul
        hlohi hEnvelope i 0 x

  have hX :
      ‖h3BKMMiddleDyadicShellSum
          lo hi i 1
          (h3BKMPhysicalVorticityX u t)
          x‖
        ≤
      h3BKMMiddleDyadicLogWidth lo hi
        * (g t * h3BKMDyadicKernelUnitMassConstant) := by
    simpa [h3BKMMiddleDyadicLogWidth] using
      norm_h3BKMMiddleDyadicShellSum_vorticityX_le_log_width_mul
        hlohi hEnvelope i 1 x

  unfold h3BKMMiddleDyadicGradientComponent2

  calc
    ‖-
        h3BKMMiddleDyadicShellSum
          lo hi i 0
          (h3BKMPhysicalVorticityY u t)
          x
      +
        h3BKMMiddleDyadicShellSum
          lo hi i 1
          (h3BKMPhysicalVorticityX u t)
          x‖
        ≤
      ‖-
        h3BKMMiddleDyadicShellSum
          lo hi i 0
          (h3BKMPhysicalVorticityY u t)
          x‖
        +
      ‖h3BKMMiddleDyadicShellSum
          lo hi i 1
          (h3BKMPhysicalVorticityX u t)
          x‖ :=
      norm_add_le _ _

    _ =
      ‖h3BKMMiddleDyadicShellSum
          lo hi i 0
          (h3BKMPhysicalVorticityY u t)
          x‖
        +
      ‖h3BKMMiddleDyadicShellSum
          lo hi i 1
          (h3BKMPhysicalVorticityX u t)
          x‖ := by
      rw [norm_neg]

    _ ≤
      h3BKMMiddleDyadicLogWidth lo hi
          * (g t * h3BKMDyadicKernelUnitMassConstant)
        +
      h3BKMMiddleDyadicLogWidth lo hi
          * (g t * h3BKMDyadicKernelUnitMassConstant) :=
      add_le_add hY hX

    _ =
      2
        * h3BKMMiddleDyadicLogWidth lo hi
        * (g t * h3BKMDyadicKernelUnitMassConstant) := by
      ring

end

end Euclidean
end Bridge
end PrimeTensor
