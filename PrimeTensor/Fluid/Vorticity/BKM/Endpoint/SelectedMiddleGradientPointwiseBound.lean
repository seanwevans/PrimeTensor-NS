import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.HighFrequencyGradientCutoffSelection
import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.DyadicMiddleGradient

/-!
# BKM endpoint: pointwise selected middle-gradient proxy bound

The bundled middle-gradient `L²` state is useful for spectral bookkeeping, but
its chosen `Lp` representative is only controlled almost everywhere.  For the
final actual-gradient endpoint we need an everywhere pointwise bound.

The physical convolution proxy from `DyadicMiddleGradient` is already a literal
function on `Point3` and already satisfies, for every point,

    ‖middleProxy_j(t,lo,hi,i,x)‖
      ≤ 2 * width(lo,hi) * (g(t) * C_BKM).

This file simply inserts the canonical upper cutoff

    hi = h3BKMUpperCutoffIndex A

and the previously proved logarithmic width estimate.  Thus all three middle
gradient proxies satisfy an everywhere logarithmic bound with no `Lp`
representative ambiguity.

The next checkpoint only has to identify the selected inverse-Fourier middle
term with this concrete physical convolution proxy.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointSelectedMiddleGradientPointwiseBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

private theorem selected_middle_pointwise_scale_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hEnvelope : VorticityEnvelope u g t) :
    0 ≤ 2 * (g t * h3BKMDyadicKernelUnitMassConstant) := by
  exact
    mul_nonneg
      (by norm_num)
      (mul_nonneg
        (h3BKM_vorticityEnvelope_nonneg hEnvelope)
        h3BKMDyadicKernelUnitMassConstant_nonneg)

/-- Everywhere selected logarithmic bound for middle gradient component `0`. -/
theorem norm_h3BKMMiddleDyadicGradientComponent0_selected_le
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hEnvelope : VorticityEnvelope u g t)
    (A : ℝ)
    (i : Fin 3)
    (x : Point3) :
    ‖h3BKMMiddleDyadicGradientComponent0
        u t
        0
        (h3BKMUpperCutoffIndex A)
        i x‖
      ≤
    2
      * (4 * Real.logb 2 (h3BKMUpperCutoffScale A) + 2)
      * (g t * h3BKMDyadicKernelUnitMassConstant) := by

  have hBase :=
    norm_h3BKMMiddleDyadicGradientComponent0_le
      (u := u)
      (g := g)
      (t := t)
      (lo := 0)
      (hi := h3BKMUpperCutoffIndex A)
      (Nat.zero_le (h3BKMUpperCutoffIndex A))
      hEnvelope
      i x

  have hWidth :=
    h3BKMMiddleDyadicLogWidth_zero_selected_le A

  have hScale :
      0 ≤ 2 * (g t * h3BKMDyadicKernelUnitMassConstant) :=
    selected_middle_pointwise_scale_nonneg hEnvelope

  calc
    ‖h3BKMMiddleDyadicGradientComponent0
        u t
        0
        (h3BKMUpperCutoffIndex A)
        i x‖
        ≤
      2
        * h3BKMMiddleDyadicLogWidth
            0
            (h3BKMUpperCutoffIndex A)
        * (g t * h3BKMDyadicKernelUnitMassConstant) :=
      hBase

    _ =
      h3BKMMiddleDyadicLogWidth
          0
          (h3BKMUpperCutoffIndex A)
        * (2 * (g t * h3BKMDyadicKernelUnitMassConstant)) := by
      ring

    _ ≤
      (4 * Real.logb 2 (h3BKMUpperCutoffScale A) + 2)
        * (2 * (g t * h3BKMDyadicKernelUnitMassConstant)) :=
      mul_le_mul_of_nonneg_right
        hWidth
        hScale

    _ =
      2
        * (4 * Real.logb 2 (h3BKMUpperCutoffScale A) + 2)
        * (g t * h3BKMDyadicKernelUnitMassConstant) := by
      ring

/-- Everywhere selected logarithmic bound for middle gradient component `1`. -/
theorem norm_h3BKMMiddleDyadicGradientComponent1_selected_le
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hEnvelope : VorticityEnvelope u g t)
    (A : ℝ)
    (i : Fin 3)
    (x : Point3) :
    ‖h3BKMMiddleDyadicGradientComponent1
        u t
        0
        (h3BKMUpperCutoffIndex A)
        i x‖
      ≤
    2
      * (4 * Real.logb 2 (h3BKMUpperCutoffScale A) + 2)
      * (g t * h3BKMDyadicKernelUnitMassConstant) := by

  have hBase :=
    norm_h3BKMMiddleDyadicGradientComponent1_le
      (u := u)
      (g := g)
      (t := t)
      (lo := 0)
      (hi := h3BKMUpperCutoffIndex A)
      (Nat.zero_le (h3BKMUpperCutoffIndex A))
      hEnvelope
      i x

  have hWidth :=
    h3BKMMiddleDyadicLogWidth_zero_selected_le A

  have hScale :
      0 ≤ 2 * (g t * h3BKMDyadicKernelUnitMassConstant) :=
    selected_middle_pointwise_scale_nonneg hEnvelope

  calc
    ‖h3BKMMiddleDyadicGradientComponent1
        u t
        0
        (h3BKMUpperCutoffIndex A)
        i x‖
        ≤
      2
        * h3BKMMiddleDyadicLogWidth
            0
            (h3BKMUpperCutoffIndex A)
        * (g t * h3BKMDyadicKernelUnitMassConstant) :=
      hBase

    _ =
      h3BKMMiddleDyadicLogWidth
          0
          (h3BKMUpperCutoffIndex A)
        * (2 * (g t * h3BKMDyadicKernelUnitMassConstant)) := by
      ring

    _ ≤
      (4 * Real.logb 2 (h3BKMUpperCutoffScale A) + 2)
        * (2 * (g t * h3BKMDyadicKernelUnitMassConstant)) :=
      mul_le_mul_of_nonneg_right
        hWidth
        hScale

    _ =
      2
        * (4 * Real.logb 2 (h3BKMUpperCutoffScale A) + 2)
        * (g t * h3BKMDyadicKernelUnitMassConstant) := by
      ring

/-- Everywhere selected logarithmic bound for middle gradient component `2`. -/
theorem norm_h3BKMMiddleDyadicGradientComponent2_selected_le
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hEnvelope : VorticityEnvelope u g t)
    (A : ℝ)
    (i : Fin 3)
    (x : Point3) :
    ‖h3BKMMiddleDyadicGradientComponent2
        u t
        0
        (h3BKMUpperCutoffIndex A)
        i x‖
      ≤
    2
      * (4 * Real.logb 2 (h3BKMUpperCutoffScale A) + 2)
      * (g t * h3BKMDyadicKernelUnitMassConstant) := by

  have hBase :=
    norm_h3BKMMiddleDyadicGradientComponent2_le
      (u := u)
      (g := g)
      (t := t)
      (lo := 0)
      (hi := h3BKMUpperCutoffIndex A)
      (Nat.zero_le (h3BKMUpperCutoffIndex A))
      hEnvelope
      i x

  have hWidth :=
    h3BKMMiddleDyadicLogWidth_zero_selected_le A

  have hScale :
      0 ≤ 2 * (g t * h3BKMDyadicKernelUnitMassConstant) :=
    selected_middle_pointwise_scale_nonneg hEnvelope

  calc
    ‖h3BKMMiddleDyadicGradientComponent2
        u t
        0
        (h3BKMUpperCutoffIndex A)
        i x‖
        ≤
      2
        * h3BKMMiddleDyadicLogWidth
            0
            (h3BKMUpperCutoffIndex A)
        * (g t * h3BKMDyadicKernelUnitMassConstant) :=
      hBase

    _ =
      h3BKMMiddleDyadicLogWidth
          0
          (h3BKMUpperCutoffIndex A)
        * (2 * (g t * h3BKMDyadicKernelUnitMassConstant)) := by
      ring

    _ ≤
      (4 * Real.logb 2 (h3BKMUpperCutoffScale A) + 2)
        * (2 * (g t * h3BKMDyadicKernelUnitMassConstant)) :=
      mul_le_mul_of_nonneg_right
        hWidth
        hScale

    _ =
      2
        * (4 * Real.logb 2 (h3BKMUpperCutoffScale A) + 2)
        * (g t * h3BKMDyadicKernelUnitMassConstant) := by
      ring

end

end Euclidean
end Bridge
end PrimeTensor
