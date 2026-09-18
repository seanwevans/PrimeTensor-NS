import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.LocalizedMultiplierSmooth
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# BKM endpoint: inverse-Fourier dyadic kernel

The localized Biot--Savart coordinate multiplier is now a genuine complex
Schwartz function.  Mathlib's Fourier automorphism of Schwartz space therefore
provides its inverse Fourier transform as another Schwartz function.

For each positive shell radius `R` and coordinate pair `(i,k)`, define

    Kᵢₖ,R = 𝓕⁻¹ Mᵢₖ,R.

This file records the two structural facts needed by the physical convolution
argument:

* `Kᵢₖ,R` is itself Schwartz;
* consequently its underlying function is Bochner-integrable, i.e. genuinely
  `L¹`.

The next checkpoint transports this Euclidean kernel to physical `Point3`
through the canonical volume-preserving carrier equivalence and identifies its
`L¹` mass there.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff

noncomputable section

noncomputable local instance axisFintypeBKMEndpointDyadicKernel
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/--
Inverse Fourier transform of one dyadically localized BKM coordinate
multiplier, retained as a Schwartz function.
-/
noncomputable def h3BKMDyadicKernelSchwartz
    (R : ℝ)
    (hR : 0 < R)
    (i k : Fin 3) :
    𝓢(H3FourierPoint3, ℂ) :=
  FourierTransformInv.fourierInv
    (h3BKMLocalizedCoordinateMultiplierSchwartz
      R hR i k)

/-- Pointwise kernel underlying the Schwartz inverse Fourier transform. -/
noncomputable def h3BKMDyadicKernel
    (R : ℝ)
    (hR : 0 < R)
    (i k : Fin 3)
    (x : H3FourierPoint3) : ℂ :=
  h3BKMDyadicKernelSchwartz R hR i k x

@[simp]
theorem h3BKMDyadicKernel_apply
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3)
    (x : H3FourierPoint3) :
    h3BKMDyadicKernel R hR i k x
      =
    h3BKMDyadicKernelSchwartz R hR i k x := by
  rfl

/-- The dyadic kernel is smooth because it is Schwartz. -/
theorem h3BKMDyadicKernel_contDiff
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    ContDiff ℝ ∞
      (h3BKMDyadicKernel R hR i k) := by

  exact
    (h3BKMDyadicKernelSchwartz
      R hR i k).smooth ⊤

/-- Every dyadic BKM kernel is genuinely integrable. -/
theorem h3BKMDyadicKernel_integrable
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    Integrable
      (h3BKMDyadicKernel R hR i k)
      (volume : Measure H3FourierPoint3) := by

  change
    Integrable
      (h3BKMDyadicKernelSchwartz R hR i k :
        H3FourierPoint3 → ℂ)
      (volume : Measure H3FourierPoint3)

  exact
    (h3BKMDyadicKernelSchwartz
      R hR i k).integrable

/-- The `L¹` kernel mass is finite in the ordinary real-integral sense. -/
theorem integrable_norm_h3BKMDyadicKernel
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    Integrable
      (fun x : H3FourierPoint3 =>
        ‖h3BKMDyadicKernel R hR i k x‖)
      (volume : Measure H3FourierPoint3) := by

  exact
    (h3BKMDyadicKernel_integrable
      hR i k).norm

/-- Named real `L¹` mass of one dyadic BKM kernel. -/
noncomputable def h3BKMDyadicKernelL1Mass
    (R : ℝ)
    (hR : 0 < R)
    (i k : Fin 3) : ℝ :=
  ∫ x : H3FourierPoint3,
    ‖h3BKMDyadicKernel R hR i k x‖
    ∂(volume : Measure H3FourierPoint3)

/-- Kernel mass is nonnegative. -/
theorem h3BKMDyadicKernelL1Mass_nonneg
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    0 ≤ h3BKMDyadicKernelL1Mass R hR i k := by

  unfold h3BKMDyadicKernelL1Mass

  exact
    integral_nonneg
      (fun _ => norm_nonneg _)

end

end Euclidean
end Bridge
end PrimeTensor
