import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Dyadic.Localization.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Young.Convolution.Representatives

/-!
# BKM endpoint: continuity of endpoint Young convolution in the L² factor

The Fourier-localization side of the dyadic BKM bridge is now continuous on
`L²`.  For the density argument we need the same closure control for the
physical convolution side.

Fix `f ∈ L¹`.  The project's endpoint Young convolution

    g ↦ h3L1L2Convolution f g

is linear in the `L²` input and satisfies

    ‖f * (g - h)‖₂ ≤ ‖f‖₁ ‖g - h‖₂.

This file records the subtraction law, the corresponding difference estimate,
and a Lipschitz/continuity package.  It then specializes those statements to
the dyadic BKM kernel `h3BKMDyadicKernelL1`.

These are precisely the continuity facts needed to extend a Schwartz-class
Fourier convolution identity to arbitrary physical-vorticity `L²` data.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointDyadicYoungContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Translation on Fourier `L²` commutes with subtraction. -/
theorem h3FourierTranslateL2_sub
    (η : H3FourierPoint3)
    (F G : H3FourierComplexL2) :
    h3FourierTranslateL2 η (F - G)
      =
    h3FourierTranslateL2 η F
      -
    h3FourierTranslateL2 η G := by

  unfold h3FourierTranslateL2

  rw [sub_eq_add_neg]
  rw [DomAddAct.vadd_Lp_add]
  rw [DomAddAct.vadd_Lp_neg]
  rw [sub_eq_add_neg]

/-- The endpoint Young integrand is linear under subtraction in the `L²` input. -/
theorem h3L1L2ConvolutionIntegrand_sub_right
    (f : H3FourierComplexL1)
    (F G : H3FourierComplexL2)
    (η : H3FourierPoint3) :
    h3L1L2ConvolutionIntegrand f (F - G) η
      =
    h3L1L2ConvolutionIntegrand f F η
      -
    h3L1L2ConvolutionIntegrand f G η := by

  unfold h3L1L2ConvolutionIntegrand

  rw [h3FourierTranslateL2_sub]

  exact smul_sub _ _ _

/-- Endpoint Young convolution commutes with subtraction in the `L²` input. -/
theorem h3L1L2Convolution_sub_right
    (f : H3FourierComplexL1)
    (F G : H3FourierComplexL2) :
    h3L1L2Convolution f (F - G)
      =
    h3L1L2Convolution f F
      -
    h3L1L2Convolution f G := by

  unfold h3L1L2Convolution

  rw [
    ← integral_sub
      (h3L1L2ConvolutionIntegrand_integrable f F)
      (h3L1L2ConvolutionIntegrand_integrable f G)
  ]

  apply integral_congr_ae

  filter_upwards with η

  exact h3L1L2ConvolutionIntegrand_sub_right f F G η

/-- Difference form of the endpoint Young estimate. -/
theorem norm_h3L1L2Convolution_sub_right_le
    (f : H3FourierComplexL1)
    (F G : H3FourierComplexL2) :
    ‖h3L1L2Convolution f F
        -
      h3L1L2Convolution f G‖
      ≤
    ‖f‖ * ‖F - G‖ := by

  rw [← h3L1L2Convolution_sub_right f F G]

  exact
    norm_h3L1L2Convolution_le
      f
      (F - G)

/-- Fixed-kernel endpoint Young convolution is Lipschitz on `L²`. -/
theorem lipschitzWith_h3L1L2Convolution_right
    (f : H3FourierComplexL1) :
    LipschitzWith
      ⟨‖f‖, norm_nonneg f⟩
      (h3L1L2Convolution f :
        H3FourierComplexL2 →
          H3FourierComplexL2) := by

  apply LipschitzWith.of_dist_le_mul

  intro F G

  rw [dist_eq_norm, dist_eq_norm]

  change
    ‖h3L1L2Convolution f F
        -
      h3L1L2Convolution f G‖
      ≤
    ‖f‖ * ‖F - G‖

  exact
    norm_h3L1L2Convolution_sub_right_le
      f F G

/-- Fixed-kernel endpoint Young convolution is continuous on `L²`. -/
theorem continuous_h3L1L2Convolution_right
    (f : H3FourierComplexL1) :
    Continuous
      (h3L1L2Convolution f :
        H3FourierComplexL2 →
          H3FourierComplexL2) :=
  (lipschitzWith_h3L1L2Convolution_right f).continuous

/-! ## Dyadic BKM specialization -/

/-- One dyadic BKM kernel gives a Lipschitz endpoint convolution operator. -/
theorem lipschitzWith_h3BKMDyadicKernelConvolutionL2
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    LipschitzWith
      ⟨‖h3BKMDyadicKernelL1 R hR i k‖,
        norm_nonneg
          (h3BKMDyadicKernelL1 R hR i k)⟩
      (h3L1L2Convolution
        (h3BKMDyadicKernelL1 R hR i k) :
        H3FourierComplexL2 →
          H3FourierComplexL2) :=
  lipschitzWith_h3L1L2Convolution_right
    (h3BKMDyadicKernelL1 R hR i k)

/-- One dyadic BKM kernel gives a continuous endpoint convolution operator. -/
theorem continuous_h3BKMDyadicKernelConvolutionL2
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    Continuous
      (h3L1L2Convolution
        (h3BKMDyadicKernelL1 R hR i k) :
        H3FourierComplexL2 →
          H3FourierComplexL2) :=
  continuous_h3L1L2Convolution_right
    (h3BKMDyadicKernelL1 R hR i k)

/--
Fourier transform after one dyadic endpoint convolution is continuous on
`L²`.
-/
theorem continuous_h3BKMDyadicKernelConvolutionL2_fourier
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    Continuous
      (fun F : H3FourierComplexL2 =>
        (MeasureTheory.Lp.fourierTransformₗᵢ
          H3FourierPoint3 ℂ)
          (h3L1L2Convolution
            (h3BKMDyadicKernelL1 R hR i k)
            F)) := by

  exact
    (MeasureTheory.Lp.fourierTransformₗᵢ
      H3FourierPoint3 ℂ).continuous.comp
        (continuous_h3BKMDyadicKernelConvolutionL2
          hR i k)

end

end Euclidean
end Bridge
end PrimeTensor
