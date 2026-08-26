import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Young.Convolution.Duality
import Mathlib.MeasureTheory.Function.L2Space

/-!
# L² pairing form of the H³ endpoint Young convolution

`YoungConvolutionDuality` proves the endpoint Bochner convolution identity for
an arbitrary continuous linear functional on Fourier `L²`.  For the Sobolev
algebra argument the canonical functionals are the Hilbert-space pairings

    G ↦ ⟪H, G⟫.

This file specializes the duality bridge to those functionals and then opens
the translated pairing into its scalar integral representative.  Thus

    ⟪H, f * g⟫
      = ∫ η, f(η) * ∫ ξ, ⟪H(ξ), g(ξ - η)⟫ dξ dη.

No interchange of the two scalar integrals is asserted here.  The next module
can perform only the change-of-variables/Fubini step justified by the weighted
kernel estimates.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped ENNReal NNReal InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3YoungConvolutionPairing
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The continuous linear functional on Fourier `L²` represented by `H`. -/
noncomputable def h3FourierL2PairingCLM
    (H : H3FourierComplexL2) :
    H3FourierComplexL2 →L[ℂ] ℂ :=
  innerSL ℂ H

/-- The pairing functional has exactly the norm of its representing state. -/
@[simp]
theorem norm_h3FourierL2PairingCLM
    (H : H3FourierComplexL2) :
    ‖h3FourierL2PairingCLM H‖ = ‖H‖ := by
  simp [h3FourierL2PairingCLM]

/--
The endpoint Young duality identity specialized to the Fourier `L²` inner
product.
-/
theorem h3L1L2Convolution_inner
    (f : H3FourierComplexL1)
    (g H : H3FourierComplexL2) :
    inner ℂ H (h3L1L2Convolution f g)
      =
    ∫ η : H3FourierPoint3,
      f η * inner ℂ H (h3FourierTranslateL2 η g) := by
  simpa only [innerSL_apply_apply] using
    h3L1L2Convolution_apply_clm f g (innerSL ℂ H)

/-- The scalar integrand in the specialized pairing identity is integrable. -/
theorem h3L1L2ConvolutionInnerIntegrable
    (f : H3FourierComplexL1)
    (g H : H3FourierComplexL2) :
    Integrable
      (fun η : H3FourierPoint3 =>
        f η * inner ℂ H (h3FourierTranslateL2 η g))
      (volume : Measure H3FourierPoint3) := by
  simpa only [innerSL_apply_apply] using
    h3L1L2ConvolutionDualIntegrable f g (innerSL ℂ H)

/--
The pairing with a translated `L²` state is the integral of the expected
pointwise inner-product kernel.
-/
theorem h3FourierTranslateL2_inner
    (H g : H3FourierComplexL2)
    (η : H3FourierPoint3) :
    inner ℂ H (h3FourierTranslateL2 η g)
      =
    ∫ ξ : H3FourierPoint3,
      inner ℂ (H ξ) (g (ξ - η)) := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [h3FourierTranslateL2_ae η g] with ξ hξ
  rw [hξ]

/--
Fully opened iterated-integral form of the endpoint Young pairing.  This is
still an iterated integral, not a global product-space Fubini assertion.
-/
theorem h3L1L2Convolution_inner_iterated
    (f : H3FourierComplexL1)
    (g H : H3FourierComplexL2) :
    inner ℂ H (h3L1L2Convolution f g)
      =
    ∫ η : H3FourierPoint3,
      f η *
        (∫ ξ : H3FourierPoint3,
          inner ℂ (H ξ) (g (ξ - η))) := by
  rw [h3L1L2Convolution_inner]
  apply integral_congr_ae
  filter_upwards with η
  rw [h3FourierTranslateL2_inner]

/-- Endpoint Young estimate expressed directly in `L²` dual pairing form. -/
theorem norm_h3L1L2Convolution_inner_le
    (f : H3FourierComplexL1)
    (g H : H3FourierComplexL2) :
    ‖inner ℂ H (h3L1L2Convolution f g)‖
      ≤
    ‖H‖ * ‖f‖ * ‖g‖ := by
  calc
    ‖inner ℂ H (h3L1L2Convolution f g)‖
        ≤ ‖H‖ * ‖h3L1L2Convolution f g‖ :=
      norm_inner_le_norm H (h3L1L2Convolution f g)
    _ ≤ ‖H‖ * (‖f‖ * ‖g‖) :=
      mul_le_mul_of_nonneg_left
        (norm_h3L1L2Convolution_le f g)
        (norm_nonneg H)
    _ = ‖H‖ * ‖f‖ * ‖g‖ := by
      ring

end

end Euclidean
end Bridge
end PrimeTensor
