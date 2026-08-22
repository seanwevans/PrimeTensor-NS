import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.YoungConvolutionRepresentatives
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Dual form of the H³ endpoint Young convolution

For the endpoint `L¹ * L² → L²` construction, the scalar two-variable
kernel need not be globally integrable: the second input is only in `L²`.
Consequently a direct global Fubini argument on

    (η, ξ) ↦ f(η) * g(ξ - η)

would assert more than the hypotheses provide.

The correct bridge is dual.  Every continuous linear functional on Fourier
`L²` commutes with the Bochner integral defining `h3L1L2Convolution`.
Thus, for `Λ : L² →L[ℂ] ℂ`,

    Λ(f * g)
      = ∫ η, f(η) * Λ(τ_η g) dη.

The scalar integrand on the right is integrable because it is the continuous
linear image of the already-proved `L²`-valued Bochner integrand.  This is the
safe Fubini/duality interface used by the next weighted Sobolev step.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3YoungConvolutionDuality
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/--
Applying a continuous complex-linear functional to the endpoint Young
integrand gives the expected scalar integrand.
-/
theorem h3L1L2ConvolutionIntegrand_apply_clm
    (f : H3FourierComplexL1)
    (g : H3FourierComplexL2)
    (Λ : H3FourierComplexL2 →L[ℂ] ℂ)
    (η : H3FourierPoint3) :
    Λ (h3L1L2ConvolutionIntegrand f g η)
      =
    f η * Λ (h3FourierTranslateL2 η g) := by
  simp [h3L1L2ConvolutionIntegrand]

/--
The scalar dual integrand is Bochner integrable in the translation variable.
-/
theorem h3L1L2ConvolutionDualIntegrable
    (f : H3FourierComplexL1)
    (g : H3FourierComplexL2)
    (Λ : H3FourierComplexL2 →L[ℂ] ℂ) :
    Integrable
      (fun η : H3FourierPoint3 =>
        f η * Λ (h3FourierTranslateL2 η g))
      (volume : Measure H3FourierPoint3) := by
  have hInt :
      Integrable
        (fun η : H3FourierPoint3 =>
          Λ (h3L1L2ConvolutionIntegrand f g η))
        (volume : Measure H3FourierPoint3) :=
    Λ.integrable_comp
      (h3L1L2ConvolutionIntegrand_integrable f g)

  exact hInt.congr <|
    Filter.Eventually.of_forall fun η =>
      h3L1L2ConvolutionIntegrand_apply_clm f g Λ η

/--
Dual representation of the endpoint Young convolution.  This is the safe
replacement for a globally-integrable two-variable Fubini statement at the
`L¹ * L²` endpoint.
-/
theorem h3L1L2Convolution_apply_clm
    (f : H3FourierComplexL1)
    (g : H3FourierComplexL2)
    (Λ : H3FourierComplexL2 →L[ℂ] ℂ) :
    Λ (h3L1L2Convolution f g)
      =
    ∫ η : H3FourierPoint3,
      f η * Λ (h3FourierTranslateL2 η g) := by
  unfold h3L1L2Convolution

  rw [← Λ.integral_comp_comm
    (h3L1L2ConvolutionIntegrand_integrable f g)]

  apply integral_congr_ae
  filter_upwards with η
  exact h3L1L2ConvolutionIntegrand_apply_clm f g Λ η

end

end Euclidean
end Bridge
end PrimeTensor
