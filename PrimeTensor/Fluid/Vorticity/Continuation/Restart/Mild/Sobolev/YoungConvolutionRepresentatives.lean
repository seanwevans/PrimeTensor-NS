import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.YoungConvolution

/-!
# Scalar representatives of the H³ endpoint Young construction

`YoungConvolution` constructs the endpoint convolution as a Bochner integral
with values in Fourier `L²`.  Before commuting that Banach-valued integral
with the spatial representative, we isolate the two pointwise facts that the
Fubini step will consume.

For fixed translation parameter `η`, the bundled translation

    τ_η g

is represented almost everywhere by

    ξ ↦ g (ξ - η).

Consequently the bundled Young integrand

    f(η) • τ_η g

is represented almost everywhere by the scalar convolution kernel

    ξ ↦ f(η) * g(ξ - η).

No interchange of integrals occurs in this file.  It is only the exact bridge
from the bundled `Lp` operations to their scalar representatives.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3YoungConvolutionRepresentatives
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/--
The bundled Fourier translation has the expected scalar representative almost
everywhere.
-/
theorem h3FourierTranslateL2_ae
    (η : H3FourierPoint3)
    (g : H3FourierComplexL2) :
    (h3FourierTranslateL2 η g : H3FourierPoint3 → ℂ)
      =ᵐ[volume]
    (fun ξ : H3FourierPoint3 => g (ξ - η)) := by
  simpa [h3FourierTranslateL2, sub_eq_add_neg, add_comm] using
    (DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk (-η)) g)

/--
The `L²`-valued endpoint Young integrand has the expected scalar convolution
kernel as its representative almost everywhere.
-/
theorem h3L1L2ConvolutionIntegrand_ae
    (f : H3FourierComplexL1)
    (g : H3FourierComplexL2)
    (η : H3FourierPoint3) :
    (h3L1L2ConvolutionIntegrand f g η : H3FourierPoint3 → ℂ)
      =ᵐ[volume]
    (fun ξ : H3FourierPoint3 => f η * g (ξ - η)) := by
  filter_upwards [
    MeasureTheory.Lp.coeFn_smul
      (f η)
      (h3FourierTranslateL2 η g),
    h3FourierTranslateL2_ae η g
  ] with ξ hSmulξ hTranslateξ
  change
    (f η • h3FourierTranslateL2 η g : H3FourierComplexL2) ξ
      = f η * g (ξ - η)
  rw [hSmulξ]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hTranslateξ]

end

end Euclidean
end Bridge
end PrimeTensor
