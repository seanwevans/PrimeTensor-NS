import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.WeightedConvolutionMajorants
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Real endpoint Young convolution on the H³ Fourier carrier

The weighted majorants are nonnegative real scalar convolutions.  The existing
`YoungConvolution` module proves the endpoint estimate for complex-valued
Fourier states; this file records the identical Banach-space construction for
real-valued states:

    L¹(ℝ³; ℝ) * L²(ℝ³; ℝ) → L²(ℝ³; ℝ),

with

    ‖f * g‖₂ ≤ ‖f‖₁ ‖g‖₂.

This remains an abstract `L²`-valued Bochner convolution.  The next bridge will
identify this state with the named scalar Young majorants by equality of set
integrals on finite-measure measurable sets.  No point evaluation on `L²` is
used here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3YoungConvolutionReal
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Real `L¹` functions on the H³ Fourier carrier. -/
abbrev H3FourierRealL1 : Type :=
  MeasureTheory.Lp
    ℝ
    1
    (volume : Measure H3FourierPoint3)

/-- Translation of a real Fourier `L²` state by `η`. -/
noncomputable def h3FourierTranslateRealL2
    (η : H3FourierPoint3)
    (g : H3FourierRealL2) :
    H3FourierRealL2 :=
  DomAddAct.mk (-η) +ᵥ g

/-- Translation preserves the real Fourier `L²` norm. -/
@[simp]
theorem norm_h3FourierTranslateRealL2
    (η : H3FourierPoint3)
    (g : H3FourierRealL2) :
    ‖h3FourierTranslateRealL2 η g‖ = ‖g‖ := by
  unfold h3FourierTranslateRealL2
  exact DomAddAct.norm_vadd_Lp _ _

/-- The real `L²` translation orbit is continuous. -/
theorem continuous_h3FourierTranslateRealL2
    (g : H3FourierRealL2) :
    Continuous
      (fun η : H3FourierPoint3 =>
        h3FourierTranslateRealL2 η g) := by
  unfold h3FourierTranslateRealL2
  letI : Fact ((2 : ENNReal) ≠ ∞) := ⟨by norm_num⟩
  letI : ContinuousVAdd H3FourierPoint3ᵈᵃᵃ H3FourierRealL2 :=
    MeasureTheory.Lp.instContinuousVAddDomAddAct
      (X := H3FourierPoint3)
      (M := H3FourierPoint3)
      (E := ℝ)
      (μ := (volume : Measure H3FourierPoint3))
      (p := (2 : ENNReal))
  exact
    continuous_vadd.comp
      ((DomAddAct.continuous_mk.comp continuous_neg).prodMk
        continuous_const)

/-- `L²`-valued Bochner integrand for the real endpoint convolution. -/
noncomputable def h3RealL1L2ConvolutionIntegrand
    (f : H3FourierRealL1)
    (g : H3FourierRealL2)
    (η : H3FourierPoint3) :
    H3FourierRealL2 :=
  f η • h3FourierTranslateRealL2 η g

/-- Exact norm of the real endpoint-convolution integrand. -/
theorem norm_h3RealL1L2ConvolutionIntegrand
    (f : H3FourierRealL1)
    (g : H3FourierRealL2)
    (η : H3FourierPoint3) :
    ‖h3RealL1L2ConvolutionIntegrand f g η‖
      = ‖f η‖ * ‖g‖ := by
  unfold h3RealL1L2ConvolutionIntegrand
  rw [norm_smul, norm_h3FourierTranslateRealL2]

/-- The real endpoint-convolution integrand is a.e. strongly measurable. -/
theorem h3RealL1L2ConvolutionIntegrand_aestronglyMeasurable
    (f : H3FourierRealL1)
    (g : H3FourierRealL2) :
    AEStronglyMeasurable
      (h3RealL1L2ConvolutionIntegrand f g)
      (volume : Measure H3FourierPoint3) := by
  unfold h3RealL1L2ConvolutionIntegrand
  exact
    (MeasureTheory.Lp.aestronglyMeasurable f).smul
      (continuous_h3FourierTranslateRealL2 g).aestronglyMeasurable

/-- The real `L²`-valued endpoint-convolution integrand is Bochner integrable. -/
theorem h3RealL1L2ConvolutionIntegrand_integrable
    (f : H3FourierRealL1)
    (g : H3FourierRealL2) :
    Integrable
      (h3RealL1L2ConvolutionIntegrand f g)
      (volume : Measure H3FourierPoint3) := by
  have hfInt :
      Integrable
        (fun η : H3FourierPoint3 =>
          ‖f η‖ * ‖g‖)
        (volume : Measure H3FourierPoint3) :=
    (L1.integrable_coeFn f).norm.mul_const ‖g‖

  refine
    Integrable.mono'
      hfInt
      (h3RealL1L2ConvolutionIntegrand_aestronglyMeasurable f g)
      ?_

  filter_upwards with η
  rw [norm_h3RealL1L2ConvolutionIntegrand]

/-- Real endpoint `L¹ * L² → L²` convolution. -/
noncomputable def h3RealL1L2Convolution
    (f : H3FourierRealL1)
    (g : H3FourierRealL2) :
    H3FourierRealL2 :=
  ∫ η : H3FourierPoint3,
    h3RealL1L2ConvolutionIntegrand f g η

/-- Endpoint Young inequality for real Fourier states. -/
theorem norm_h3RealL1L2Convolution_le
    (f : H3FourierRealL1)
    (g : H3FourierRealL2) :
    ‖h3RealL1L2Convolution f g‖
      ≤ ‖f‖ * ‖g‖ := by
  unfold h3RealL1L2Convolution

  calc
    ‖∫ η : H3FourierPoint3,
        h3RealL1L2ConvolutionIntegrand f g η‖
        ≤
      ∫ η : H3FourierPoint3,
        ‖h3RealL1L2ConvolutionIntegrand f g η‖ :=
          norm_integral_le_integral_norm _
    _ =
      ∫ η : H3FourierPoint3,
        ‖f η‖ * ‖g‖ := by
          apply integral_congr_ae
          filter_upwards with η
          exact norm_h3RealL1L2ConvolutionIntegrand f g η
    _ =
      (∫ η : H3FourierPoint3, ‖f η‖) * ‖g‖ := by
        rw [integral_mul_const]
    _ =
      ‖f‖ * ‖g‖ := by
        rw [L1.norm_eq_integral_norm]

/-- The bundled real translation has the expected scalar representative a.e. -/
theorem h3FourierTranslateRealL2_ae
    (η : H3FourierPoint3)
    (g : H3FourierRealL2) :
    (h3FourierTranslateRealL2 η g : H3FourierPoint3 → ℝ)
      =ᵐ[volume]
    (fun ξ : H3FourierPoint3 => g (ξ - η)) := by
  simpa [h3FourierTranslateRealL2, sub_eq_add_neg, add_comm] using
    (DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk (-η)) g)

/-- The real endpoint Young integrand has the expected scalar representative a.e. -/
theorem h3RealL1L2ConvolutionIntegrand_ae
    (f : H3FourierRealL1)
    (g : H3FourierRealL2)
    (η : H3FourierPoint3) :
    (h3RealL1L2ConvolutionIntegrand f g η : H3FourierPoint3 → ℝ)
      =ᵐ[volume]
    (fun ξ : H3FourierPoint3 => f η * g (ξ - η)) := by
  filter_upwards [
    MeasureTheory.Lp.coeFn_smul
      (f η)
      (h3FourierTranslateRealL2 η g),
    h3FourierTranslateRealL2_ae η g
  ] with ξ hSmulξ hTranslateξ
  change
    (f η • h3FourierTranslateRealL2 η g : H3FourierRealL2) ξ
      = f η * g (ξ - η)
  rw [hSmulξ]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hTranslateξ]

end

end Euclidean
end Bridge
end PrimeTensor
