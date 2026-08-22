import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.SpectralWeightSplit
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# The endpoint Young estimate `L¹ * L² → L²` on the H³ Fourier carrier

Mathlib's pointwise convolution file does not yet package the general `Lᵖ`
Young inequalities.  For the H³ mild solver we only need the endpoint

    ‖f * g‖₂ ≤ ‖f‖₁ ‖g‖₂.

The clean formal representation is a Bochner integral with values in the
Banach space `L²` itself:

    f * g = ∫ η, f(η) • τ_η g dη,

where `τ_η g (ξ) = g (ξ - η)`.

Translation preserves volume, hence it is an isometry on `L²`.  The
translation orbit is continuous, so the `L²`-valued integrand is strongly
measurable.  Its norm is exactly

    ‖f(η) • τ_η g‖₂ = ‖f(η)‖ ‖g‖₂,

which is integrable because `f ∈ L¹`.  The Banach-space inequality
`norm_integral_le_integral_norm` then gives Young directly.

This module deliberately stops at the abstract `L²`-valued convolution.
The next Sobolev module combines it with the exact H³ weight split.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3YoungConvolution
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Complex `L¹` functions on the H³ Fourier carrier. -/
abbrev H3FourierComplexL1 : Type :=
  MeasureTheory.Lp
    ℂ
    1
    (volume : Measure H3FourierPoint3)

/-! ## Translation on Fourier `L²` -/

/--
Translation of an `L²` Fourier state by `η`.

The domain action `DomAddAct.mk (-η)` represents precomposition by
`ξ ↦ ξ - η`.
-/
noncomputable def h3FourierTranslateL2
    (η : H3FourierPoint3)
    (g : H3FourierComplexL2) :
    H3FourierComplexL2 :=
  DomAddAct.mk (-η) +ᵥ g

/-- Translation preserves the `L²` norm exactly. -/
@[simp]
theorem norm_h3FourierTranslateL2
    (η : H3FourierPoint3)
    (g : H3FourierComplexL2) :
    ‖h3FourierTranslateL2 η g‖ = ‖g‖ := by
  unfold h3FourierTranslateL2
  exact DomAddAct.norm_vadd_Lp _ _

/--
The translation orbit of a fixed `L²` state is continuous in the
translation parameter.
-/
theorem continuous_h3FourierTranslateL2
    (g : H3FourierComplexL2) :
    Continuous
      (fun η : H3FourierPoint3 =>
        h3FourierTranslateL2 η g) := by
  unfold h3FourierTranslateL2
  letI : Fact ((2 : ENNReal) ≠ ∞) := ⟨by norm_num⟩
  letI : ContinuousVAdd H3FourierPoint3ᵈᵃᵃ H3FourierComplexL2 :=
    MeasureTheory.Lp.instContinuousVAddDomAddAct
      (X := H3FourierPoint3)
      (M := H3FourierPoint3)
      (E := ℂ)
      (μ := (volume : Measure H3FourierPoint3))
      (p := (2 : ENNReal))
  exact
    continuous_vadd.comp
      ((DomAddAct.continuous_mk.comp continuous_neg).prodMk
        continuous_const)

/-! ## The `L²`-valued convolution integrand -/

/--
Bochner integrand for the endpoint convolution theorem.
-/
noncomputable def h3L1L2ConvolutionIntegrand
    (f : H3FourierComplexL1)
    (g : H3FourierComplexL2)
    (η : H3FourierPoint3) :
    H3FourierComplexL2 :=
  f η • h3FourierTranslateL2 η g

/-- Exact norm of the `L²`-valued convolution integrand. -/
theorem norm_h3L1L2ConvolutionIntegrand
    (f : H3FourierComplexL1)
    (g : H3FourierComplexL2)
    (η : H3FourierPoint3) :
    ‖h3L1L2ConvolutionIntegrand f g η‖
      =
    ‖f η‖ * ‖g‖ := by
  unfold h3L1L2ConvolutionIntegrand
  rw [norm_smul, norm_h3FourierTranslateL2]

/--
The `L²`-valued convolution integrand is a.e. strongly measurable.
-/
theorem h3L1L2ConvolutionIntegrand_aestronglyMeasurable
    (f : H3FourierComplexL1)
    (g : H3FourierComplexL2) :
    AEStronglyMeasurable
      (h3L1L2ConvolutionIntegrand f g)
      (volume : Measure H3FourierPoint3) := by
  unfold h3L1L2ConvolutionIntegrand
  exact
    (MeasureTheory.Lp.aestronglyMeasurable f).smul
      (continuous_h3FourierTranslateL2 g).aestronglyMeasurable

/--
The `L²`-valued convolution integrand is Bochner integrable.
-/
theorem h3L1L2ConvolutionIntegrand_integrable
    (f : H3FourierComplexL1)
    (g : H3FourierComplexL2) :
    Integrable
      (h3L1L2ConvolutionIntegrand f g)
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
      (h3L1L2ConvolutionIntegrand_aestronglyMeasurable f g)
      ?_

  filter_upwards with η

  rw [norm_h3L1L2ConvolutionIntegrand]

/-! ## The endpoint convolution and Young bound -/

/--
The endpoint `L¹ * L² → L²` convolution, represented as an `L²`-valued
Bochner integral.
-/
noncomputable def h3L1L2Convolution
    (f : H3FourierComplexL1)
    (g : H3FourierComplexL2) :
    H3FourierComplexL2 :=
  ∫ η : H3FourierPoint3,
    h3L1L2ConvolutionIntegrand f g η

/--
Endpoint Young inequality on the H³ Fourier carrier:

`‖f * g‖₂ ≤ ‖f‖₁ ‖g‖₂`.
-/
theorem norm_h3L1L2Convolution_le
    (f : H3FourierComplexL1)
    (g : H3FourierComplexL2) :
    ‖h3L1L2Convolution f g‖
      ≤
    ‖f‖ * ‖g‖ := by
  unfold h3L1L2Convolution

  calc
    ‖∫ η : H3FourierPoint3,
        h3L1L2ConvolutionIntegrand f g η‖
        ≤
      ∫ η : H3FourierPoint3,
        ‖h3L1L2ConvolutionIntegrand f g η‖ :=
          norm_integral_le_integral_norm _
    _ =
      ∫ η : H3FourierPoint3,
        ‖f η‖ * ‖g‖ := by
          apply integral_congr_ae
          filter_upwards with η
          exact norm_h3L1L2ConvolutionIntegrand f g η
    _ =
      (∫ η : H3FourierPoint3, ‖f η‖) * ‖g‖ := by
        rw [integral_mul_const]
    _ =
      ‖f‖ * ‖g‖ := by
        rw [L1.norm_eq_integral_norm]

end

end Euclidean
end Bridge
end PrimeTensor
