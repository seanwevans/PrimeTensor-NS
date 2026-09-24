import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Dyadic.Schwartz.Anchor
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Weighted.Convolution.Integrand
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# BKM endpoint: identify endpoint Young convolution with the Schwartz anchor

`DyadicSchwartzAnchor` proves the exact smooth identity

    𝓕(Kᵢₖ,R * P) = Mᵢₖ,R · 𝓕P

for the Schwartz convolution.  `DyadicConvolutionClosure` already shows that
the corresponding identity for the project's endpoint Bochner convolution
extends from Schwartz inputs to arbitrary `L²`.

The remaining seam is therefore precise:

    h3L1L2Convolution (Kᵢₖ,R : L¹) (P : L²)

must equal the `L²` package of the ordinary Schwartz convolution.

We prove that equality without evaluating an `L²` class at a fixed point.
Following the finite-set uniqueness pattern used by the weighted Young
majorants:

* pair the bundled endpoint convolution with the `L²` indicator of an
  arbitrary measurable finite-measure set;
* commute that continuous pairing through the Bochner integral;
* replace the bundled integrand by its scalar representative;
* use Fubini, justified here globally because both the dyadic kernel and `P`
  are Schwartz;
* identify the resulting scalar convolution with
  `h3BKMDyadicSchwartzConvolution`;
* conclude a.e. equality by sigma-finite set-integral uniqueness.

This closes the smooth Bochner/Schwartz bridge and then discharges the
Schwartz hypothesis of `DyadicConvolutionClosure`, yielding the full dyadic
Fourier multiplier theorem for arbitrary complex `L²` input.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set ContinuousLinearMap
open FourierTransform
open scoped ENNReal NNReal InnerProductSpace Convolution

noncomputable section

noncomputable local instance axisFintypeBKMEndpointDyadicYoungSchwartzBridge
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Fubini for the smooth dyadic scalar kernel -/

/--
The scalar dyadic Schwartz convolution kernel is product-integrable, even
before restricting the output variable to a finite-measure set.
-/
theorem h3BKMDyadicSchwartzConvolution_fubini_integrable
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3)
    (P : SchwartzMap H3FourierPoint3 ℂ)
    (s : Set H3FourierPoint3)
    (_hs : MeasurableSet s)
    (_hμs : (volume : Measure H3FourierPoint3) s < ∞) :
    Integrable
      (Function.uncurry
        (fun ξ η : H3FourierPoint3 =>
          h3BKMDyadicKernel R hR i k η
            *
          P (ξ - η)))
      (((volume : Measure H3FourierPoint3).restrict s).prod
        (volume : Measure H3FourierPoint3)) := by

  have hFull :
      Integrable
        (Function.uncurry
          (fun ξ η : H3FourierPoint3 =>
            h3BKMDyadicKernel R hR i k η
              *
            P (ξ - η)))
        ((volume : Measure H3FourierPoint3).prod
          (volume : Measure H3FourierPoint3)) := by

    change
      Integrable
        (fun p : H3FourierPoint3 × H3FourierPoint3 =>
          h3BKMDyadicKernel R hR i k p.2
            *
          P (p.1 - p.2))
        ((volume : Measure H3FourierPoint3).prod
          (volume : Measure H3FourierPoint3))

    simpa only [ContinuousLinearMap.mul_apply'] using
      (h3BKMDyadicKernel_integrable hR i k).convolution_integrand
        (ContinuousLinearMap.mul ℂ ℂ)
        P.integrable

  exact
    hFull.mono_measure
      (Measure.prod_mono Measure.restrict_le_self le_rfl)

/--
Fubini orientation of the scalar Schwartz convolution on a finite-measure
output set.
-/
theorem h3BKMDyadicSchwartzConvolution_setIntegral_eq_iterated
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3)
    (P : SchwartzMap H3FourierPoint3 ℂ)
    (s : Set H3FourierPoint3)
    (hs : MeasurableSet s)
    (hμs : (volume : Measure H3FourierPoint3) s < ∞) :
    (∫ ξ in s,
        h3BKMDyadicSchwartzConvolution
          R hR i k P ξ)
      =
    ∫ η : H3FourierPoint3,
      ∫ ξ in s,
        h3BKMDyadicKernel R hR i k η
          *
        P (ξ - η) := by

  have hSwap :=
    integral_integral_swap
      (h3BKMDyadicSchwartzConvolution_fubini_integrable
        hR i k P s hs hμs)

  calc
    (∫ ξ in s,
        h3BKMDyadicSchwartzConvolution
          R hR i k P ξ)
        =
      ∫ ξ in s,
        ∫ η : H3FourierPoint3,
          h3BKMDyadicKernel R hR i k η
            *
          P (ξ - η) := by
            apply integral_congr_ae
            filter_upwards with ξ
            exact
              h3BKMDyadicSchwartzConvolution_apply
                hR i k P ξ
    _ =
      ∫ η : H3FourierPoint3,
        ∫ ξ in s,
          h3BKMDyadicKernel R hR i k η
            *
          P (ξ - η) := hSwap

/-! ## Finite-set integrals of the bundled endpoint Young state -/

/--
On every measurable finite-measure output set, the bundled endpoint Young
state has the same integral as the iterated scalar dyadic kernel.
-/
theorem h3BKMDyadicYoungSchwartz_setIntegral_eq_iterated
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3)
    (P : SchwartzMap H3FourierPoint3 ℂ)
    (s : Set H3FourierPoint3)
    (hs : MeasurableSet s)
    (hμs : (volume : Measure H3FourierPoint3) s < ∞) :
    (∫ ξ in s,
        (h3L1L2Convolution
          (h3BKMDyadicKernelL1 R hR i k)
          (P.toLp
            2
            (volume : Measure H3FourierPoint3)) :
          H3FourierPoint3 → ℂ) ξ)
      =
    ∫ η : H3FourierPoint3,
      ∫ ξ in s,
        h3BKMDyadicKernel R hR i k η
          *
        P (ξ - η) := by

  let f : H3FourierComplexL1 :=
    h3BKMDyadicKernelL1 R hR i k

  let g : H3FourierComplexL2 :=
    P.toLp 2 (volume : Measure H3FourierPoint3)

  let c : H3FourierComplexL2 :=
    indicatorConstLp 2 hs hμs.ne (1 : ℂ)

  have hInt :
      Integrable
        (h3L1L2ConvolutionIntegrand f g)
        (volume : Measure H3FourierPoint3) :=
    h3L1L2ConvolutionIntegrand_integrable f g

  calc
    (∫ ξ in s,
        (h3L1L2Convolution
          (h3BKMDyadicKernelL1 R hR i k)
          (P.toLp
            2
            (volume : Measure H3FourierPoint3)) :
          H3FourierPoint3 → ℂ) ξ)
        =
      inner ℂ c (h3L1L2Convolution f g) := by
        symm
        simpa [c, f, g] using
          (L2.inner_indicatorConstLp_one
            (𝕜 := ℂ)
            hs
            hμs.ne
            (h3L1L2Convolution f g))

    _ =
      inner ℂ c
        (∫ η : H3FourierPoint3,
          h3L1L2ConvolutionIntegrand f g η) := by
        rfl

    _ =
      ∫ η : H3FourierPoint3,
        inner ℂ c
          (h3L1L2ConvolutionIntegrand f g η) := by
        exact (integral_inner hInt c).symm

    _ =
      ∫ η : H3FourierPoint3,
        ∫ ξ in s,
          (h3L1L2ConvolutionIntegrand f g η :
            H3FourierPoint3 → ℂ) ξ := by
        apply integral_congr_ae
        filter_upwards with η
        simpa [c] using
          (L2.inner_indicatorConstLp_one
            (𝕜 := ℂ)
            hs
            hμs.ne
            (h3L1L2ConvolutionIntegrand f g η))

    _ =
      ∫ η : H3FourierPoint3,
        ∫ ξ in s,
          h3BKMDyadicKernel R hR i k η
            *
          P (ξ - η) := by
        apply integral_congr_ae

        filter_upwards [
          h3BKMDyadicKernelL1_ae hR i k
        ] with η hKernelη

        have hKernelη' :
            f η = h3BKMDyadicKernel R hR i k η := by
          simpa [f] using hKernelη

        have hShift :
            (fun ξ : H3FourierPoint3 =>
              g (ξ - η))
              =ᵐ[(volume : Measure H3FourierPoint3)]
            (fun ξ : H3FourierPoint3 =>
              P (ξ - η)) := by

          have h :=
            (h3MeasurePreserving_sub_right η).quasiMeasurePreserving.ae_eq_comp
              (SchwartzMap.coeFn_toLp
                P
                2
                (volume : Measure H3FourierPoint3))

          simpa [g, Function.comp_def] using h

        have hIntegrand :=
          h3L1L2ConvolutionIntegrand_ae f g η

        apply integral_congr_ae

        filter_upwards [
          hIntegrand.filter_mono
            (ae_restrict_le
              (μ := (volume : Measure H3FourierPoint3))
              (s := s)),
          hShift.filter_mono
            (ae_restrict_le
              (μ := (volume : Measure H3FourierPoint3))
              (s := s))
        ] with ξ hIntegrandξ hShiftξ

        rw [hIntegrandξ, hShiftξ, hKernelη']

/-! ## A.e. and bundled equality of the two smooth convolutions -/

/--
For Schwartz input, the endpoint Bochner convolution represents exactly the
ordinary dyadic Schwartz convolution almost everywhere.
-/
theorem h3BKMDyadicYoungSchwartz_ae
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3)
    (P : SchwartzMap H3FourierPoint3 ℂ) :
    (h3L1L2Convolution
        (h3BKMDyadicKernelL1 R hR i k)
        (P.toLp
          2
          (volume : Measure H3FourierPoint3)) :
        H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (h3BKMDyadicSchwartzConvolution
      R hR i k P :
      H3FourierPoint3 → ℂ) := by

  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite

  · intro s hs hμs
    exact
      integrableOn_Lp_of_measure_ne_top
        (h3L1L2Convolution
          (h3BKMDyadicKernelL1 R hR i k)
          (P.toLp
            2
            (volume : Measure H3FourierPoint3)))
        fact_one_le_two_ennreal.elim
        hμs.ne

  · intro s hs hμs
    exact
      (h3BKMDyadicSchwartzConvolution
        R hR i k P).integrable.integrableOn

  · intro s hs hμs
    rw [
      h3BKMDyadicYoungSchwartz_setIntegral_eq_iterated
        hR i k P s hs hμs,
      ← h3BKMDyadicSchwartzConvolution_setIntegral_eq_iterated
        hR i k P s hs hμs
    ]

/--
For Schwartz input, the endpoint Bochner convolution is literally the `L²`
package of the Schwartz convolution.
-/
theorem h3BKMDyadicYoungSchwartz_eq
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3)
    (P : SchwartzMap H3FourierPoint3 ℂ) :
    h3L1L2Convolution
        (h3BKMDyadicKernelL1 R hR i k)
        (P.toLp
          2
          (volume : Measure H3FourierPoint3))
      =
    (h3BKMDyadicSchwartzConvolution
        R hR i k P).toLp
      2
      (volume : Measure H3FourierPoint3) := by

  apply MeasureTheory.Lp.ext

  exact
    (h3BKMDyadicYoungSchwartz_ae
      hR i k P).trans
      (SchwartzMap.coeFn_toLp
        (h3BKMDyadicSchwartzConvolution
          R hR i k P)
        2
        (volume : Measure H3FourierPoint3)).symm

/-! ## Discharge the Schwartz anchor and close the arbitrary-L² theorem -/

/--
The exact endpoint Young convolution Fourier identity on one Schwartz input.
-/
theorem h3BKMDyadicKernelConvolution_schwartz_fourier_eq_localized
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3)
    (P : SchwartzMap H3FourierPoint3 ℂ) :
    (MeasureTheory.Lp.fourierTransformₗᵢ
        H3FourierPoint3 ℂ)
      (h3L1L2Convolution
        (h3BKMDyadicKernelL1 R hR i k)
        (P.toLp
          2
          (volume : Measure H3FourierPoint3)))
      =
    h3BKMLocalizedCoordinateMultiplierApplyL2
      R hR i k
      ((MeasureTheory.Lp.fourierTransformₗᵢ
          H3FourierPoint3 ℂ)
        (P.toLp
          2
          (volume : Measure H3FourierPoint3))) := by

  rw [h3BKMDyadicYoungSchwartz_eq hR i k P]

  exact
    h3BKMDyadicSchwartzConvolutionL2_fourier_eq_localized
      hR i k P

/--
Full endpoint dyadic convolution theorem: for arbitrary complex `L²` input,
Fourier transform of convolution by the dyadic inverse-Fourier kernel is
exactly multiplication by the localized BKM coordinate symbol.
-/
theorem h3BKMDyadicKernelConvolution_fourier_eq_localized_all
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3)
    (F : H3FourierComplexL2) :
    (MeasureTheory.Lp.fourierTransformₗᵢ
        H3FourierPoint3 ℂ)
      (h3L1L2Convolution
        (h3BKMDyadicKernelL1 R hR i k)
        F)
      =
    h3BKMLocalizedCoordinateMultiplierApplyL2
      R hR i k
      ((MeasureTheory.Lp.fourierTransformₗᵢ
          H3FourierPoint3 ℂ) F) := by

  exact
    h3BKMDyadicKernelConvolution_fourier_eq_localized_of_schwartz
      hR
      i
      k
      (fun P =>
        h3BKMDyadicKernelConvolution_schwartz_fourier_eq_localized
          hR i k P)
      F

end

end Euclidean
end Bridge
end PrimeTensor
