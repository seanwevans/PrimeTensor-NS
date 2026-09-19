import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.DyadicVorticityConvolutionReconstruction
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Young.Convolution.Representatives
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Weighted.Convolution.Integrand
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# BKM endpoint: pointwise representatives of dyadic vorticity convolutions

The previous checkpoint identifies the bundled endpoint-Young states with the
localized inverse-Fourier curl states.  To use the already-proved physical
`L∞` convolution bounds, we still need to know what those bundled states
represent pointwise.

This file proves a general endpoint fact tailored to the present application.

Suppose

* `f : L¹`,
* `g : L²`,
* `κ` is an integrable representative of `f`,
* `φ` is a representative of `g`,
* `φ` is globally bounded by `M`.

Then the Bochner-valued Young convolution

    h3L1L2Convolution f g

is represented almost everywhere by the scalar convolution

    ξ ↦ ∫ η, κ η * φ (ξ - η).

The proof never evaluates an `L²` class at a fixed point.  As in the earlier
Schwartz bridge, it compares finite-set integrals and uses sigma-finite
uniqueness.  The product-integrability step now comes from the `L¹` kernel
together with the global bound on `φ`.

We then specialize this theorem to the three physical vorticity components
under a `VorticityEnvelope`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set ContinuousLinearMap
open scoped ENNReal NNReal InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeBKMEndpointDyadicVorticityConvolutionRepresentative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Generic bounded representative theorem -/

/--
On a finite-measure output set, an integrable kernel times a globally bounded
translated scalar field is product-integrable.
-/
theorem h3BoundedL1Convolution_fubini_integrable
    (κ φ : H3FourierPoint3 → ℂ)
    (M : ℝ)
    (hκ : Integrable κ (volume : Measure H3FourierPoint3))
    (hφMeas :
      AEStronglyMeasurable
        φ
        (volume : Measure H3FourierPoint3))
    (hφ : ∀ ξ : H3FourierPoint3, ‖φ ξ‖ ≤ M)
    (hM : 0 ≤ M)
    (s : Set H3FourierPoint3)
    (_hs : MeasurableSet s)
    (hμs : (volume : Measure H3FourierPoint3) s < ∞) :
    Integrable
      (Function.uncurry
        (fun ξ η : H3FourierPoint3 =>
          κ η * φ (ξ - η)))
      (((volume : Measure H3FourierPoint3).restrict s).prod
        (volume : Measure H3FourierPoint3)) := by

  have hJointFull :
      AEStronglyMeasurable
        (fun p : H3FourierPoint3 × H3FourierPoint3 =>
          κ p.2 * φ (p.1 - p.2))
        ((volume : Measure H3FourierPoint3).prod
          (volume : Measure H3FourierPoint3)) := by
    simpa only [ContinuousLinearMap.mul_apply'] using
      hκ.aestronglyMeasurable.convolution_integrand
        (ContinuousLinearMap.mul ℂ ℂ)
        hφMeas

  have hJoint :
      AEStronglyMeasurable
        (fun p : H3FourierPoint3 × H3FourierPoint3 =>
          κ p.2 * φ (p.1 - p.2))
        (((volume : Measure H3FourierPoint3).restrict s).prod
          (volume : Measure H3FourierPoint3)) :=
    hJointFull.mono_measure
      (Measure.prod_mono Measure.restrict_le_self le_rfl)

  letI : Fact ((volume : Measure H3FourierPoint3) s < ∞) :=
    ⟨hμs⟩

  have hMajorEta :
      Integrable
        (fun η : H3FourierPoint3 => M * ‖κ η‖)
        (volume : Measure H3FourierPoint3) :=
    hκ.norm.const_mul M

  have hMajorProd :
      Integrable
        (fun p : H3FourierPoint3 × H3FourierPoint3 =>
          M * ‖κ p.2‖)
        (((volume : Measure H3FourierPoint3).restrict s).prod
          (volume : Measure H3FourierPoint3)) :=
    hMajorEta.comp_snd
      ((volume : Measure H3FourierPoint3).restrict s)

  refine Integrable.mono' hMajorProd hJoint ?_

  filter_upwards with p

  have hPoint :
      ‖κ p.2‖ * ‖φ (p.1 - p.2)‖
        ≤
      ‖κ p.2‖ * M :=
    mul_le_mul_of_nonneg_left
      (hφ (p.1 - p.2))
      (norm_nonneg _)

  change
    ‖κ p.2 * φ (p.1 - p.2)‖
      ≤
    M * ‖κ p.2‖

  rw [norm_mul]

  simpa only [mul_comm] using hPoint

/--
Finite-set integral of the raw bounded convolution equals the iterated
kernel/output integral.
-/
theorem h3BoundedL1Convolution_setIntegral_eq_iterated
    (κ φ : H3FourierPoint3 → ℂ)
    (M : ℝ)
    (hκ : Integrable κ (volume : Measure H3FourierPoint3))
    (hφMeas :
      AEStronglyMeasurable
        φ
        (volume : Measure H3FourierPoint3))
    (hφ : ∀ ξ : H3FourierPoint3, ‖φ ξ‖ ≤ M)
    (hM : 0 ≤ M)
    (s : Set H3FourierPoint3)
    (hs : MeasurableSet s)
    (hμs : (volume : Measure H3FourierPoint3) s < ∞) :
    (∫ ξ in s,
        ∫ η : H3FourierPoint3,
          κ η * φ (ξ - η))
      =
    ∫ η : H3FourierPoint3,
      ∫ ξ in s,
        κ η * φ (ξ - η) := by

  exact
    integral_integral_swap
      (h3BoundedL1Convolution_fubini_integrable
        κ φ M hκ hφMeas hφ hM s hs hμs)

/--
Finite-set integral of the bundled endpoint Young state equals the same
iterated scalar convolution when both factors are replaced by chosen
representatives.
-/
theorem h3L1L2Convolution_boundedRepresentatives_setIntegral_eq_iterated
    (f : H3FourierComplexL1)
    (g : H3FourierComplexL2)
    (κ φ : H3FourierPoint3 → ℂ)
    (hf :
      (f : H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      κ)
    (hg :
      (g : H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      φ)
    (s : Set H3FourierPoint3)
    (hs : MeasurableSet s)
    (hμs : (volume : Measure H3FourierPoint3) s < ∞) :
    (∫ ξ in s,
        (h3L1L2Convolution f g :
          H3FourierPoint3 → ℂ) ξ)
      =
    ∫ η : H3FourierPoint3,
      ∫ ξ in s,
        κ η * φ (ξ - η) := by

  let c : H3FourierComplexL2 :=
    indicatorConstLp 2 hs hμs.ne (1 : ℂ)

  have hInt :
      Integrable
        (h3L1L2ConvolutionIntegrand f g)
        (volume : Measure H3FourierPoint3) :=
    h3L1L2ConvolutionIntegrand_integrable f g

  calc
    (∫ ξ in s,
        (h3L1L2Convolution f g :
          H3FourierPoint3 → ℂ) ξ)
        =
      inner ℂ c (h3L1L2Convolution f g) := by
        symm
        simpa [c] using
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
          κ η * φ (ξ - η) := by
        apply integral_congr_ae

        filter_upwards [hf] with η hfη

        have hShift :
            (fun ξ : H3FourierPoint3 =>
              g (ξ - η))
              =ᵐ[(volume : Measure H3FourierPoint3)]
            (fun ξ : H3FourierPoint3 =>
              φ (ξ - η)) := by
          have h :=
            (h3MeasurePreserving_sub_right η).quasiMeasurePreserving.ae_eq_comp
              hg
          simpa [Function.comp_def] using h

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

        rw [hIntegrandξ, hShiftξ, hfη]

/--
A bounded chosen representative of the `L²` factor gives the literal scalar
convolution representative of the endpoint Young state.
-/
theorem h3L1L2Convolution_ae_eq_boundedRepresentatives
    (f : H3FourierComplexL1)
    (g : H3FourierComplexL2)
    (κ φ : H3FourierPoint3 → ℂ)
    (M : ℝ)
    (hf :
      (f : H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      κ)
    (hκ : Integrable κ (volume : Measure H3FourierPoint3))
    (hg :
      (g : H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      φ)
    (hφ : ∀ ξ : H3FourierPoint3, ‖φ ξ‖ ≤ M)
    (hM : 0 ≤ M) :
    (h3L1L2Convolution f g :
        H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ∫ η : H3FourierPoint3,
        κ η * φ (ξ - η)) := by

  have hφMeas :
      AEStronglyMeasurable
        φ
        (volume : Measure H3FourierPoint3) :=
    (MeasureTheory.Lp.aestronglyMeasurable g).congr hg

  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite

  · intro s hs hμs
    exact
      integrableOn_Lp_of_measure_ne_top
        (h3L1L2Convolution f g)
        fact_one_le_two_ennreal.elim
        hμs.ne

  · intro s hs hμs
    exact
      (h3BoundedL1Convolution_fubini_integrable
        κ φ M hκ hφMeas hφ hM s hs hμs).integral_prod_left

  · intro s hs hμs
    rw [
      h3L1L2Convolution_boundedRepresentatives_setIntegral_eq_iterated
        f g κ φ hf hg s hs hμs,
      ← h3BoundedL1Convolution_setIntegral_eq_iterated
        κ φ M hκ hφMeas hφ hM s hs hμs
    ]

/-! ## Raw Euclidean dyadic vorticity convolutions -/

noncomputable def h3BKMDyadicVorticityXConvolutionRaw
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t R : ℝ)
    (hR : 0 < R)
    (i k : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  ∫ η : H3FourierPoint3,
    h3BKMDyadicKernel R hR i k η
      *
    h3BKMPhysicalVorticityX
      u t
      ((WithLp.ofLp :
        H3FourierPoint3 → Point3) (ξ - η))

noncomputable def h3BKMDyadicVorticityYConvolutionRaw
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t R : ℝ)
    (hR : 0 < R)
    (i k : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  ∫ η : H3FourierPoint3,
    h3BKMDyadicKernel R hR i k η
      *
    h3BKMPhysicalVorticityY
      u t
      ((WithLp.ofLp :
        H3FourierPoint3 → Point3) (ξ - η))

noncomputable def h3BKMDyadicVorticityZConvolutionRaw
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t R : ℝ)
    (hR : 0 < R)
    (i k : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  ∫ η : H3FourierPoint3,
    h3BKMDyadicKernel R hR i k η
      *
    h3BKMPhysicalVorticityZ
      u t
      ((WithLp.ofLp :
        H3FourierPoint3 → Point3) (ξ - η))

/-! ## Physical-vorticity specializations -/

theorem h3BKMDyadicVorticityXConvolutionL2_ae_eq_raw
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hEnvelope : VorticityEnvelope u g t)
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    (h3BKMDyadicVorticityXConvolutionL2
        hInt hMeas R hR i k :
        H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3BKMDyadicVorticityXConvolutionRaw
      u t R hR i k := by

  have hM : 0 ≤ g t :=
    (norm_nonneg
      (h3BKMPhysicalVorticityX u t (0 : Point3))).trans
      (norm_h3BKMPhysicalVorticityX_le
        hEnvelope (0 : Point3))

  unfold h3BKMDyadicVorticityXConvolutionL2
  unfold h3BKMDyadicVorticityXConvolutionRaw

  exact
    h3L1L2Convolution_ae_eq_boundedRepresentatives
      (h3BKMDyadicKernelL1 R hR i k)
      (h3PhysicalScalarL2EuclideanComplex
        (h3BKMPhysicalVorticityXL2
          u t hInt hMeas))
      (h3BKMDyadicKernel R hR i k)
      (fun ξ : H3FourierPoint3 =>
        h3BKMPhysicalVorticityX
          u t
          ((WithLp.ofLp :
            H3FourierPoint3 → Point3) ξ))
      (g t)
      (h3BKMDyadicKernelL1_ae hR i k)
      (h3BKMDyadicKernel_integrable hR i k)
      (h3BKMPhysicalVorticityXEuclideanComplex_ae
        hInt hMeas)
      (fun ξ =>
        norm_h3BKMPhysicalVorticityX_le
          hEnvelope
          ((WithLp.ofLp :
            H3FourierPoint3 → Point3) ξ))
      hM

theorem h3BKMDyadicVorticityYConvolutionL2_ae_eq_raw
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hEnvelope : VorticityEnvelope u g t)
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    (h3BKMDyadicVorticityYConvolutionL2
        hInt hMeas R hR i k :
        H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3BKMDyadicVorticityYConvolutionRaw
      u t R hR i k := by

  have hM : 0 ≤ g t :=
    (norm_nonneg
      (h3BKMPhysicalVorticityY u t (0 : Point3))).trans
      (norm_h3BKMPhysicalVorticityY_le
        hEnvelope (0 : Point3))

  unfold h3BKMDyadicVorticityYConvolutionL2
  unfold h3BKMDyadicVorticityYConvolutionRaw

  exact
    h3L1L2Convolution_ae_eq_boundedRepresentatives
      (h3BKMDyadicKernelL1 R hR i k)
      (h3PhysicalScalarL2EuclideanComplex
        (h3BKMPhysicalVorticityYL2
          u t hInt hMeas))
      (h3BKMDyadicKernel R hR i k)
      (fun ξ : H3FourierPoint3 =>
        h3BKMPhysicalVorticityY
          u t
          ((WithLp.ofLp :
            H3FourierPoint3 → Point3) ξ))
      (g t)
      (h3BKMDyadicKernelL1_ae hR i k)
      (h3BKMDyadicKernel_integrable hR i k)
      (h3BKMPhysicalVorticityYEuclideanComplex_ae
        hInt hMeas)
      (fun ξ =>
        norm_h3BKMPhysicalVorticityY_le
          hEnvelope
          ((WithLp.ofLp :
            H3FourierPoint3 → Point3) ξ))
      hM

theorem h3BKMDyadicVorticityZConvolutionL2_ae_eq_raw
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hEnvelope : VorticityEnvelope u g t)
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    (h3BKMDyadicVorticityZConvolutionL2
        hInt hMeas R hR i k :
        H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3BKMDyadicVorticityZConvolutionRaw
      u t R hR i k := by

  have hM : 0 ≤ g t :=
    (norm_nonneg
      (h3BKMPhysicalVorticityZ u t (0 : Point3))).trans
      (norm_h3BKMPhysicalVorticityZ_le
        hEnvelope (0 : Point3))

  unfold h3BKMDyadicVorticityZConvolutionL2
  unfold h3BKMDyadicVorticityZConvolutionRaw

  exact
    h3L1L2Convolution_ae_eq_boundedRepresentatives
      (h3BKMDyadicKernelL1 R hR i k)
      (h3PhysicalScalarL2EuclideanComplex
        (h3BKMPhysicalVorticityZL2
          u t hInt hMeas))
      (h3BKMDyadicKernel R hR i k)
      (fun ξ : H3FourierPoint3 =>
        h3BKMPhysicalVorticityZ
          u t
          ((WithLp.ofLp :
            H3FourierPoint3 → Point3) ξ))
      (g t)
      (h3BKMDyadicKernelL1_ae hR i k)
      (h3BKMDyadicKernel_integrable hR i k)
      (h3BKMPhysicalVorticityZEuclideanComplex_ae
        hInt hMeas)
      (fun ξ =>
        norm_h3BKMPhysicalVorticityZ_le
          hEnvelope
          ((WithLp.ofLp :
            H3FourierPoint3 → Point3) ξ))
      hM

end

end Euclidean
end Bridge
end PrimeTensor
