import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Weighted.Convolution.Majorant.Local
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Representatives of the weighted H³ Young majorants

The real endpoint Young construction returns bundled `L²` states, while the weighted Fourier
estimate is written using scalar convolution integrals.  This file identifies the two bundled
states with the two scalar majorants almost everywhere.

The identification never evaluates an `L²` equivalence class at a fixed point.  Instead, on every
measurable finite-measure set `s` we pair the bundled Young state with the `L²` indicator of `s`.
The pairing is exactly the set integral.  Since continuous linear functionals commute with the
Bochner integral, this becomes an iterated scalar integral.  Fubini, justified by the local control
proved in `WeightedConvolutionMajorantLocal`, shows that the scalar majorant has the same set
integral.  Sigma-finite uniqueness then gives the desired a.e. equality.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter ContinuousLinearMap
open scoped ENNReal NNReal InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3WeightedConvolutionMajorantRepresentatives
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Product integrability needed to swap the first scalar majorant over a finite-measure set. -/
theorem h3FirstYoungMajorant_fubini_integrable
    (F G : H3SpectralScalarState)
    (s : Set H3FourierPoint3)
    (hs : MeasurableSet s)
    (hμs : (volume : Measure H3FourierPoint3) s < ∞) :
    Integrable
      (Function.uncurry
        (fun ξ η : H3FourierPoint3 =>
          ‖h3SpectralScalarRawFourier G η‖ * ‖F (ξ - η)‖))
      (((volume : Measure H3FourierPoint3).restrict s).prod
        (volume : Measure H3FourierPoint3)) := by
  have hRaw :
      AEStronglyMeasurable
        (fun η : H3FourierPoint3 =>
          ‖h3SpectralScalarRawFourier G η‖)
        (volume : Measure H3FourierPoint3) :=
    (h3SpectralScalarRawFourier_memLp2 G).1.norm

  have hWeighted :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 => ‖F ξ‖)
        (volume : Measure H3FourierPoint3) :=
    (MeasureTheory.Lp.aestronglyMeasurable F).norm

  have hJointFull :
      AEStronglyMeasurable
        (fun p : H3FourierPoint3 × H3FourierPoint3 =>
          ‖h3SpectralScalarRawFourier G p.2‖ * ‖F (p.1 - p.2)‖)
        ((volume : Measure H3FourierPoint3).prod
          (volume : Measure H3FourierPoint3)) := by
    simpa only [mul_apply'] using
      hRaw.convolution_integrand (mul ℝ ℝ) hWeighted

  have hJoint :
      AEStronglyMeasurable
        (fun p : H3FourierPoint3 × H3FourierPoint3 =>
          ‖h3SpectralScalarRawFourier G p.2‖ * ‖F (p.1 - p.2)‖)
        (((volume : Measure H3FourierPoint3).restrict s).prod
          (volume : Measure H3FourierPoint3)) :=
    hJointFull.mono_measure
      (Measure.prod_mono Measure.restrict_le_self le_rfl)

  refine (integrable_prod_iff hJoint).2 ?_
  constructor
  · exact
      Eventually.of_forall fun ξ =>
        h3FirstYoungMajorant_oriented_integrable F G ξ
  · have hLocal :=
      h3FirstYoungMajorant_integrableOn_finite F G s hs hμs
    refine hLocal.congr ?_
    filter_upwards with ξ
    apply integral_congr_ae
    filter_upwards with η
    rw [Real.norm_eq_abs, abs_of_nonneg]
    positivity

/-- Product integrability needed to swap the second scalar majorant over a finite-measure set. -/
theorem h3SecondYoungMajorant_fubini_integrable
    (F G : H3SpectralScalarState)
    (s : Set H3FourierPoint3)
    (hs : MeasurableSet s)
    (hμs : (volume : Measure H3FourierPoint3) s < ∞) :
    Integrable
      (Function.uncurry
        (fun ξ η : H3FourierPoint3 =>
          ‖h3SpectralScalarRawFourier F η‖ * ‖G (ξ - η)‖))
      (((volume : Measure H3FourierPoint3).restrict s).prod
        (volume : Measure H3FourierPoint3)) := by
  have hRaw :
      AEStronglyMeasurable
        (fun η : H3FourierPoint3 =>
          ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3) :=
    (h3SpectralScalarRawFourier_memLp2 F).1.norm

  have hWeighted :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 => ‖G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    (MeasureTheory.Lp.aestronglyMeasurable G).norm

  have hJointFull :
      AEStronglyMeasurable
        (fun p : H3FourierPoint3 × H3FourierPoint3 =>
          ‖h3SpectralScalarRawFourier F p.2‖ * ‖G (p.1 - p.2)‖)
        ((volume : Measure H3FourierPoint3).prod
          (volume : Measure H3FourierPoint3)) := by
    simpa only [mul_apply'] using
      hRaw.convolution_integrand (mul ℝ ℝ) hWeighted

  have hJoint :
      AEStronglyMeasurable
        (fun p : H3FourierPoint3 × H3FourierPoint3 =>
          ‖h3SpectralScalarRawFourier F p.2‖ * ‖G (p.1 - p.2)‖)
        (((volume : Measure H3FourierPoint3).restrict s).prod
          (volume : Measure H3FourierPoint3)) :=
    hJointFull.mono_measure
      (Measure.prod_mono Measure.restrict_le_self le_rfl)

  refine (integrable_prod_iff hJoint).2 ?_
  constructor
  · exact
      Eventually.of_forall fun ξ =>
        h3SecondYoungMajorant_oriented_integrable F G ξ
  · have hLocal :=
      h3SecondYoungMajorant_integrableOn_finite F G s hs hμs
    refine hLocal.congr ?_
    filter_upwards with ξ
    apply integral_congr_ae
    filter_upwards with η
    rw [Real.norm_eq_abs, abs_of_nonneg]
    positivity

/-- Fubini orientation of the first scalar majorant on a finite-measure set. -/
theorem h3FirstYoungMajorant_setIntegral_eq_iterated
    (F G : H3SpectralScalarState)
    (s : Set H3FourierPoint3)
    (hs : MeasurableSet s)
    (hμs : (volume : Measure H3FourierPoint3) s < ∞) :
    (∫ ξ in s, h3FirstYoungMajorant F G ξ)
      =
    ∫ η : H3FourierPoint3,
      ∫ ξ in s,
        ‖h3SpectralScalarRawFourier G η‖ * ‖F (ξ - η)‖ := by
  have hSwap :=
    integral_integral_swap
      (h3FirstYoungMajorant_fubini_integrable F G s hs hμs)
  simpa [h3FirstYoungMajorant] using hSwap

/-- Fubini orientation of the second scalar majorant on a finite-measure set. -/
theorem h3SecondYoungMajorant_setIntegral_eq_iterated
    (F G : H3SpectralScalarState)
    (s : Set H3FourierPoint3)
    (hs : MeasurableSet s)
    (hμs : (volume : Measure H3FourierPoint3) s < ∞) :
    (∫ ξ in s, h3SecondYoungMajorant F G ξ)
      =
    ∫ η : H3FourierPoint3,
      ∫ ξ in s,
        ‖h3SpectralScalarRawFourier F η‖ * ‖G (ξ - η)‖ := by
  have hSwap :=
    integral_integral_swap
      (h3SecondYoungMajorant_fubini_integrable F G s hs hμs)
  simpa [h3SecondYoungMajorant] using hSwap

/-- The first abstract Young candidate has the same finite-set integral as its scalar kernel. -/
theorem h3FirstYoungMajorantCandidateL2_setIntegral_eq_iterated
    (F G : H3SpectralScalarState)
    (s : Set H3FourierPoint3)
    (hs : MeasurableSet s)
    (hμs : (volume : Measure H3FourierPoint3) s < ∞) :
    (∫ ξ in s,
        (h3FirstYoungMajorantCandidateL2 F G : H3FourierPoint3 → ℝ) ξ)
      =
    ∫ η : H3FourierPoint3,
      ∫ ξ in s,
        ‖h3SpectralScalarRawFourier G η‖ * ‖F (ξ - η)‖ := by
  let f : H3FourierRealL1 := h3RawFourierNormRealL1 G
  let g : H3FourierRealL2 := h3WeightedNormRealL2 F
  let c : H3FourierRealL2 :=
    indicatorConstLp 2 hs hμs.ne (1 : ℝ)

  have hInt :
      Integrable
        (h3RealL1L2ConvolutionIntegrand f g)
        (volume : Measure H3FourierPoint3) :=
    h3RealL1L2ConvolutionIntegrand_integrable f g

  have hCandidate :
      h3FirstYoungMajorantCandidateL2 F G
        = h3RealL1L2Convolution f g := by
    rfl

  calc
    (∫ ξ in s,
        (h3FirstYoungMajorantCandidateL2 F G : H3FourierPoint3 → ℝ) ξ)
        = inner ℝ c (h3FirstYoungMajorantCandidateL2 F G) := by
            symm
            simpa [c] using
              (L2.inner_indicatorConstLp_one
                (𝕜 := ℝ)
                hs
                hμs.ne
                (h3FirstYoungMajorantCandidateL2 F G))
    _ = inner ℝ c
          (∫ η : H3FourierPoint3,
            h3RealL1L2ConvolutionIntegrand f g η) := by
          rw [hCandidate]
          rfl
    _ = ∫ η : H3FourierPoint3,
          inner ℝ c (h3RealL1L2ConvolutionIntegrand f g η) := by
          exact (integral_inner hInt c).symm
    _ = ∫ η : H3FourierPoint3,
          ∫ ξ in s,
            (h3RealL1L2ConvolutionIntegrand f g η :
              H3FourierPoint3 → ℝ) ξ := by
          apply integral_congr_ae
          filter_upwards with η
          simpa [c] using
            (L2.inner_indicatorConstLp_one
              (𝕜 := ℝ)
              hs
              hμs.ne
              (h3RealL1L2ConvolutionIntegrand f g η))
    _ = ∫ η : H3FourierPoint3,
          ∫ ξ in s,
            ‖h3SpectralScalarRawFourier G η‖ * ‖F (ξ - η)‖ := by
          apply integral_congr_ae
          filter_upwards [h3RawFourierNormRealL1_ae G] with η hRawη
          have hRawη' :
              f η = ‖h3SpectralScalarRawFourier G η‖ := by
            simpa [f] using hRawη
          have hShift :
              (fun ξ : H3FourierPoint3 => g (ξ - η))
                =ᵐ[volume]
              (fun ξ : H3FourierPoint3 => ‖F (ξ - η)‖) := by
            have h :=
              (h3MeasurePreserving_sub_right η).quasiMeasurePreserving.ae_eq_comp
                (h3WeightedNormRealL2_ae F)
            simpa [g, Function.comp_def] using h
          have hIntegrand := h3RealL1L2ConvolutionIntegrand_ae f g η
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
          rw [hIntegrandξ, hShiftξ, hRawη']

/-- The second abstract Young candidate has the same finite-set integral as its scalar kernel. -/
theorem h3SecondYoungMajorantCandidateL2_setIntegral_eq_iterated
    (F G : H3SpectralScalarState)
    (s : Set H3FourierPoint3)
    (hs : MeasurableSet s)
    (hμs : (volume : Measure H3FourierPoint3) s < ∞) :
    (∫ ξ in s,
        (h3SecondYoungMajorantCandidateL2 F G : H3FourierPoint3 → ℝ) ξ)
      =
    ∫ η : H3FourierPoint3,
      ∫ ξ in s,
        ‖h3SpectralScalarRawFourier F η‖ * ‖G (ξ - η)‖ := by
  let f : H3FourierRealL1 := h3RawFourierNormRealL1 F
  let g : H3FourierRealL2 := h3WeightedNormRealL2 G
  let c : H3FourierRealL2 :=
    indicatorConstLp 2 hs hμs.ne (1 : ℝ)

  have hInt :
      Integrable
        (h3RealL1L2ConvolutionIntegrand f g)
        (volume : Measure H3FourierPoint3) :=
    h3RealL1L2ConvolutionIntegrand_integrable f g

  have hCandidate :
      h3SecondYoungMajorantCandidateL2 F G
        = h3RealL1L2Convolution f g := by
    rfl

  calc
    (∫ ξ in s,
        (h3SecondYoungMajorantCandidateL2 F G : H3FourierPoint3 → ℝ) ξ)
        = inner ℝ c (h3SecondYoungMajorantCandidateL2 F G) := by
            symm
            simpa [c] using
              (L2.inner_indicatorConstLp_one
                (𝕜 := ℝ)
                hs
                hμs.ne
                (h3SecondYoungMajorantCandidateL2 F G))
    _ = inner ℝ c
          (∫ η : H3FourierPoint3,
            h3RealL1L2ConvolutionIntegrand f g η) := by
          rw [hCandidate]
          rfl
    _ = ∫ η : H3FourierPoint3,
          inner ℝ c (h3RealL1L2ConvolutionIntegrand f g η) := by
          exact (integral_inner hInt c).symm
    _ = ∫ η : H3FourierPoint3,
          ∫ ξ in s,
            (h3RealL1L2ConvolutionIntegrand f g η :
              H3FourierPoint3 → ℝ) ξ := by
          apply integral_congr_ae
          filter_upwards with η
          simpa [c] using
            (L2.inner_indicatorConstLp_one
              (𝕜 := ℝ)
              hs
              hμs.ne
              (h3RealL1L2ConvolutionIntegrand f g η))
    _ = ∫ η : H3FourierPoint3,
          ∫ ξ in s,
            ‖h3SpectralScalarRawFourier F η‖ * ‖G (ξ - η)‖ := by
          apply integral_congr_ae
          filter_upwards [h3RawFourierNormRealL1_ae F] with η hRawη
          have hRawη' :
              f η = ‖h3SpectralScalarRawFourier F η‖ := by
            simpa [f] using hRawη
          have hShift :
              (fun ξ : H3FourierPoint3 => g (ξ - η))
                =ᵐ[volume]
              (fun ξ : H3FourierPoint3 => ‖G (ξ - η)‖) := by
            have h :=
              (h3MeasurePreserving_sub_right η).quasiMeasurePreserving.ae_eq_comp
                (h3WeightedNormRealL2_ae G)
            simpa [g, Function.comp_def] using h
          have hIntegrand := h3RealL1L2ConvolutionIntegrand_ae f g η
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
          rw [hIntegrandξ, hShiftξ, hRawη']

/-- Equality of finite-set integrals for the first candidate and scalar majorant. -/
theorem h3FirstYoungMajorantCandidateL2_setIntegral_eq_majorant
    (F G : H3SpectralScalarState)
    (s : Set H3FourierPoint3)
    (hs : MeasurableSet s)
    (hμs : (volume : Measure H3FourierPoint3) s < ∞) :
    (∫ ξ in s,
        (h3FirstYoungMajorantCandidateL2 F G : H3FourierPoint3 → ℝ) ξ)
      =
    ∫ ξ in s, h3FirstYoungMajorant F G ξ := by
  rw [
    h3FirstYoungMajorantCandidateL2_setIntegral_eq_iterated F G s hs hμs,
    ← h3FirstYoungMajorant_setIntegral_eq_iterated F G s hs hμs
  ]

/-- Equality of finite-set integrals for the second candidate and scalar majorant. -/
theorem h3SecondYoungMajorantCandidateL2_setIntegral_eq_majorant
    (F G : H3SpectralScalarState)
    (s : Set H3FourierPoint3)
    (hs : MeasurableSet s)
    (hμs : (volume : Measure H3FourierPoint3) s < ∞) :
    (∫ ξ in s,
        (h3SecondYoungMajorantCandidateL2 F G : H3FourierPoint3 → ℝ) ξ)
      =
    ∫ ξ in s, h3SecondYoungMajorant F G ξ := by
  rw [
    h3SecondYoungMajorantCandidateL2_setIntegral_eq_iterated F G s hs hμs,
    ← h3SecondYoungMajorant_setIntegral_eq_iterated F G s hs hμs
  ]

/-- The first real endpoint Young state represents the first scalar majorant a.e. -/
theorem h3FirstYoungMajorantCandidateL2_ae
    (F G : H3SpectralScalarState) :
    (h3FirstYoungMajorantCandidateL2 F G : H3FourierPoint3 → ℝ)
      =ᵐ[volume]
    h3FirstYoungMajorant F G := by
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
  · intro s hs hμs
    exact h3FirstYoungMajorantCandidateL2_integrableOn_finite F G s hs hμs
  · intro s hs hμs
    exact h3FirstYoungMajorant_integrableOn_finite F G s hs hμs
  · intro s hs hμs
    exact h3FirstYoungMajorantCandidateL2_setIntegral_eq_majorant F G s hs hμs

/-- The second real endpoint Young state represents the second scalar majorant a.e. -/
theorem h3SecondYoungMajorantCandidateL2_ae
    (F G : H3SpectralScalarState) :
    (h3SecondYoungMajorantCandidateL2 F G : H3FourierPoint3 → ℝ)
      =ᵐ[volume]
    h3SecondYoungMajorant F G := by
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
  · intro s hs hμs
    exact h3SecondYoungMajorantCandidateL2_integrableOn_finite F G s hs hμs
  · intro s hs hμs
    exact h3SecondYoungMajorant_integrableOn_finite F G s hs hμs
  · intro s hs hμs
    exact h3SecondYoungMajorantCandidateL2_setIntegral_eq_majorant F G s hs hμs

/-- The first scalar Young majorant genuinely belongs to `L²`. -/
theorem h3FirstYoungMajorant_memLp2
    (F G : H3SpectralScalarState) :
    MemLp
      (h3FirstYoungMajorant F G)
      2
      (volume : Measure H3FourierPoint3) := by
  refine
    (MeasureTheory.Lp.memLp
      (h3FirstYoungMajorantCandidateL2 F G)).congr_norm
      (h3FirstYoungMajorant_aestronglyMeasurable F G)
      ?_
  filter_upwards [h3FirstYoungMajorantCandidateL2_ae F G] with ξ hξ
  rw [hξ]

/-- The second scalar Young majorant genuinely belongs to `L²`. -/
theorem h3SecondYoungMajorant_memLp2
    (F G : H3SpectralScalarState) :
    MemLp
      (h3SecondYoungMajorant F G)
      2
      (volume : Measure H3FourierPoint3) := by
  refine
    (MeasureTheory.Lp.memLp
      (h3SecondYoungMajorantCandidateL2 F G)).congr_norm
      (h3SecondYoungMajorant_aestronglyMeasurable F G)
      ?_
  filter_upwards [h3SecondYoungMajorantCandidateL2_ae F G] with ξ hξ
  rw [hξ]

/-- Bundled `L²` realization of the first scalar Young majorant. -/
noncomputable def h3FirstYoungMajorantL2
    (F G : H3SpectralScalarState) :
    H3FourierRealL2 :=
  (h3FirstYoungMajorant_memLp2 F G).toLp
    (h3FirstYoungMajorant F G)

/-- Bundled `L²` realization of the second scalar Young majorant. -/
noncomputable def h3SecondYoungMajorantL2
    (F G : H3SpectralScalarState) :
    H3FourierRealL2 :=
  (h3SecondYoungMajorant_memLp2 F G).toLp
    (h3SecondYoungMajorant F G)

/-- The bundled first majorant has the expected scalar representative. -/
theorem h3FirstYoungMajorantL2_ae
    (F G : H3SpectralScalarState) :
    (h3FirstYoungMajorantL2 F G : H3FourierPoint3 → ℝ)
      =ᵐ[volume]
    h3FirstYoungMajorant F G := by
  exact MemLp.coeFn_toLp (h3FirstYoungMajorant_memLp2 F G)

/-- The bundled second majorant has the expected scalar representative. -/
theorem h3SecondYoungMajorantL2_ae
    (F G : H3SpectralScalarState) :
    (h3SecondYoungMajorantL2 F G : H3FourierPoint3 → ℝ)
      =ᵐ[volume]
    h3SecondYoungMajorant F G := by
  exact MemLp.coeFn_toLp (h3SecondYoungMajorant_memLp2 F G)

/-- The packaged first scalar majorant is the abstract endpoint-Young state. -/
theorem h3FirstYoungMajorantL2_eq_candidate
    (F G : H3SpectralScalarState) :
    h3FirstYoungMajorantL2 F G
      = h3FirstYoungMajorantCandidateL2 F G := by
  apply MeasureTheory.Lp.ext
  exact
    (h3FirstYoungMajorantL2_ae F G).trans
      (h3FirstYoungMajorantCandidateL2_ae F G).symm

/-- The packaged second scalar majorant is the abstract endpoint-Young state. -/
theorem h3SecondYoungMajorantL2_eq_candidate
    (F G : H3SpectralScalarState) :
    h3SecondYoungMajorantL2 F G
      = h3SecondYoungMajorantCandidateL2 F G := by
  apply MeasureTheory.Lp.ext
  exact
    (h3SecondYoungMajorantL2_ae F G).trans
      (h3SecondYoungMajorantCandidateL2_ae F G).symm

/-- Endpoint Young `L²` bound for the actual first scalar majorant. -/
theorem norm_h3FirstYoungMajorantL2_le
    (F G : H3SpectralScalarState) :
    ‖h3FirstYoungMajorantL2 F G‖
      ≤ h3SobolevDeweightingConstant * ‖G‖ * ‖F‖ := by
  rw [h3FirstYoungMajorantL2_eq_candidate]
  exact norm_h3FirstYoungMajorantCandidateL2_le F G

/-- Endpoint Young `L²` bound for the actual second scalar majorant. -/
theorem norm_h3SecondYoungMajorantL2_le
    (F G : H3SpectralScalarState) :
    ‖h3SecondYoungMajorantL2 F G‖
      ≤ h3SobolevDeweightingConstant * ‖F‖ * ‖G‖ := by
  rw [h3SecondYoungMajorantL2_eq_candidate]
  exact norm_h3SecondYoungMajorantCandidateL2_le F G

end

end Euclidean
end Bridge
end PrimeTensor
