import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.SchwartzSpectralHeatReconstructionL2Bridge
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Positive-time classical / L² Fourier reconstruction compatibility

The positive-time heat smoothing layer now gives two reconstructions of the
same deweighted spectral amplitude:

* the ordinary inverse Fourier integral, which is spatially `C³`; and
* Mathlib's unitary `L²` inverse Fourier transform, which is the decoder used
  by the mild restart stack.

This file proves the standard `L¹ ∩ L²` compatibility theorem needed to
identify those two objects almost everywhere.  The proof compares both
reconstructions against compactly supported smooth test functions.  Fubini
moves the ordinary inverse Fourier integral onto the test function, while the
tempered-distribution compatibility of the `L²` inverse transform gives the
same pairing on the Plancherel side.  Distributional uniqueness then yields
a.e. equality.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform SchwartzMap
open scoped ENNReal NNReal Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzHeatReconstructionCompatibility
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/--
Generic `L¹ ∩ L²` compatibility for the inverse Fourier transform on the H³
frequency space.  The ordinary inverse Fourier integral agrees almost
everywhere with Mathlib's unitary `L²` inverse Fourier transform of the same
function.
-/
theorem h3FourierInv_integrable_memLp2_ae_eq_L2
    {f : H3FourierPoint3 → ℂ}
    (hf1 : Integrable f (volume : Measure H3FourierPoint3))
    (hf2 : MemLp f 2 (volume : Measure H3FourierPoint3)) :
    FourierTransformInv.fourierInv f
      =ᵐ[volume]
    ((MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ).symm
        (hf2.toLp f) : H3FourierPoint3 → ℂ) := by
  let f2 : H3FourierComplexL2 := hf2.toLp f
  let u2 : H3FourierComplexL2 :=
    (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ).symm f2

  have hInnerNegContinuous :
      Continuous (fun p : H3FourierPoint3 × H3FourierPoint3 =>
        ((-(innerₗ H3FourierPoint3)) p.1) p.2) := by
    change Continuous (fun p : H3FourierPoint3 × H3FourierPoint3 =>
      -inner ℝ p.1 p.2)
    exact (continuous_inner (𝕜 := ℝ) (E := H3FourierPoint3)).neg

  have hClassicalContinuous :
      Continuous (FourierTransformInv.fourierInv f) := by
    change Continuous
      (VectorFourier.fourierIntegral
        Real.fourierChar
        (volume : Measure H3FourierPoint3)
        (-(innerₗ H3FourierPoint3))
        f)
    exact
      VectorFourier.fourierIntegral_continuous
        Real.continuous_fourierChar
        hInnerNegContinuous
        hf1

  have hClassicalLocallyIntegrable :
      LocallyIntegrable
        (FourierTransformInv.fourierInv f)
        (volume : Measure H3FourierPoint3) :=
    hClassicalContinuous.locallyIntegrable

  have hL2LocallyIntegrable :
      LocallyIntegrable
        ((u2 : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
        (volume : Measure H3FourierPoint3) :=
    (MeasureTheory.Lp.memLp u2).locallyIntegrable (by norm_num)

  change
    FourierTransformInv.fourierInv f
      =ᵐ[volume]
    ((u2 : H3FourierComplexL2) : H3FourierPoint3 → ℂ)

  apply
    ae_eq_of_integral_contDiff_smul_eq
      hClassicalLocallyIntegrable
      hL2LocallyIntegrable

  intro g hg hgCompact

  let gc : H3FourierPoint3 → ℂ := Complex.ofRealCLM ∘ g

  have hgcSmooth : ContDiff ℝ (↑(⊤ : ℕ∞)) gc := by
    dsimp [gc]
    simpa [Function.comp_def] using
      (hg.continuousLinearMap_comp Complex.ofRealCLM)

  have hgcCompact : HasCompactSupport gc := by
    dsimp [gc]
    exact hgCompact.comp_left rfl

  have hgcIntegrable :
      Integrable gc (volume : Measure H3FourierPoint3) :=
    hgcSmooth.continuous.integrable_of_hasCompactSupport hgcCompact

  let ψ : SchwartzMap H3FourierPoint3 ℂ :=
    hgcCompact.toSchwartzMap hgcSmooth

  have hflip :
      (-(innerₗ H3FourierPoint3)).flip =
        -(innerₗ H3FourierPoint3) := by
    ext x y
    simp [LinearMap.flip_apply, real_inner_comm]

  have hClassicalPair :=
    VectorFourier.integral_fourierIntegral_smul_eq_flip
      (e := Real.fourierChar)
      (μ := (volume : Measure H3FourierPoint3))
      (ν := (volume : Measure H3FourierPoint3))
      (L := -(innerₗ H3FourierPoint3))
      (f := f)
      (g := gc)
      Real.continuous_fourierChar
      hInnerNegContinuous
      hf1
      hgcIntegrable

  rw [hflip] at hClassicalPair
  change
    (∫ ξ : H3FourierPoint3,
        FourierTransformInv.fourierInv f ξ • gc ξ) =
      ∫ x : H3FourierPoint3,
        f x • FourierTransformInv.fourierInv gc x
    at hClassicalPair

  have hClassicalPair' :
      (∫ x : H3FourierPoint3,
          gc x * FourierTransformInv.fourierInv f x) =
        ∫ ξ : H3FourierPoint3,
          FourierTransformInv.fourierInv gc ξ * f ξ := by
    simpa only [smul_eq_mul, mul_comm] using hClassicalPair

  have hDistribution :=
    MeasureTheory.Lp.fourierInv_toTemperedDistribution_eq f2

  change
    FourierTransformInv.fourierInv
        ((f2 : H3FourierComplexL2) : 𝓢'(H3FourierPoint3, ℂ))
      =
    ((u2 : H3FourierComplexL2) : 𝓢'(H3FourierPoint3, ℂ))
    at hDistribution

  have hDistributionAtTest :=
    congrArg
      (fun T : 𝓢'(H3FourierPoint3, ℂ) => T ψ)
      hDistribution

  have hf2ae :
      ((f2 : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
        =ᵐ[volume] f := by
    dsimp [f2]
    exact hf2.coeFn_toLp

  have hDistributionPair :
      (∫ ξ : H3FourierPoint3,
          FourierTransformInv.fourierInv gc ξ * f ξ) =
        ∫ x : H3FourierPoint3,
          gc x * ((u2 : H3FourierComplexL2) x) := by
    simp only [TemperedDistribution.fourierInv_apply,
      MeasureTheory.Lp.toTemperedDistribution_apply, smul_eq_mul]
      at hDistributionAtTest

    have hψcoe :
        (ψ : H3FourierPoint3 → ℂ) = gc := by
      funext x
      simp [ψ]

    have hψinv :
        ((FourierTransformInv.fourierInv ψ :
            SchwartzMap H3FourierPoint3 ℂ) : H3FourierPoint3 → ℂ)
          = FourierTransformInv.fourierInv gc := by
      rw [SchwartzMap.fourierInv_coe]
      simp [hψcoe]

    rw [hψinv] at hDistributionAtTest

    have hLeft :
        (∫ ξ : H3FourierPoint3,
            FourierTransformInv.fourierInv gc ξ *
              ((f2 : H3FourierComplexL2) ξ)) =
          ∫ ξ : H3FourierPoint3,
            FourierTransformInv.fourierInv gc ξ * f ξ := by
      apply integral_congr_ae
      filter_upwards [hf2ae] with ξ hξ
      rw [hξ]

    have hRight :
        (∫ x : H3FourierPoint3,
            (ψ x) * ((u2 : H3FourierComplexL2) x)) =
          ∫ x : H3FourierPoint3,
            gc x * ((u2 : H3FourierComplexL2) x) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by rw [hψcoe])

    rw [hLeft, hRight] at hDistributionAtTest
    exact hDistributionAtTest

  calc
    (∫ x : H3FourierPoint3,
        g x • FourierTransformInv.fourierInv f x)
        = ∫ x : H3FourierPoint3,
            gc x * FourierTransformInv.fourierInv f x := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun x => by
            simp [gc, Function.comp_apply, Complex.real_smul])
    _ = ∫ ξ : H3FourierPoint3,
          FourierTransformInv.fourierInv gc ξ * f ξ :=
      hClassicalPair'
    _ = ∫ x : H3FourierPoint3,
          gc x * ((u2 : H3FourierComplexL2) x) :=
      hDistributionPair
    _ = ∫ x : H3FourierPoint3,
          g x • ((u2 : H3FourierComplexL2) x) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        simp [gc, Function.comp_apply, Complex.real_smul])

/-- Positive heat time makes the raw deweighted spectral representative
integrable. -/
theorem h3SpectralScalarHeatRawRepresentative_integrable
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState) :
    Integrable
      (h3SpectralScalarHeatRawRepresentative ν t G)
      (volume : Measure H3FourierPoint3) := by
  rw [← integrable_norm_iff
    (h3SpectralScalarHeatRawRepresentative_aestronglyMeasurable ν t G)]
  simpa using
    (h3SpectralScalarHeatRawRepresentative_moment_integrable
      hν ht G 0 (by norm_num))

/--
The spatially `C³` ordinary inverse-Fourier reconstruction of a positive-time
heat-evolved H³ state agrees almost everywhere with the existing complex `L²`
decoder of that same state.
-/
theorem h3SpectralScalarHeatC3Representative_ae_eq_decodeComplexL2
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState) :
    h3SpectralScalarHeatC3Representative ν t G
      =ᵐ[volume]
    ((h3SpectralScalarDecodeComplexL2
        (h3SpectralScalarHeatApplyNN
          ν hν.le (NNReal.mk t ht.le) G) :
      H3ComplexPhysicalScalarL2) : H3FourierPoint3 → ℂ) := by
  have hCompat :=
    h3FourierInv_integrable_memLp2_ae_eq_L2
      (h3SpectralScalarHeatRawRepresentative_integrable hν ht G)
      (h3SpectralScalarHeatRawRepresentative_memLp2 hν ht G)

  unfold h3SpectralScalarHeatC3Representative
  rw [
    h3SpectralScalarDecodeComplexL2_heatApplyNN_eq_fourierInv_rawRepresentativeL2
      hν ht G
  ]

  simpa [h3SpectralScalarHeatRawRepresentativeL2] using hCompat

end

end Euclidean
end Bridge
end PrimeTensor
