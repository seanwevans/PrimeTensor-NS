import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.H3.Real.C1.Product
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Spectral.Realizability.Bridge
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Pointwise reality of realizable H³ C¹ representatives

The spectral realizability layer proves that the exact complex inverse-Fourier
decoder of a realizable weighted H³ state is the complexification of its
canonical real decoder.  That statement lives in physical `L²`.

The arbitrary-H³ classicalization layer independently constructs continuous
`C¹` representatives of both decoders and proves agreement almost everywhere.

Because Euclidean volume assigns positive measure to every nonempty open set,
two continuous representatives that agree almost everywhere agree everywhere.
Thus realizability upgrades from an `L²` range condition to the pointwise
identity

    C1Rep(G)(x) = (RealC1Rep(G)(x) : ℂ).

In particular the imaginary part of the canonical complex representative
vanishes pointwise.  Combining this with the exact complex H³ product theorem
gives the corresponding exact real pointwise product theorem, including the
project's `Point3` carrier.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeH3C1RealizablePointwise
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- A realizable H³ scalar state's canonical complex C¹ representative is
pointwise the complexification of its canonical real C¹ representative. -/
theorem h3SpectralScalarC1Representative_eq_ofReal_real_of_realizable
    (G : H3SpectralScalarState)
    (hG : H3SpectralScalarRealizable G) :
    h3SpectralScalarC1Representative G
      =
    fun x : H3FourierPoint3 =>
      (h3SpectralScalarRealC1Representative G x : ℂ) := by
  have hComplex :
      h3SpectralScalarC1Representative G
        =ᵐ[(volume : Measure H3FourierPoint3)]
      ((h3SpectralScalarDecodeComplexL2 G : H3ComplexPhysicalScalarL2) :
        H3FourierPoint3 → ℂ) :=
    h3SpectralScalarC1Representative_ae_eq_decodeComplexL2 G

  have hReal :
      h3SpectralScalarRealC1Representative G
        =ᵐ[(volume : Measure H3FourierPoint3)]
      ((h3SpectralScalarDecodeRealL2 G : H3RealPhysicalScalarL2) :
        H3FourierPoint3 → ℝ) :=
    h3SpectralScalarRealC1Representative_ae_eq_decodeRealL2 G

  have hDecoder :
      ((h3SpectralScalarDecodeComplexL2 G : H3ComplexPhysicalScalarL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun x : H3FourierPoint3 =>
        ((h3SpectralScalarDecodeRealL2 G : H3RealPhysicalScalarL2) x : ℂ)) := by
    rw [hG]
    unfold h3ComplexifyFourierL2
    exact
      Complex.ofRealCLM.coeFn_compLp
        (h3SpectralScalarDecodeRealL2 G)

  have hAE :
      h3SpectralScalarC1Representative G
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun x : H3FourierPoint3 =>
        (h3SpectralScalarRealC1Representative G x : ℂ)) := by
    filter_upwards [hComplex, hReal, hDecoder] with x hxC hxR hxD
    rw [hxC, hxD, hxR]

  have hLeft :
      Continuous
        (h3SpectralScalarC1Representative G) :=
    (h3SpectralScalarC1Representative_contDiff_one G).continuous

  have hRight :
      Continuous
        (fun x : H3FourierPoint3 =>
          (h3SpectralScalarRealC1Representative G x : ℂ)) := by
    change
      Continuous
        (Complex.ofRealCLM ∘
          h3SpectralScalarRealC1Representative G)
    exact
      Complex.ofRealCLM.continuous.comp
        (h3SpectralScalarRealC1Representative_contDiff_one G).continuous

  exact
    (hLeft.ae_eq_iff_eq
      (volume : Measure H3FourierPoint3)
      hRight).mp hAE

/-- Pointwise form of the realizability upgrade. -/
theorem h3SpectralScalarC1Representative_eq_ofReal_real_at_of_realizable
    (G : H3SpectralScalarState)
    (hG : H3SpectralScalarRealizable G)
    (x : H3FourierPoint3) :
    h3SpectralScalarC1Representative G x
      =
    (h3SpectralScalarRealC1Representative G x : ℂ) := by
  exact
    congrFun
      (h3SpectralScalarC1Representative_eq_ofReal_real_of_realizable
        G hG)
      x

/-- The canonical complex C¹ representative of a realizable H³ state has zero
imaginary part at every point. -/
theorem h3SpectralScalarC1Representative_im_eq_zero_of_realizable
    (G : H3SpectralScalarState)
    (hG : H3SpectralScalarRealizable G)
    (x : H3FourierPoint3) :
    (h3SpectralScalarC1Representative G x).im = 0 := by
  rw [
    h3SpectralScalarC1Representative_eq_ofReal_real_at_of_realizable
      G hG x
  ]
  simp

/-- Exact real pointwise product reconstruction for two realizable H³ states
on the Fourier Euclidean carrier. -/
theorem h3SpectralScalarRealC1Representative_weightedRawProductConvolutionL2_eq_mul_of_realizable
    (F G : H3SpectralScalarState)
    (hF : H3SpectralScalarRealizable F)
    (hG : H3SpectralScalarRealizable G)
    (x : H3FourierPoint3) :
    h3SpectralScalarRealC1Representative
        (h3WeightedRawProductConvolutionL2 F G)
        x
      =
    h3SpectralScalarRealC1Representative F x *
      h3SpectralScalarRealC1Representative G x := by
  exact
    h3SpectralScalarRealC1Representative_weightedRawProductConvolutionL2_eq_mul_of_im_eq_zero
      F G x
      (h3SpectralScalarC1Representative_im_eq_zero_of_realizable
        F hF x)
      (h3SpectralScalarC1Representative_im_eq_zero_of_realizable
        G hG x)

/-- Exact real pointwise product reconstruction transported to the project's
`Point3` carrier. -/
theorem h3SpectralScalarRealC1RepresentativeOnPoint3_weightedRawProductConvolutionL2_eq_mul_of_realizable
    (F G : H3SpectralScalarState)
    (hF : H3SpectralScalarRealizable F)
    (hG : H3SpectralScalarRealizable G)
    (x : Point3) :
    h3SpectralScalarRealC1RepresentativeOnPoint3
        (h3WeightedRawProductConvolutionL2 F G)
        x
      =
    h3SpectralScalarRealC1RepresentativeOnPoint3 F x *
      h3SpectralScalarRealC1RepresentativeOnPoint3 G x := by
  unfold h3SpectralScalarRealC1RepresentativeOnPoint3
  exact
    h3SpectralScalarRealC1Representative_weightedRawProductConvolutionL2_eq_mul_of_realizable
      F G hF hG
      ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)

/-- Functional form on `Point3`, useful for rewriting underneath
`spatial3.d`. -/
theorem h3SpectralScalarRealC1RepresentativeOnPoint3_weightedRawProductConvolutionL2_eq_mul_fun_of_realizable
    (F G : H3SpectralScalarState)
    (hF : H3SpectralScalarRealizable F)
    (hG : H3SpectralScalarRealizable G) :
    h3SpectralScalarRealC1RepresentativeOnPoint3
        (h3WeightedRawProductConvolutionL2 F G)
      =
    fun x : Point3 =>
      h3SpectralScalarRealC1RepresentativeOnPoint3 F x *
        h3SpectralScalarRealC1RepresentativeOnPoint3 G x := by
  funext x
  exact
    h3SpectralScalarRealC1RepresentativeOnPoint3_weightedRawProductConvolutionL2_eq_mul_of_realizable
      F G hF hG x

end

end Euclidean
end Bridge
end PrimeTensor
