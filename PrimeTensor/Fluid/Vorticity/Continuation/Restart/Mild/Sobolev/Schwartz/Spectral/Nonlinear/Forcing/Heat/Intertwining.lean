import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Heat.C3.Bridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Leray.Physical.Closure

/-!
# Exact intertwining for the positive-lag nonlinear forcing reconstruction

`SchwartzSpectralNonlinearForcingHeatC3Bridge` constructs a classical `C³`
inverse-Fourier representative from the explicit raw amplitude

    H_τ(ξ) · P(ξ) div(U ⊗ V)(ξ).

This file identifies that amplitude with the exact H³-deweighted Fourier
representative of the *existing* spectral heat--Leray velocity operator used
inside the Duhamel term.

The proof is purely algebraic after the representative theorems already in the
library:

* deweighting commutes with the heat-derivative multiplier;
* deweighting the bundled H³ product recovers the exact raw convolution;
* deweighting commutes with finite sums and with the finite Leray matrix.

Consequently the positive-lag `C³` reconstruction is not a parallel object: it
agrees almost everywhere with the existing complex physical decoder of the
actual spectral heat--Leray nonlinear kernel, coordinatewise and also after
transport to `Point3`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralNonlinearForcingHeatIntertwining
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3SchwartzSpectralNonlinearForcingHeatIntertwining :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Deweight one heat derivative of one exact H³ product -/

/-- After exact Sobolev deweighting, one heat derivative of the bundled H³
product has the expected raw representative. -/
theorem h3SpectralScalarHeatDerivative_weightedRawProduct_rawFourierL2_ae
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (j : Fin 3)
    (F G : H3SpectralScalarState) :
    ((h3SpectralScalarRawFourierL2
        (h3SpectralScalarHeatDerivativeApply
          ν τ hν hτ j
          (h3WeightedRawProductConvolutionL2 F G)) : H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      h3HeatDerivativeSymbol ν τ j ξ *
        h3RawProductConvolution F G ξ) := by
  rw [h3SpectralScalarRawFourierL2_heatDerivativeApply hν hτ j]
  filter_upwards [
    h3SpectralScalarHeatDerivativeApply_ae
      hν hτ j
      (h3SpectralScalarRawFourierL2
        (h3WeightedRawProductConvolutionL2 F G)),
    h3SpectralScalarRawFourierL2_weightedRawProductConvolutionL2_ae F G
  ] with ξ hDer hConv
  rw [hDer, hConv]

/-! ## Finite divergence -/

/-- Deweighting the actual finite pre-Leray heat-divergence operator gives
heat times the exact raw finite divergence. -/
theorem h3SpectralFinVelocityHeatDivergenceApply_rawFourierL2_ae
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    ((h3SpectralScalarRawFourierL2
        (h3SpectralFinVelocityHeatDivergenceApply
          ν τ hν hτ U V i) : H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      h3HeatFourierSymbol ν τ ξ *
        h3RawFinOuterProductDivergence U V i ξ) := by
  unfold h3SpectralFinVelocityHeatDivergenceApply
  unfold h3SpectralFinTensorHeatDivergenceApply
  rw [h3SpectralScalarRawFourierL2_sum]

  have hSum :=
    MeasureTheory.Lp.coeFn_finsetSum
      (Finset.univ : Finset (Fin 3))
      (fun j : Fin 3 =>
        h3SpectralScalarRawFourierL2
          (h3SpectralScalarHeatDerivativeApply
            ν τ hν hτ j
            (h3SpectralFinOuterProduct U V i j)))

  have hTerms :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        ∀ j : Fin 3,
          ((h3SpectralScalarRawFourierL2
              (h3SpectralScalarHeatDerivativeApply
                ν τ hν hτ j
                (h3SpectralFinOuterProduct U V i j)) : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ
            =
          h3HeatDerivativeSymbol ν τ j ξ *
            h3RawProductConvolution (U i) (V j) ξ := by
    exact ae_all_iff.2 (fun j => by
      change
        ((h3SpectralScalarRawFourierL2
            (h3SpectralScalarHeatDerivativeApply
              ν τ hν hτ j
              (h3WeightedRawProductConvolutionL2 (U i) (V j))) :
            H3FourierComplexL2) : H3FourierPoint3 → ℂ)
          =ᵐ[(volume : Measure H3FourierPoint3)]
        (fun ξ : H3FourierPoint3 =>
          h3HeatDerivativeSymbol ν τ j ξ *
            h3RawProductConvolution (U i) (V j) ξ)
      exact
        h3SpectralScalarHeatDerivative_weightedRawProduct_rawFourierL2_ae
          hν hτ j (U i) (V j))

  filter_upwards [hSum, hTerms] with ξ hSumξ hTermsξ
  rw [hSumξ]
  simp only [Finset.sum_apply]
  unfold h3RawFinOuterProductDivergence
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [hTermsξ j]
  unfold h3HeatDerivativeSymbol
  ring

/-! ## Full Leray kernel -/

/-- The exact deweighted Fourier `L²` state of the existing positive-lag
heat--Leray velocity operator is the packaged explicit raw heat-forcing
amplitude. -/
theorem h3SpectralFinHeatLerayVelocityApply_rawFourierL2_eq_rawHeatForcingL2
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    h3SpectralScalarRawFourierL2
        (h3SpectralFinHeatLerayVelocityApply
          ν τ hν hτ U V i)
      =
    h3RawFinLerayOuterProductDivergenceHeatFourierL2
      ν τ hν hτ U V i := by
  unfold h3SpectralFinHeatLerayVelocityApply
  rw [h3SpectralFinLerayApply_rawFourierL2_apply]
  unfold h3SpectralFinLerayApply

  apply MeasureTheory.Lp.ext

  have hSum :=
    MeasureTheory.Lp.coeFn_finsetSum
      (Finset.univ : Finset (Fin 3))
      (fun k : Fin 3 =>
        h3SpectralScalarLerayCoefficientApply
          i k
          (h3SpectralScalarRawFourierL2
            (h3SpectralFinVelocityHeatDivergenceApply
              ν τ hν hτ U V k)))

  have hLeray :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        ∀ k : Fin 3,
          ((h3SpectralScalarLerayCoefficientApply
              i k
              (h3SpectralScalarRawFourierL2
                (h3SpectralFinVelocityHeatDivergenceApply
                  ν τ hν hτ U V k)) : H3SpectralScalarState) :
            H3FourierPoint3 → ℂ) ξ
            =
          h3LerayCoefficient ξ i k *
            ((h3SpectralScalarRawFourierL2
                (h3SpectralFinVelocityHeatDivergenceApply
                  ν τ hν hτ U V k) : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ := by
    exact ae_all_iff.2 (fun k =>
      h3SpectralScalarLerayCoefficientApply_ae
        i k
        (h3SpectralScalarRawFourierL2
          (h3SpectralFinVelocityHeatDivergenceApply
            ν τ hν hτ U V k)))

  have hPre :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        ∀ k : Fin 3,
          ((h3SpectralScalarRawFourierL2
              (h3SpectralFinVelocityHeatDivergenceApply
                ν τ hν hτ U V k) : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ
            =
          h3HeatFourierSymbol ν τ ξ *
            h3RawFinOuterProductDivergence U V k ξ := by
    exact ae_all_iff.2 (fun k =>
      h3SpectralFinVelocityHeatDivergenceApply_rawFourierL2_ae
        hν hτ U V k)

  have hRaw :
      ((h3RawFinLerayOuterProductDivergenceHeatFourierL2
          ν τ hν hτ U V i : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      h3RawFinLerayOuterProductDivergenceHeatRepresentative
        ν τ U V i := by
    unfold h3RawFinLerayOuterProductDivergenceHeatFourierL2
    exact
      MemLp.coeFn_toLp
        (h3RawFinLerayOuterProductDivergenceHeatRepresentative_memLp2
          hν hτ U V i)

  filter_upwards [hSum, hLeray, hPre, hRaw] with
      ξ hSumξ hLerayξ hPreξ hRawξ

  rw [hSumξ, hRawξ]
  simp only [Finset.sum_apply]
  unfold h3RawFinLerayOuterProductDivergenceHeatRepresentative
  unfold h3RawFinLerayOuterProductDivergence
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k hk
  rw [hLerayξ k, hPreξ k]
  ring

/-! ## The classical representative is the existing decoder -/

/-- The fixed-lag classical `C³` reconstruction agrees almost everywhere with
the existing complex physical decoder of the actual spectral heat--Leray
velocity kernel. -/
theorem h3RawFinLerayOuterProductDivergenceHeatC3Representative_ae_eq_heatLerayDecodeComplexL2
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    h3RawFinLerayOuterProductDivergenceHeatC3Representative
        ν τ U V i
      =ᵐ[(volume : Measure H3FourierPoint3)]
    ((h3SpectralScalarDecodeComplexL2
        (h3SpectralFinHeatLerayVelocityApply
          ν τ hν hτ U V i) : H3ComplexPhysicalScalarL2) :
      H3FourierPoint3 → ℂ) := by
  have hC3 :=
    h3RawFinLerayOuterProductDivergenceHeatC3Representative_ae_eq_physicalL2
      hν hτ U V i
  have hEq :=
    h3SpectralFinHeatLerayVelocityApply_rawFourierL2_eq_rawHeatForcingL2
      hν hτ U V i
  unfold h3RawFinLerayOuterProductDivergenceHeatPhysicalL2 at hC3
  unfold h3SpectralScalarDecodeComplexL2
  rw [hEq]
  exact hC3

/-- The same decoder compatibility after transport to the project's spatial
carrier `Point3`. -/
theorem h3RawFinLerayOuterProductDivergenceHeatC3RepresentativeOnPoint3_ae_eq_heatLerayDecodeComplexL2
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    h3RawFinLerayOuterProductDivergenceHeatC3RepresentativeOnPoint3
        ν τ U V i
      =ᵐ[(volume : Measure Point3)]
    (fun x : Point3 =>
      ((h3SpectralScalarDecodeComplexL2
          (h3SpectralFinHeatLerayVelocityApply
            ν τ hν hτ U V i) : H3ComplexPhysicalScalarL2) :
        H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)) := by
  exact
    (PiLp.volume_preserving_toLp
      (PrimeTensor.Axis Depth.three)).quasiMeasurePreserving.ae_eq_comp
        (h3RawFinLerayOuterProductDivergenceHeatC3Representative_ae_eq_heatLerayDecodeComplexL2
          hν hτ U V i)

end

end Euclidean
end Bridge
end PrimeTensor
