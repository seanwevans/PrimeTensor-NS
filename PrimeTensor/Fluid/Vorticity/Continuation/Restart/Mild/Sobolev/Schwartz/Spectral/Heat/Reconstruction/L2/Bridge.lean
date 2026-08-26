import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Moment.Smoothing
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Spectral.Heat.Intertwining
import Mathlib.Analysis.Fourier.LpSpace

/-!
# Positive-time C³ reconstruction / L² decoder bridge

`SchwartzSpectralHeatMomentSmoothing` constructs, from a positive-time heat
smoothed weighted H³ state, an ordinary inverse-Fourier representative which
is spatially `C³`.

The existing spectral decoder, however, is defined through Mathlib's `L²`
Fourier isometry.  Before comparing the two inverse transforms pointwise, we
must first verify that they are fed by exactly the same deweighted Fourier
state.

This file closes that bookkeeping boundary.  The positive-time raw heat
representative is packaged in `L²`, identified exactly with the deweighted
spectral heat state, and the decoder is rewritten as the `L²` inverse Fourier
transform of that package.  We also record the corresponding tempered-
distribution identity.  Thus the remaining classicalization step is reduced
to the standard `L¹ ∩ L²` compatibility between the classical inverse Fourier
integral and the `L²` inverse Fourier transform.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform SchwartzMap
open scoped ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzHeatReconstructionL2Bridge
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Positive-time heat deweighting remains in `L²`. -/
theorem h3SpectralScalarHeatRawRepresentative_memLp2
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState) :
    MemLp
      (h3SpectralScalarHeatRawRepresentative ν t G)
      2
      (volume : Measure H3FourierPoint3) := by
  apply
    (h3SpectralScalarRawFourier_memLp2 G).of_le
      (h3SpectralScalarHeatRawRepresentative_aestronglyMeasurable ν t G)
  filter_upwards with ξ
  unfold h3SpectralScalarHeatRawRepresentative
  rw [norm_mul]
  calc
    ‖h3HeatFourierSymbol ν t ξ‖ * ‖h3SpectralScalarRawFourier G ξ‖
        ≤ 1 * ‖h3SpectralScalarRawFourier G ξ‖ :=
      mul_le_mul_of_nonneg_right
        (norm_h3HeatFourierSymbol_le_one hν.le ht.le ξ)
        (norm_nonneg _)
    _ = ‖h3SpectralScalarRawFourier G ξ‖ := by simp

/-- Canonical `L²` package of the positive-time raw heat representative. -/
noncomputable def h3SpectralScalarHeatRawRepresentativeL2
    (ν t : ℝ)
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState) :
    H3FourierComplexL2 :=
  (h3SpectralScalarHeatRawRepresentative_memLp2 hν ht G).toLp
    (h3SpectralScalarHeatRawRepresentative ν t G)

/-- The packaged positive-time raw heat state has the expected representative
almost everywhere. -/
theorem h3SpectralScalarHeatRawRepresentativeL2_ae
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState) :
    (h3SpectralScalarHeatRawRepresentativeL2 ν t hν ht G :
        H3FourierPoint3 → ℂ)
      =ᵐ[volume]
    h3SpectralScalarHeatRawRepresentative ν t G := by
  exact
    MemLp.coeFn_toLp
      (h3SpectralScalarHeatRawRepresentative_memLp2 hν ht G)

/--
The `L²` package of the explicit positive-time heat representative is exactly
what one obtains by first applying weighted spectral heat evolution and then
stripping the H³ weight.
-/
theorem h3SpectralScalarHeatRawRepresentativeL2_eq_rawFourierL2_heatApplyNN
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState) :
    h3SpectralScalarHeatRawRepresentativeL2 ν t hν ht G
      =
    h3SpectralScalarRawFourierL2
      (h3SpectralScalarHeatApplyNN
        ν hν.le (NNReal.mk t ht.le) G) := by
  rw [h3SpectralScalarRawFourierL2_heatApplyNN]
  apply MeasureTheory.Lp.ext
  filter_upwards [
    h3SpectralScalarHeatRawRepresentativeL2_ae hν ht G,
    h3HeatFrequencyApplyNN_coeFn
      ν hν.le (NNReal.mk t ht.le) (h3SpectralScalarRawFourierL2 G),
    h3SpectralScalarRawFourierL2_ae G
  ] with ξ hRep hHeat hRaw
  rw [hRep, hHeat, hRaw]
  rfl

/--
The existing complex `L²` decoder of the heat-evolved state is literally the
`L²` inverse Fourier transform of the explicit raw representative packaged
above.
-/
theorem h3SpectralScalarDecodeComplexL2_heatApplyNN_eq_fourierInv_rawRepresentativeL2
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState) :
    h3SpectralScalarDecodeComplexL2
        (h3SpectralScalarHeatApplyNN ν hν.le (NNReal.mk t ht.le) G)
      =
    (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ).symm
      (h3SpectralScalarHeatRawRepresentativeL2 ν t hν ht G) := by
  unfold h3SpectralScalarDecodeComplexL2
  rw [← h3SpectralScalarHeatRawRepresentativeL2_eq_rawFourierL2_heatApplyNN
        hν ht G]

/--
Tempered-distribution form of the same bridge.  This is useful for the final
`L¹ ∩ L²` compatibility argument because Mathlib already proves that the
`L²` inverse Fourier transform commutes with the embedding into tempered
distributions.
-/
theorem h3SpectralScalarDecodeComplexL2_heatApplyNN_toTemperedDistribution
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState) :
    (h3SpectralScalarDecodeComplexL2
        (h3SpectralScalarHeatApplyNN ν hν.le (NNReal.mk t ht.le) G) :
      𝓢'(H3FourierPoint3, ℂ))
      =
    FourierTransformInv.fourierInv
      (h3SpectralScalarHeatRawRepresentativeL2 ν t hν ht G :
        𝓢'(H3FourierPoint3, ℂ)) := by
  rw [
    h3SpectralScalarDecodeComplexL2_heatApplyNN_eq_fourierInv_rawRepresentativeL2
      hν ht G
  ]
  exact
    (MeasureTheory.Lp.fourierInv_toTemperedDistribution_eq
      (h3SpectralScalarHeatRawRepresentativeL2 ν t hν ht G)).symm

/-- Named `C³` representative of the same explicit raw heat amplitude. -/
noncomputable def h3SpectralScalarHeatC3Representative
    (ν t : ℝ)
    (G : H3SpectralScalarState) :
    H3FourierPoint3 → ℂ :=
  FourierTransformInv.fourierInv
    (h3SpectralScalarHeatRawRepresentative ν t G)

/-- The named positive-time reconstruction is spatially `C³`. -/
theorem h3SpectralScalarHeatC3Representative_contDiff_three
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState) :
    ContDiff ℝ 3
      (h3SpectralScalarHeatC3Representative ν t G) := by
  exact
    h3SpectralScalarHeatRawRepresentative_fourierInv_contDiff_three
      hν ht G

end

end Euclidean
end Bridge
end PrimeTensor
