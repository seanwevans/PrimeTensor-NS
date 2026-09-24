import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Canonical.Vorticity.Fourier
import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Multiplier.Localized.Smooth
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Spectral.Round.Trip
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.H3.Real.C1.F.Deriv.Coordinate.Bound

/-!
# BKM endpoint: canonical curl amplitudes are integrable

The physical-vorticity/Fourier-curl bridge identifies the three canonical curl
amplitudes with Fourier transforms of the physical vorticity `L²` packages.
For the physical convolution identity we need one stronger fact: the canonical
curl amplitudes themselves are ordinary `L¹` Fourier functions.

That follows from the full H³ spectral encoder.  For each velocity component,
the encoded weighted H³ state has an integrable raw first Fourier derivative.
The encoder/decoder round trip identifies its raw Fourier representative with
the canonical base Fourier field almost everywhere.  Therefore each canonical
curl is almost everywhere a difference of two integrable raw derivative
functions.

We also prove that multiplication by any localized BKM coordinate multiplier
preserves this `L¹` property.  The localized symbol has pointwise norm at most
one, so the product is directly dominated by the already-integrable curl.

These are the precise absolute-integrability inputs needed for the next
inverse-Fourier/Fubini convolution bridge.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointCanonicalCurlIntegrable
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/--
The canonical base Fourier representative agrees almost everywhere with the
ordinary raw Fourier representative of its encoded weighted H³ state.
-/
theorem velocityH3BaseFourierAt_ae_eq_spectralRawFourier
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j : Fin 3) :
    (velocityH3BaseFourierAt
        u t hInt hMeas j :
        H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3SpectralScalarRawFourier
      (velocityH3SpectralScalarAt
        u t hInt hMeas hFourier j) := by

  let G : H3SpectralScalarState :=
    velocityH3SpectralScalarAt
      u t hInt hMeas hFourier j

  have hRaw :
      (h3SpectralScalarRawFourierL2 G :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      h3SpectralScalarRawFourier G :=
    h3SpectralScalarRawFourierL2_ae G

  have hRound :
      h3SpectralScalarRawFourierL2 G
        =
      velocityH3BaseFourierAt
        u t hInt hMeas j := by
    dsimp only [G]
    exact
      h3SpectralScalarRawFourierL2_velocityH3SpectralScalarAt_eq
        hFourier j

  rw [hRound] at hRaw

  simpa only [G] using hRaw

/-- The canonical `C01` curl amplitude belongs to ordinary Fourier `L¹`. -/
theorem h3BKMCanonicalCurl01Amplitude_integrable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    Integrable
      (h3BKMCanonicalCurl01Amplitude hInt hMeas)
      (volume : Measure H3FourierPoint3) := by

  let G0 : H3SpectralScalarState :=
    velocityH3SpectralScalarAt
      u t hInt hMeas hFourier 0

  let G1 : H3SpectralScalarState :=
    velocityH3SpectralScalarAt
      u t hInt hMeas hFourier 1

  have hBase0 :=
    velocityH3BaseFourierAt_ae_eq_spectralRawFourier
      hFourier (0 : Fin 3)

  have hBase1 :=
    velocityH3BaseFourierAt_ae_eq_spectralRawFourier
      hFourier (1 : Fin 3)

  have hModel :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3SpectralScalarRawFourierCoordinateDerivative
              G0 (1 : Fin 3) ξ
            -
          h3SpectralScalarRawFourierCoordinateDerivative
              G1 (0 : Fin 3) ξ)
        (volume : Measure H3FourierPoint3) :=
    (h3SpectralScalarRawFourierCoordinateDerivative_integrable
      G0 (1 : Fin 3)).sub
      (h3SpectralScalarRawFourierCoordinateDerivative_integrable
        G1 (0 : Fin 3))

  apply Integrable.congr hModel

  filter_upwards [hBase0, hBase1] with ξ h0 h1

  unfold
    h3BKMCanonicalCurl01Amplitude
    h3BKMCurl01Amplitude
    h3SpectralScalarRawFourierCoordinateDerivative

  simp only [G0, G1]

  rw [← h0, ← h1]

/-- The canonical `C02` curl amplitude belongs to ordinary Fourier `L¹`. -/
theorem h3BKMCanonicalCurl02Amplitude_integrable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    Integrable
      (h3BKMCanonicalCurl02Amplitude hInt hMeas)
      (volume : Measure H3FourierPoint3) := by

  let G0 : H3SpectralScalarState :=
    velocityH3SpectralScalarAt
      u t hInt hMeas hFourier 0

  let G2 : H3SpectralScalarState :=
    velocityH3SpectralScalarAt
      u t hInt hMeas hFourier 2

  have hBase0 :=
    velocityH3BaseFourierAt_ae_eq_spectralRawFourier
      hFourier (0 : Fin 3)

  have hBase2 :=
    velocityH3BaseFourierAt_ae_eq_spectralRawFourier
      hFourier (2 : Fin 3)

  have hModel :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3SpectralScalarRawFourierCoordinateDerivative
              G0 (2 : Fin 3) ξ
            -
          h3SpectralScalarRawFourierCoordinateDerivative
              G2 (0 : Fin 3) ξ)
        (volume : Measure H3FourierPoint3) :=
    (h3SpectralScalarRawFourierCoordinateDerivative_integrable
      G0 (2 : Fin 3)).sub
      (h3SpectralScalarRawFourierCoordinateDerivative_integrable
        G2 (0 : Fin 3))

  apply Integrable.congr hModel

  filter_upwards [hBase0, hBase2] with ξ h0 h2

  unfold
    h3BKMCanonicalCurl02Amplitude
    h3BKMCurl02Amplitude
    h3SpectralScalarRawFourierCoordinateDerivative

  simp only [G0, G2]

  rw [← h0, ← h2]

/-- The canonical `C12` curl amplitude belongs to ordinary Fourier `L¹`. -/
theorem h3BKMCanonicalCurl12Amplitude_integrable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    Integrable
      (h3BKMCanonicalCurl12Amplitude hInt hMeas)
      (volume : Measure H3FourierPoint3) := by

  let G1 : H3SpectralScalarState :=
    velocityH3SpectralScalarAt
      u t hInt hMeas hFourier 1

  let G2 : H3SpectralScalarState :=
    velocityH3SpectralScalarAt
      u t hInt hMeas hFourier 2

  have hBase1 :=
    velocityH3BaseFourierAt_ae_eq_spectralRawFourier
      hFourier (1 : Fin 3)

  have hBase2 :=
    velocityH3BaseFourierAt_ae_eq_spectralRawFourier
      hFourier (2 : Fin 3)

  have hModel :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3SpectralScalarRawFourierCoordinateDerivative
              G1 (2 : Fin 3) ξ
            -
          h3SpectralScalarRawFourierCoordinateDerivative
              G2 (1 : Fin 3) ξ)
        (volume : Measure H3FourierPoint3) :=
    (h3SpectralScalarRawFourierCoordinateDerivative_integrable
      G1 (2 : Fin 3)).sub
      (h3SpectralScalarRawFourierCoordinateDerivative_integrable
        G2 (1 : Fin 3))

  apply Integrable.congr hModel

  filter_upwards [hBase1, hBase2] with ξ h1 h2

  unfold
    h3BKMCanonicalCurl12Amplitude
    h3BKMCurl12Amplitude
    h3SpectralScalarRawFourierCoordinateDerivative

  simp only [G1, G2]

  rw [← h1, ← h2]

/--
Multiplying an integrable scalar Fourier field by a localized BKM coordinate
multiplier preserves integrability.
-/
theorem h3BKMLocalizedCoordinateMultiplier_mul_integrable
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3)
    {f : H3FourierPoint3 → ℂ}
    (hf : Integrable f
      (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3BKMLocalizedCoordinateMultiplier
            R hR i k ξ
          *
        f ξ)
      (volume : Measure H3FourierPoint3) := by

  have hMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3BKMLocalizedCoordinateMultiplier
              R hR i k ξ
            *
          f ξ)
        (volume : Measure H3FourierPoint3) := by
    exact
      (h3BKMLocalizedCoordinateMultiplier_contDiff
        hR i k).continuous.aestronglyMeasurable.mul
          hf.aestronglyMeasurable

  refine Integrable.mono' hf.norm hMeas ?_

  filter_upwards with ξ

  rw [norm_mul]

  calc
    ‖h3BKMLocalizedCoordinateMultiplier
        R hR i k ξ‖ * ‖f ξ‖
        ≤
      1 * ‖f ξ‖ := by
        exact
          mul_le_mul_of_nonneg_right
            (norm_h3BKMLocalizedCoordinateMultiplier_le_one
              hR i k ξ)
            (norm_nonneg _)

    _ = ‖f ξ‖ := by
      rw [one_mul]

/-- Localized `C01` multiplier products are ordinary Fourier `L¹`. -/
theorem h3BKMLocalizedCoordinateMultiplier_mul_canonicalCurl01_integrable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3BKMLocalizedCoordinateMultiplier
            R hR i k ξ
          *
        h3BKMCanonicalCurl01Amplitude
          hInt hMeas ξ)
      (volume : Measure H3FourierPoint3) :=
  h3BKMLocalizedCoordinateMultiplier_mul_integrable
    hR i k
    (h3BKMCanonicalCurl01Amplitude_integrable hFourier)

/-- Localized `C02` multiplier products are ordinary Fourier `L¹`. -/
theorem h3BKMLocalizedCoordinateMultiplier_mul_canonicalCurl02_integrable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3BKMLocalizedCoordinateMultiplier
            R hR i k ξ
          *
        h3BKMCanonicalCurl02Amplitude
          hInt hMeas ξ)
      (volume : Measure H3FourierPoint3) :=
  h3BKMLocalizedCoordinateMultiplier_mul_integrable
    hR i k
    (h3BKMCanonicalCurl02Amplitude_integrable hFourier)

/-- Localized `C12` multiplier products are ordinary Fourier `L¹`. -/
theorem h3BKMLocalizedCoordinateMultiplier_mul_canonicalCurl12_integrable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3BKMLocalizedCoordinateMultiplier
            R hR i k ξ
          *
        h3BKMCanonicalCurl12Amplitude
          hInt hMeas ξ)
      (volume : Measure H3FourierPoint3) :=
  h3BKMLocalizedCoordinateMultiplier_mul_integrable
    hR i k
    (h3BKMCanonicalCurl12Amplitude_integrable hFourier)

end

end Euclidean
end Bridge
end PrimeTensor
