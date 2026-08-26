import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Spectral.Decoder
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Spectral.Encoder

/-!
# Encoder/decoder round trip on genuine H³ velocity snapshots

The complex spectral decoder is defined on every weighted spectral state.  This
file identifies its action on the concrete range of the existing H³ spectral
encoder.

For an encoded velocity component

    G = W₃ * û,

deweighting cancels the strictly positive H³ weight exactly, so the raw `L²`
Fourier state is the original zeroth-order Fourier component.  Applying the
inverse `L²` Fourier isometry therefore recovers precisely the complexification
of the transported real `L²` velocity component.

No reality-preservation claim for an arbitrary spectral Picard iterate is made
here.  Instead this establishes the exact range theorem needed to formulate
that invariant cleanly in the next layer.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform Filter
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3SpectralRoundTrip
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Exact cancellation of the H³ weight -/

/-- The reciprocal spectral H³ weight cancels the weight exactly. -/
@[simp]
theorem h3SobolevFrequencyWeightInvComplex_mul_weight
    (ξ : H3FourierPoint3) :
    h3SobolevFrequencyWeightInvComplex ξ *
        (h3SobolevFrequencyWeight ξ : ℂ)
      = 1 := by
  have hW : h3SobolevFrequencyWeight ξ ≠ 0 :=
    ne_of_gt (h3SobolevFrequencyWeight_pos ξ)
  simp [
    h3SobolevFrequencyWeightInvComplex,
    h3SobolevFrequencyWeightInv,
    hW
  ]

/-- Deweighting a genuinely encoded scalar component recovers its original
zeroth-order Fourier `L²` state exactly. -/
theorem h3SpectralScalarRawFourierL2_velocityH3SpectralScalarAt_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j : Fin 3) :
    h3SpectralScalarRawFourierL2
        (velocityH3SpectralScalarAt u t hInt hMeas hFourier j)
      =
    velocityH3BaseFourierAt u t hInt hMeas j := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    h3SpectralScalarRawFourierL2_ae
      (velocityH3SpectralScalarAt u t hInt hMeas hFourier j),
    velocityH3SpectralScalarAt_ae hFourier j
  ] with ξ hRaw hEncoded
  rw [hRaw]
  unfold h3SpectralScalarRawFourier
  rw [hEncoded]
  unfold velocityH3WeightedBaseFourierRaw
  rw [← mul_assoc, h3SobolevFrequencyWeightInvComplex_mul_weight, one_mul]

/-! ## Exact inverse-Fourier round trip -/

/-- Decoding an encoded scalar component recovers exactly the complexification
of the transported real zeroth-order velocity component. -/
theorem h3SpectralScalarDecodeComplexL2_velocityH3SpectralScalarAt_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j : Fin 3) :
    h3SpectralScalarDecodeComplexL2
        (velocityH3SpectralScalarAt u t hInt hMeas hFourier j)
      =
    h3ComplexifyFourierL2
      (h3ToFourierRealL2
        (velocityH3L2JetAt u t hInt hMeas (h3JetSlot0 j))) := by
  apply
    (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ).injective
  rw [h3Fourier_h3SpectralScalarDecodeComplexL2]
  rw [
    h3SpectralScalarRawFourierL2_velocityH3SpectralScalarAt_eq
      hFourier j
  ]
  rfl

/-- Taking the real part after decoding an encoded component loses nothing: it
is exactly the transported real zeroth-order velocity component. -/
theorem h3RealPartFourierL2_h3SpectralScalarDecodeComplexL2_velocityH3SpectralScalarAt_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j : Fin 3) :
    h3RealPartFourierL2
      (h3SpectralScalarDecodeComplexL2
        (velocityH3SpectralScalarAt u t hInt hMeas hFourier j))
      =
    h3ToFourierRealL2
      (velocityH3L2JetAt u t hInt hMeas (h3JetSlot0 j)) := by
  rw [
    h3SpectralScalarDecodeComplexL2_velocityH3SpectralScalarAt_eq
      hFourier j
  ]
  exact h3RealPartFourierL2_complexify_eq _

/-! ## Velocity-state packaging -/

/-- Real Fourier-carrier projection of the decoded spectral velocity.  This is
defined for every spectral state; on the encoder range it is an exact inverse
by the theorem below. -/
noncomputable def h3SpectralVelocityDecodeRealFourierL2
    (U : H3SpectralVelocityState) :
    Fin 3 → H3FourierRealL2 :=
  fun j =>
    h3RealPartFourierL2
      (h3SpectralVelocityDecodeComplexL2 U j)

@[simp]
theorem h3SpectralVelocityDecodeRealFourierL2_apply
    (U : H3SpectralVelocityState)
    (j : Fin 3) :
    h3SpectralVelocityDecodeRealFourierL2 U j
      =
    h3RealPartFourierL2
      (h3SpectralScalarDecodeComplexL2 (U j)) :=
  rfl

/-- Coordinatewise encode/decode round trip for a genuine H³ velocity
snapshot. -/
theorem h3SpectralVelocityDecodeRealFourierL2_velocityH3SpectralStateAt_apply_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j : Fin 3) :
    h3SpectralVelocityDecodeRealFourierL2
        (velocityH3SpectralStateAt u t hInt hMeas hFourier) j
      =
    h3ToFourierRealL2
      (velocityH3L2JetAt u t hInt hMeas (h3JetSlot0 j)) := by
  change
    h3RealPartFourierL2
      (h3SpectralScalarDecodeComplexL2
        (velocityH3SpectralScalarAt u t hInt hMeas hFourier j))
      = _
  exact
    h3RealPartFourierL2_h3SpectralScalarDecodeComplexL2_velocityH3SpectralScalarAt_eq
      hFourier j

end

end Euclidean
end Bridge
end PrimeTensor
