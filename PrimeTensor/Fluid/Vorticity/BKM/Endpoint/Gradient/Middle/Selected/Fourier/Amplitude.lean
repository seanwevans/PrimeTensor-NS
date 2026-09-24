import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Gradient.Selected.Model.Bound
import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Gradient.Middle.Localized.Fourier

/-!
# BKM endpoint: selected middle Fourier amplitude

The selected middle physical proxy has already been packaged pointwise and
identified almost everywhere with the corresponding finite middle `L²` state.

This file now packages the spectral side of that same object.

For an arbitrary target velocity component `j`, define the selected middle
inverse `L²` state and take its unitary `L²` Fourier transform.  Its chosen
representative is the canonical selected middle Fourier amplitude.

The existing componentwise middle-Fourier theorem then shows that this
amplitude agrees almost everywhere with the explicit finite shell sum.  Combining
that with the exact low/middle/high trichotomy and the canonical raw-Fourier
representative gives

    middle
      = raw derivative - low - high

almost everywhere.

Consequently the selected middle amplitude is ordinary Fourier `L¹` and `L²`.
This is exactly the input needed by the next inverse-Fourier reconstruction
checkpoint.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointSelectedMiddleGradientFourierAmplitude
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Selected middle `L²` state -/

/--
Selected finite-middle inverse `L²` state for an arbitrary target component.
-/
noncomputable def h3BKMSelectedMiddleGradientInverseL2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (A : ℝ)
    (j i : Fin 3) :
    H3FourierComplexL2 :=
  ![
    h3BKMMiddleLocalizedGradientComponent0InverseL2
      hFourier 0 (h3BKMUpperCutoffIndex A) i,
    h3BKMMiddleLocalizedGradientComponent1InverseL2
      hFourier 0 (h3BKMUpperCutoffIndex A) i,
    h3BKMMiddleLocalizedGradientComponent2InverseL2
      hFourier 0 (h3BKMUpperCutoffIndex A) i
  ] j

/--
The selected middle `L²` state represents the canonical selected physical
middle-gradient proxy almost everywhere on `Point3`.
-/
theorem h3BKMSelectedMiddleGradientInverseL2_ae_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (hEnvelope : VorticityEnvelope u g t)
    (A : ℝ)
    (j i : Fin 3) :
    (fun x : Point3 =>
      (h3BKMSelectedMiddleGradientInverseL2
          hFourier A j i :
          H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x))
      =ᵐ[(volume : Measure Point3)]
    h3BKMSelectedMiddleGradient u t A j i := by

  fin_cases j

  · change
      (fun x : Point3 =>
        (h3BKMMiddleLocalizedGradientComponent0InverseL2
            hFourier 0 (h3BKMUpperCutoffIndex A) i :
            H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x))
        =ᵐ[(volume : Measure Point3)]
      (h3BKMSelectedMiddleGradientComponent0 u t A i)

    exact
      h3BKMSelectedMiddleGradientComponent0_ae_eq
        hInt hMeas hFourier hEnvelope A i

  · change
      (fun x : Point3 =>
        (h3BKMMiddleLocalizedGradientComponent1InverseL2
            hFourier 0 (h3BKMUpperCutoffIndex A) i :
            H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x))
        =ᵐ[(volume : Measure Point3)]
      (h3BKMSelectedMiddleGradientComponent1 u t A i)

    exact
      h3BKMSelectedMiddleGradientComponent1_ae_eq
        hInt hMeas hFourier hEnvelope A i

  · change
      (fun x : Point3 =>
        (h3BKMMiddleLocalizedGradientComponent2InverseL2
            hFourier 0 (h3BKMUpperCutoffIndex A) i :
            H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x))
        =ᵐ[(volume : Measure Point3)]
      (h3BKMSelectedMiddleGradientComponent2 u t A i)

    exact
      h3BKMSelectedMiddleGradientComponent2_ae_eq
        hInt hMeas hFourier hEnvelope A i

/-! ## Canonical selected middle Fourier amplitude -/

/--
Chosen pointwise representative of the unitary Fourier transform of the
selected middle inverse `L²` state.
-/
noncomputable def h3BKMSelectedMiddleGradientFourierAmplitude
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (A : ℝ)
    (j i : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  (((MeasureTheory.Lp.fourierTransformₗᵢ
      H3FourierPoint3 ℂ)
    (h3BKMSelectedMiddleGradientInverseL2
      hFourier A j i) :
      H3FourierComplexL2) :
    H3FourierPoint3 → ℂ) ξ

/--
The canonical selected middle Fourier amplitude is represented almost
everywhere by the explicit finite dyadic shell sum.
-/
theorem h3BKMSelectedMiddleGradientFourierAmplitude_ae_eq_shellSum
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (A : ℝ)
    (j i : Fin 3) :
    h3BKMSelectedMiddleGradientFourierAmplitude
        hFourier A j i
      =ᵐ[(volume : Measure H3FourierPoint3)]
    fun ξ : H3FourierPoint3 =>
      ∑ n ∈ Finset.Icc 0 (h3BKMUpperCutoffIndex A),
        (h3BKMFrequencyShell
            (h3BKMDyadicRadius n)
            (h3BKMDyadicRadius_pos n)
            ξ : ℂ)
          *
        (h3FourierDerivativeSymbol i ξ
          *
        velocityH3BaseFourierAt
          u t hInt hMeas j ξ) := by

  fin_cases j

  · change
      (((MeasureTheory.Lp.fourierTransformₗᵢ
          H3FourierPoint3 ℂ)
        (h3BKMMiddleLocalizedGradientComponent0InverseL2
          hFourier 0 (h3BKMUpperCutoffIndex A) i) :
          H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      fun ξ : H3FourierPoint3 =>
        ∑ n ∈ Finset.Icc 0 (h3BKMUpperCutoffIndex A),
          (h3BKMFrequencyShell
              (h3BKMDyadicRadius n)
              (h3BKMDyadicRadius_pos n)
              ξ : ℂ)
            *
          (h3FourierDerivativeSymbol i ξ
            *
          velocityH3BaseFourierAt
            u t hInt hMeas 0 ξ)

    exact
      h3BKMMiddleLocalizedGradientComponent0InverseL2_fourier_ae
        hNS ht hFourier
        0
        (h3BKMUpperCutoffIndex A)
        i

  · change
      (((MeasureTheory.Lp.fourierTransformₗᵢ
          H3FourierPoint3 ℂ)
        (h3BKMMiddleLocalizedGradientComponent1InverseL2
          hFourier 0 (h3BKMUpperCutoffIndex A) i) :
          H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      fun ξ : H3FourierPoint3 =>
        ∑ n ∈ Finset.Icc 0 (h3BKMUpperCutoffIndex A),
          (h3BKMFrequencyShell
              (h3BKMDyadicRadius n)
              (h3BKMDyadicRadius_pos n)
              ξ : ℂ)
            *
          (h3FourierDerivativeSymbol i ξ
            *
          velocityH3BaseFourierAt
            u t hInt hMeas 1 ξ)

    exact
      h3BKMMiddleLocalizedGradientComponent1InverseL2_fourier_ae
        hNS ht hFourier
        0
        (h3BKMUpperCutoffIndex A)
        i

  · change
      (((MeasureTheory.Lp.fourierTransformₗᵢ
          H3FourierPoint3 ℂ)
        (h3BKMMiddleLocalizedGradientComponent2InverseL2
          hFourier 0 (h3BKMUpperCutoffIndex A) i) :
          H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      fun ξ : H3FourierPoint3 =>
        ∑ n ∈ Finset.Icc 0 (h3BKMUpperCutoffIndex A),
          (h3BKMFrequencyShell
              (h3BKMDyadicRadius n)
              (h3BKMDyadicRadius_pos n)
              ξ : ℂ)
            *
          (h3FourierDerivativeSymbol i ξ
            *
          velocityH3BaseFourierAt
            u t hInt hMeas 2 ξ)

    exact
      h3BKMMiddleLocalizedGradientComponent2InverseL2_fourier_ae
        hNS ht hFourier
        0
        (h3BKMUpperCutoffIndex A)
        i

/-! ## Exact a.e. trichotomy in raw-H³ variables -/

/--
After replacing the canonical base Fourier representative by the ordinary raw
Fourier representative of the encoded H³ state, the selected middle amplitude
is exactly `raw derivative - low - high` almost everywhere.
-/
theorem h3BKMSelectedMiddleGradientFourierAmplitude_ae_eq_raw_sub_low_sub_high
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (A : ℝ)
    (j i : Fin 3) :
    h3BKMSelectedMiddleGradientFourierAmplitude
        hFourier A j i
      =ᵐ[(volume : Measure H3FourierPoint3)]
    fun ξ : H3FourierPoint3 =>
      h3SpectralScalarRawFourierCoordinateDerivative
          (velocityH3SpectralScalarAt
            u t hInt hMeas hFourier j)
          i ξ
        -
      h3BKMLowGradientAmplitude
          0
          (velocityH3SpectralScalarAt
            u t hInt hMeas hFourier j)
          i ξ
        -
      h3BKMHighGradientAmplitude
          (h3BKMUpperCutoffIndex A)
          (velocityH3SpectralScalarAt
            u t hInt hMeas hFourier j)
          i ξ := by

  let G : H3SpectralScalarState :=
    velocityH3SpectralScalarAt
      u t hInt hMeas hFourier j

  have hMiddle :=
    h3BKMSelectedMiddleGradientFourierAmplitude_ae_eq_shellSum
      hNS ht hFourier A j i

  have hBase :=
    velocityH3BaseFourierAt_ae_eq_spectralRawFourier
      hFourier j

  filter_upwards [hMiddle, hBase] with ξ hMiddleξ hBaseξ

  have hTri :=
    velocityH3BaseFourier_gradient_frequencyTrichotomy_sum
      (u := u)
      (t := t)
      (hInt := hInt)
      (hMeas := hMeas)
      (lo := 0)
      (hi := h3BKMUpperCutoffIndex A)
      (Nat.zero_le (h3BKMUpperCutoffIndex A))
      i j ξ

  rw [hBaseξ] at hTri
  rw [hMiddleξ]
  rw [hBaseξ]

  change
    (∑ n ∈ Finset.Icc 0 (h3BKMUpperCutoffIndex A),
        (h3BKMFrequencyShell
            (h3BKMDyadicRadius n)
            (h3BKMDyadicRadius_pos n)
            ξ : ℂ)
          *
        (h3FourierDerivativeSymbol i ξ
          *
        h3SpectralScalarRawFourier G ξ))
      =
    h3SpectralScalarRawFourierCoordinateDerivative G i ξ
      -
    h3BKMLowGradientAmplitude 0 G i ξ
      -
    h3BKMHighGradientAmplitude
      (h3BKMUpperCutoffIndex A) G i ξ

  unfold
    h3SpectralScalarRawFourierCoordinateDerivative
    h3BKMLowGradientAmplitude
    h3BKMHighGradientAmplitude

  dsimp only [G] at hTri ⊢

  apply (eq_sub_iff_add_eq).2
  apply (eq_sub_iff_add_eq).2

  calc
    (∑ n ∈ Finset.Icc 0 (h3BKMUpperCutoffIndex A),
        (h3BKMFrequencyShell
            (h3BKMDyadicRadius n)
            (h3BKMDyadicRadius_pos n)
            ξ : ℂ)
          *
        (h3FourierDerivativeSymbol i ξ
          *
        h3SpectralScalarRawFourier
          (velocityH3SpectralScalarAt
            u t hInt hMeas hFourier j) ξ))
        +
      (h3BKMDyadicHighFrequencyFactor
          (h3BKMUpperCutoffIndex A) ξ : ℂ)
        *
      (h3FourierDerivativeSymbol i ξ
        *
      h3SpectralScalarRawFourier
        (velocityH3SpectralScalarAt
          u t hInt hMeas hFourier j) ξ)
        +
      (h3BKMDyadicLowFrequencyFactor 0 ξ : ℂ)
        *
      (h3FourierDerivativeSymbol i ξ
        *
      h3SpectralScalarRawFourier
        (velocityH3SpectralScalarAt
          u t hInt hMeas hFourier j) ξ)
        =
      (h3BKMDyadicLowFrequencyFactor 0 ξ : ℂ)
        *
      (h3FourierDerivativeSymbol i ξ
        *
      h3SpectralScalarRawFourier
        (velocityH3SpectralScalarAt
          u t hInt hMeas hFourier j) ξ)
        +
      (∑ n ∈ Finset.Icc 0 (h3BKMUpperCutoffIndex A),
        (h3BKMFrequencyShell
            (h3BKMDyadicRadius n)
            (h3BKMDyadicRadius_pos n)
            ξ : ℂ)
          *
        (h3FourierDerivativeSymbol i ξ
          *
        h3SpectralScalarRawFourier
          (velocityH3SpectralScalarAt
            u t hInt hMeas hFourier j) ξ))
        +
      (h3BKMDyadicHighFrequencyFactor
          (h3BKMUpperCutoffIndex A) ξ : ℂ)
        *
      (h3FourierDerivativeSymbol i ξ
        *
      h3SpectralScalarRawFourier
        (velocityH3SpectralScalarAt
          u t hInt hMeas hFourier j) ξ) := by
      abel

    _ =
      h3FourierDerivativeSymbol i ξ
        *
      h3SpectralScalarRawFourier
        (velocityH3SpectralScalarAt
          u t hInt hMeas hFourier j) ξ :=
      hTri.symm

/-! ## Ordinary `L¹ ∩ L²` membership -/

/--
The selected middle Fourier amplitude is ordinary Fourier `L¹`.
-/
theorem h3BKMSelectedMiddleGradientFourierAmplitude_integrable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (A : ℝ)
    (j i : Fin 3) :
    Integrable
      (h3BKMSelectedMiddleGradientFourierAmplitude
        hFourier A j i)
      (volume : Measure H3FourierPoint3) := by

  let G : H3SpectralScalarState :=
    velocityH3SpectralScalarAt
      u t hInt hMeas hFourier j

  have hModel :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3SpectralScalarRawFourierCoordinateDerivative G i ξ
            -
          h3BKMLowGradientAmplitude 0 G i ξ
            -
          h3BKMHighGradientAmplitude
            (h3BKMUpperCutoffIndex A) G i ξ)
        (volume : Measure H3FourierPoint3) :=
    ((h3SpectralScalarRawFourierCoordinateDerivative_integrable
        G i).sub
      (h3BKMLowGradientAmplitude_integrable
        0 G i)).sub
      (h3BKMHighGradientAmplitude_integrable
        (h3BKMUpperCutoffIndex A) G i)

  have hAE :=
    h3BKMSelectedMiddleGradientFourierAmplitude_ae_eq_raw_sub_low_sub_high
      hNS ht hFourier A j i

  exact
    Integrable.congr
      hModel
      hAE.symm

/--
The selected middle Fourier amplitude belongs to Fourier `L²` because it is
literally the chosen representative of a unitary `L²` Fourier transform.
-/
theorem h3BKMSelectedMiddleGradientFourierAmplitude_memLp2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (A : ℝ)
    (j i : Fin 3) :
    MemLp
      (h3BKMSelectedMiddleGradientFourierAmplitude
        hFourier A j i)
      2
      (volume : Measure H3FourierPoint3) := by

  unfold h3BKMSelectedMiddleGradientFourierAmplitude

  exact
    MeasureTheory.Lp.memLp
      ((MeasureTheory.Lp.fourierTransformₗᵢ
        H3FourierPoint3 ℂ)
        (h3BKMSelectedMiddleGradientInverseL2
          hFourier A j i))

end

end Euclidean
end Bridge
end PrimeTensor
