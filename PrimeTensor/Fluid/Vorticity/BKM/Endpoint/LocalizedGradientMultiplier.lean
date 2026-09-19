import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.DyadicMiddleGradient

/-!
# BKM endpoint: localized gradient multiplier identities

The middle-frequency physical estimates are now assembled.  To connect them
back to the canonical velocity gradient, this checkpoint returns to the
Fourier-side Biot--Savart identities and inserts one smooth dyadic shell.

Multiplying

    dᵢ ûⱼ = degree-zero coordinate multipliers applied to curl amplitudes

by the shell `ψ_R` turns each bare coordinate multiplier into the already
constructed localized multiplier `Mᵢₖ,R`.

The three identities retain exactly the vorticity sign pattern used by
`DyadicMiddleGradient`.  The final section specializes them almost everywhere
to the genuine canonical H³ Fourier velocity slice.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointLocalizedGradientMultiplier
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/--
One-shell localized Biot--Savart identity for target velocity component `0`.
-/
theorem h3BKM_frequencyShell_mul_gradient_component0_eq_localizedCurl
    {R : ℝ}
    (hR : 0 < R)
    (ξ : H3FourierPoint3)
    (g : Fin 3 → ℂ)
    (
      hDiv :
        (∑ j : Fin 3,
          h3FourierDerivativeSymbol j ξ * g j)
          =
        0
    )
    (i : Fin 3) :
    (h3BKMFrequencyShell R hR ξ : ℂ)
        *
      (h3FourierDerivativeSymbol i ξ * g 0)
      =
    h3BKMLocalizedCoordinateMultiplier R hR i 1 ξ
        *
      h3BKMCurl01Amplitude ξ g
      +
    h3BKMLocalizedCoordinateMultiplier R hR i 2 ξ
        *
      h3BKMCurl02Amplitude ξ g := by

  by_cases hξ : ξ = 0

  · subst ξ
    simp [
      h3FourierDerivativeSymbol,
      h3BKMLocalizedCoordinateMultiplier,
      h3BKMCoordinateCoefficient,
      h3BKMFourierRadiusSqReal
    ]

  · rw [
      h3BKM_gradient_component0_eq_coordinateCoefficients
        ξ hξ g hDiv i
    ]

    unfold h3BKMLocalizedCoordinateMultiplier
    ring

/--
One-shell localized Biot--Savart identity for target velocity component `1`.
-/
theorem h3BKM_frequencyShell_mul_gradient_component1_eq_localizedCurl
    {R : ℝ}
    (hR : 0 < R)
    (ξ : H3FourierPoint3)
    (g : Fin 3 → ℂ)
    (
      hDiv :
        (∑ j : Fin 3,
          h3FourierDerivativeSymbol j ξ * g j)
          =
        0
    )
    (i : Fin 3) :
    (h3BKMFrequencyShell R hR ξ : ℂ)
        *
      (h3FourierDerivativeSymbol i ξ * g 1)
      =
    -
      (
        h3BKMLocalizedCoordinateMultiplier R hR i 0 ξ
          *
        h3BKMCurl01Amplitude ξ g
      )
      +
    h3BKMLocalizedCoordinateMultiplier R hR i 2 ξ
        *
      h3BKMCurl12Amplitude ξ g := by

  by_cases hξ : ξ = 0

  · subst ξ
    simp [
      h3FourierDerivativeSymbol,
      h3BKMLocalizedCoordinateMultiplier,
      h3BKMCoordinateCoefficient,
      h3BKMFourierRadiusSqReal
    ]

  · rw [
      h3BKM_gradient_component1_eq_coordinateCoefficients
        ξ hξ g hDiv i
    ]

    unfold h3BKMLocalizedCoordinateMultiplier
    ring

/--
One-shell localized Biot--Savart identity for target velocity component `2`.
-/
theorem h3BKM_frequencyShell_mul_gradient_component2_eq_localizedCurl
    {R : ℝ}
    (hR : 0 < R)
    (ξ : H3FourierPoint3)
    (g : Fin 3 → ℂ)
    (
      hDiv :
        (∑ j : Fin 3,
          h3FourierDerivativeSymbol j ξ * g j)
          =
        0
    )
    (i : Fin 3) :
    (h3BKMFrequencyShell R hR ξ : ℂ)
        *
      (h3FourierDerivativeSymbol i ξ * g 2)
      =
    -
      (
        h3BKMLocalizedCoordinateMultiplier R hR i 0 ξ
          *
        h3BKMCurl02Amplitude ξ g
      )
      -
    h3BKMLocalizedCoordinateMultiplier R hR i 1 ξ
        *
      h3BKMCurl12Amplitude ξ g := by

  by_cases hξ : ξ = 0

  · subst ξ
    simp [
      h3FourierDerivativeSymbol,
      h3BKMLocalizedCoordinateMultiplier,
      h3BKMCoordinateCoefficient,
      h3BKMFourierRadiusSqReal
    ]

  · rw [
      h3BKM_gradient_component2_eq_coordinateCoefficients
        ξ hξ g hDiv i
    ]

    unfold h3BKMLocalizedCoordinateMultiplier
    ring

/--
Canonical-slice localized multiplier identity for target velocity component `0`.
-/
theorem velocityH3BaseFourier_frequencyShell_gradient_component0_eq_localizedCurl_ae
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t R : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (hR : 0 < R) :
    ∀ᵐ ξ ∂(volume : Measure H3FourierPoint3),
      ∀ i : Fin 3,
        (h3BKMFrequencyShell R hR ξ : ℂ)
            *
          (
            h3FourierDerivativeSymbol i ξ
              *
            velocityH3BaseFourierAt
              u t hInt hMeas 0 ξ
          )
          =
        h3BKMLocalizedCoordinateMultiplier R hR i 1 ξ
            *
          h3BKMCanonicalCurl01Amplitude
            hInt hMeas ξ
          +
        h3BKMLocalizedCoordinateMultiplier R hR i 2 ξ
            *
          h3BKMCanonicalCurl02Amplitude
            hInt hMeas ξ := by

  have hDiv :
      VelocityH3BaseFourierDivergenceFreeAt
        u t hInt hMeas :=
    velocityH3BaseFourierDivergenceFreeAt_of_preterminal
      hNS ht hFourier

  filter_upwards [hDiv] with ξ hDivξ

  intro i

  simpa only [
    h3BKMCanonicalCurl01Amplitude,
    h3BKMCanonicalCurl02Amplitude
  ] using
    h3BKM_frequencyShell_mul_gradient_component0_eq_localizedCurl
      hR
      ξ
      (fun j =>
        velocityH3BaseFourierAt
          u t hInt hMeas j ξ)
      hDivξ
      i

/--
Canonical-slice localized multiplier identity for target velocity component `1`.
-/
theorem velocityH3BaseFourier_frequencyShell_gradient_component1_eq_localizedCurl_ae
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t R : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (hR : 0 < R) :
    ∀ᵐ ξ ∂(volume : Measure H3FourierPoint3),
      ∀ i : Fin 3,
        (h3BKMFrequencyShell R hR ξ : ℂ)
            *
          (
            h3FourierDerivativeSymbol i ξ
              *
            velocityH3BaseFourierAt
              u t hInt hMeas 1 ξ
          )
          =
        -
          (
            h3BKMLocalizedCoordinateMultiplier R hR i 0 ξ
              *
            h3BKMCanonicalCurl01Amplitude
              hInt hMeas ξ
          )
          +
        h3BKMLocalizedCoordinateMultiplier R hR i 2 ξ
            *
          h3BKMCanonicalCurl12Amplitude
            hInt hMeas ξ := by

  have hDiv :
      VelocityH3BaseFourierDivergenceFreeAt
        u t hInt hMeas :=
    velocityH3BaseFourierDivergenceFreeAt_of_preterminal
      hNS ht hFourier

  filter_upwards [hDiv] with ξ hDivξ

  intro i

  simpa only [
    h3BKMCanonicalCurl01Amplitude,
    h3BKMCanonicalCurl12Amplitude
  ] using
    h3BKM_frequencyShell_mul_gradient_component1_eq_localizedCurl
      hR
      ξ
      (fun j =>
        velocityH3BaseFourierAt
          u t hInt hMeas j ξ)
      hDivξ
      i

/--
Canonical-slice localized multiplier identity for target velocity component `2`.
-/
theorem velocityH3BaseFourier_frequencyShell_gradient_component2_eq_localizedCurl_ae
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t R : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (hR : 0 < R) :
    ∀ᵐ ξ ∂(volume : Measure H3FourierPoint3),
      ∀ i : Fin 3,
        (h3BKMFrequencyShell R hR ξ : ℂ)
            *
          (
            h3FourierDerivativeSymbol i ξ
              *
            velocityH3BaseFourierAt
              u t hInt hMeas 2 ξ
          )
          =
        -
          (
            h3BKMLocalizedCoordinateMultiplier R hR i 0 ξ
              *
            h3BKMCanonicalCurl02Amplitude
              hInt hMeas ξ
          )
          -
        h3BKMLocalizedCoordinateMultiplier R hR i 1 ξ
            *
          h3BKMCanonicalCurl12Amplitude
            hInt hMeas ξ := by

  have hDiv :
      VelocityH3BaseFourierDivergenceFreeAt
        u t hInt hMeas :=
    velocityH3BaseFourierDivergenceFreeAt_of_preterminal
      hNS ht hFourier

  filter_upwards [hDiv] with ξ hDivξ

  intro i

  simpa only [
    h3BKMCanonicalCurl02Amplitude,
    h3BKMCanonicalCurl12Amplitude
  ] using
    h3BKM_frequencyShell_mul_gradient_component2_eq_localizedCurl
      hR
      ξ
      (fun j =>
        velocityH3BaseFourierAt
          u t hInt hMeas j ξ)
      hDivξ
      i

end

end Euclidean
end Bridge
end PrimeTensor
