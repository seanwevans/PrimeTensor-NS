import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Gradient.Localized.Multiplier

/-!
# BKM endpoint: finite-shell localized gradient identities

The preceding checkpoint inserted one smooth dyadic shell into the Fourier
Biot--Savart identities.  The middle-frequency object is a finite sum of those
shells, so the next step is purely finite algebra.

For an arbitrary finite shell set `J : Finset ℕ`, sum the one-shell identities
at radii `2ⁿ`.  The three target velocity components retain the exact
Biot--Savart sign pattern.  We then specialize `J` to the middle window
`Finset.Icc lo hi` and finally to the genuine canonical H³ Fourier slice.

This keeps the next inverse-Fourier step clean: it will only need to transport a
finite sum of already-identified localized multiplier terms.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointLocalizedGradientShellSum
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/--
Finite-shell localized Biot--Savart identity for target velocity component `0`.
-/
theorem h3BKM_sum_frequencyShell_mul_gradient_component0_eq_localizedCurl
    (J : Finset ℕ)
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
    (∑ n ∈ J,
      (h3BKMFrequencyShell
          (h3BKMDyadicRadius n)
          (h3BKMDyadicRadius_pos n)
          ξ : ℂ)
        *
      (h3FourierDerivativeSymbol i ξ * g 0))
      =
    ∑ n ∈ J,
      (
        h3BKMLocalizedCoordinateMultiplier
            (h3BKMDyadicRadius n)
            (h3BKMDyadicRadius_pos n)
            i 1 ξ
          *
        h3BKMCurl01Amplitude ξ g
          +
        h3BKMLocalizedCoordinateMultiplier
            (h3BKMDyadicRadius n)
            (h3BKMDyadicRadius_pos n)
            i 2 ξ
          *
        h3BKMCurl02Amplitude ξ g
      ) := by

  apply Finset.sum_congr rfl
  intro n hn

  exact
    h3BKM_frequencyShell_mul_gradient_component0_eq_localizedCurl
      (h3BKMDyadicRadius_pos n)
      ξ
      g
      hDiv
      i

/--
Finite-shell localized Biot--Savart identity for target velocity component `1`.
-/
theorem h3BKM_sum_frequencyShell_mul_gradient_component1_eq_localizedCurl
    (J : Finset ℕ)
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
    (∑ n ∈ J,
      (h3BKMFrequencyShell
          (h3BKMDyadicRadius n)
          (h3BKMDyadicRadius_pos n)
          ξ : ℂ)
        *
      (h3FourierDerivativeSymbol i ξ * g 1))
      =
    ∑ n ∈ J,
      (
        -
          (
            h3BKMLocalizedCoordinateMultiplier
                (h3BKMDyadicRadius n)
                (h3BKMDyadicRadius_pos n)
                i 0 ξ
              *
            h3BKMCurl01Amplitude ξ g
          )
          +
        h3BKMLocalizedCoordinateMultiplier
            (h3BKMDyadicRadius n)
            (h3BKMDyadicRadius_pos n)
            i 2 ξ
          *
        h3BKMCurl12Amplitude ξ g
      ) := by

  apply Finset.sum_congr rfl
  intro n hn

  exact
    h3BKM_frequencyShell_mul_gradient_component1_eq_localizedCurl
      (h3BKMDyadicRadius_pos n)
      ξ
      g
      hDiv
      i

/--
Finite-shell localized Biot--Savart identity for target velocity component `2`.
-/
theorem h3BKM_sum_frequencyShell_mul_gradient_component2_eq_localizedCurl
    (J : Finset ℕ)
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
    (∑ n ∈ J,
      (h3BKMFrequencyShell
          (h3BKMDyadicRadius n)
          (h3BKMDyadicRadius_pos n)
          ξ : ℂ)
        *
      (h3FourierDerivativeSymbol i ξ * g 2))
      =
    ∑ n ∈ J,
      (
        -
          (
            h3BKMLocalizedCoordinateMultiplier
                (h3BKMDyadicRadius n)
                (h3BKMDyadicRadius_pos n)
                i 0 ξ
              *
            h3BKMCurl02Amplitude ξ g
          )
          -
        h3BKMLocalizedCoordinateMultiplier
            (h3BKMDyadicRadius n)
            (h3BKMDyadicRadius_pos n)
            i 1 ξ
          *
        h3BKMCurl12Amplitude ξ g
      ) := by

  apply Finset.sum_congr rfl
  intro n hn

  exact
    h3BKM_frequencyShell_mul_gradient_component2_eq_localizedCurl
      (h3BKMDyadicRadius_pos n)
      ξ
      g
      hDiv
      i

/--
Middle-window finite-shell identity for target velocity component `0`.
-/
theorem h3BKM_middle_frequencyShell_gradient_component0_eq_localizedCurl
    (lo hi : ℕ)
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
    (∑ n ∈ Finset.Icc lo hi,
      (h3BKMFrequencyShell
          (h3BKMDyadicRadius n)
          (h3BKMDyadicRadius_pos n)
          ξ : ℂ)
        *
      (h3FourierDerivativeSymbol i ξ * g 0))
      =
    ∑ n ∈ Finset.Icc lo hi,
      (
        h3BKMLocalizedCoordinateMultiplier
            (h3BKMDyadicRadius n)
            (h3BKMDyadicRadius_pos n)
            i 1 ξ
          *
        h3BKMCurl01Amplitude ξ g
          +
        h3BKMLocalizedCoordinateMultiplier
            (h3BKMDyadicRadius n)
            (h3BKMDyadicRadius_pos n)
            i 2 ξ
          *
        h3BKMCurl02Amplitude ξ g
      ) := by

  exact
    h3BKM_sum_frequencyShell_mul_gradient_component0_eq_localizedCurl
      (Finset.Icc lo hi)
      ξ g hDiv i

/--
Middle-window finite-shell identity for target velocity component `1`.
-/
theorem h3BKM_middle_frequencyShell_gradient_component1_eq_localizedCurl
    (lo hi : ℕ)
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
    (∑ n ∈ Finset.Icc lo hi,
      (h3BKMFrequencyShell
          (h3BKMDyadicRadius n)
          (h3BKMDyadicRadius_pos n)
          ξ : ℂ)
        *
      (h3FourierDerivativeSymbol i ξ * g 1))
      =
    ∑ n ∈ Finset.Icc lo hi,
      (
        -
          (
            h3BKMLocalizedCoordinateMultiplier
                (h3BKMDyadicRadius n)
                (h3BKMDyadicRadius_pos n)
                i 0 ξ
              *
            h3BKMCurl01Amplitude ξ g
          )
          +
        h3BKMLocalizedCoordinateMultiplier
            (h3BKMDyadicRadius n)
            (h3BKMDyadicRadius_pos n)
            i 2 ξ
          *
        h3BKMCurl12Amplitude ξ g
      ) := by

  exact
    h3BKM_sum_frequencyShell_mul_gradient_component1_eq_localizedCurl
      (Finset.Icc lo hi)
      ξ g hDiv i

/--
Middle-window finite-shell identity for target velocity component `2`.
-/
theorem h3BKM_middle_frequencyShell_gradient_component2_eq_localizedCurl
    (lo hi : ℕ)
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
    (∑ n ∈ Finset.Icc lo hi,
      (h3BKMFrequencyShell
          (h3BKMDyadicRadius n)
          (h3BKMDyadicRadius_pos n)
          ξ : ℂ)
        *
      (h3FourierDerivativeSymbol i ξ * g 2))
      =
    ∑ n ∈ Finset.Icc lo hi,
      (
        -
          (
            h3BKMLocalizedCoordinateMultiplier
                (h3BKMDyadicRadius n)
                (h3BKMDyadicRadius_pos n)
                i 0 ξ
              *
            h3BKMCurl02Amplitude ξ g
          )
          -
        h3BKMLocalizedCoordinateMultiplier
            (h3BKMDyadicRadius n)
            (h3BKMDyadicRadius_pos n)
            i 1 ξ
          *
        h3BKMCurl12Amplitude ξ g
      ) := by

  exact
    h3BKM_sum_frequencyShell_mul_gradient_component2_eq_localizedCurl
      (Finset.Icc lo hi)
      ξ g hDiv i

/--
Canonical H³ middle-window localized identity for target velocity component `0`.
-/
theorem velocityH3BaseFourier_middle_frequencyShell_gradient_component0_eq_localizedCurl_ae
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (lo hi : ℕ) :
    ∀ᵐ ξ ∂(volume : Measure H3FourierPoint3),
      ∀ i : Fin 3,
        (∑ n ∈ Finset.Icc lo hi,
          (h3BKMFrequencyShell
              (h3BKMDyadicRadius n)
              (h3BKMDyadicRadius_pos n)
              ξ : ℂ)
            *
          (
            h3FourierDerivativeSymbol i ξ
              *
            velocityH3BaseFourierAt
              u t hInt hMeas 0 ξ
          ))
          =
        ∑ n ∈ Finset.Icc lo hi,
          (
            h3BKMLocalizedCoordinateMultiplier
                (h3BKMDyadicRadius n)
                (h3BKMDyadicRadius_pos n)
                i 1 ξ
              *
            h3BKMCanonicalCurl01Amplitude
              hInt hMeas ξ
              +
            h3BKMLocalizedCoordinateMultiplier
                (h3BKMDyadicRadius n)
                (h3BKMDyadicRadius_pos n)
                i 2 ξ
              *
            h3BKMCanonicalCurl02Amplitude
              hInt hMeas ξ
          ) := by

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
    h3BKM_middle_frequencyShell_gradient_component0_eq_localizedCurl
      lo
      hi
      ξ
      (fun j =>
        velocityH3BaseFourierAt
          u t hInt hMeas j ξ)
      hDivξ
      i

/--
Canonical H³ middle-window localized identity for target velocity component `1`.
-/
theorem velocityH3BaseFourier_middle_frequencyShell_gradient_component1_eq_localizedCurl_ae
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (lo hi : ℕ) :
    ∀ᵐ ξ ∂(volume : Measure H3FourierPoint3),
      ∀ i : Fin 3,
        (∑ n ∈ Finset.Icc lo hi,
          (h3BKMFrequencyShell
              (h3BKMDyadicRadius n)
              (h3BKMDyadicRadius_pos n)
              ξ : ℂ)
            *
          (
            h3FourierDerivativeSymbol i ξ
              *
            velocityH3BaseFourierAt
              u t hInt hMeas 1 ξ
          ))
          =
        ∑ n ∈ Finset.Icc lo hi,
          (
            -
              (
                h3BKMLocalizedCoordinateMultiplier
                    (h3BKMDyadicRadius n)
                    (h3BKMDyadicRadius_pos n)
                    i 0 ξ
                  *
                h3BKMCanonicalCurl01Amplitude
                  hInt hMeas ξ
              )
              +
            h3BKMLocalizedCoordinateMultiplier
                (h3BKMDyadicRadius n)
                (h3BKMDyadicRadius_pos n)
                i 2 ξ
              *
            h3BKMCanonicalCurl12Amplitude
              hInt hMeas ξ
          ) := by

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
    h3BKM_middle_frequencyShell_gradient_component1_eq_localizedCurl
      lo
      hi
      ξ
      (fun j =>
        velocityH3BaseFourierAt
          u t hInt hMeas j ξ)
      hDivξ
      i

/--
Canonical H³ middle-window localized identity for target velocity component `2`.
-/
theorem velocityH3BaseFourier_middle_frequencyShell_gradient_component2_eq_localizedCurl_ae
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (lo hi : ℕ) :
    ∀ᵐ ξ ∂(volume : Measure H3FourierPoint3),
      ∀ i : Fin 3,
        (∑ n ∈ Finset.Icc lo hi,
          (h3BKMFrequencyShell
              (h3BKMDyadicRadius n)
              (h3BKMDyadicRadius_pos n)
              ξ : ℂ)
            *
          (
            h3FourierDerivativeSymbol i ξ
              *
            velocityH3BaseFourierAt
              u t hInt hMeas 2 ξ
          ))
          =
        ∑ n ∈ Finset.Icc lo hi,
          (
            -
              (
                h3BKMLocalizedCoordinateMultiplier
                    (h3BKMDyadicRadius n)
                    (h3BKMDyadicRadius_pos n)
                    i 0 ξ
                  *
                h3BKMCanonicalCurl02Amplitude
                  hInt hMeas ξ
              )
              -
            h3BKMLocalizedCoordinateMultiplier
                (h3BKMDyadicRadius n)
                (h3BKMDyadicRadius_pos n)
                i 1 ξ
              *
            h3BKMCanonicalCurl12Amplitude
              hInt hMeas ξ
          ) := by

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
    h3BKM_middle_frequencyShell_gradient_component2_eq_localizedCurl
      lo
      hi
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
