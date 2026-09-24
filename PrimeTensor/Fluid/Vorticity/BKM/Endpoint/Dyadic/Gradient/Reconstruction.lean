import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Dyadic.Shell.Partition

/-!
# BKM endpoint: exact gradient reconstruction on dyadic annuli

Two adjacent BKM shells form an exact partition on

    R_{n+1} ≤ ‖ξ‖ ≤ R_{n+2}.

Each individual shell already satisfies the localized Biot--Savart identity.
Adding the two identities and using the partition therefore reconstructs the
actual Fourier gradient mode itself.

For target component `0`, for example,

    dᵢ û₀
      =
    (Mᵢ₁,n C₀₁ + Mᵢ₂,n C₀₂)
      +
    (Mᵢ₁,n+1 C₀₁ + Mᵢ₂,n+1 C₀₂)

throughout the annulus.  The corresponding sign patterns are proved for target
components `1` and `2`.

The final three theorems specialize these exact annular identities almost
everywhere to the canonical preterminal H³ Fourier velocity slice.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointDyadicGradientReconstruction
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/--
Exact adjacent-shell reconstruction of target gradient component `0`.
-/
theorem h3BKMDyadicGradientComponent0_reconstruct_on_annulus
    (n : ℕ)
    (ξ : H3FourierPoint3)
    (g : Fin 3 → ℂ)
    (
      hDiv :
        (∑ j : Fin 3,
          h3FourierDerivativeSymbol j ξ * g j)
          =
        0
    )
    (i : Fin 3)
    (
      hLower :
        h3BKMDyadicRadius (n + 1) ≤ ‖ξ‖
    )
    (
      hUpper :
        ‖ξ‖ ≤ h3BKMDyadicRadius (n + 2)
    ) :
    h3FourierDerivativeSymbol i ξ * g 0
      =
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
    )
      +
    (
      h3BKMLocalizedCoordinateMultiplier
          (h3BKMDyadicRadius (n + 1))
          (h3BKMDyadicRadius_pos (n + 1))
          i 1 ξ
        *
      h3BKMCurl01Amplitude ξ g
        +
      h3BKMLocalizedCoordinateMultiplier
          (h3BKMDyadicRadius (n + 1))
          (h3BKMDyadicRadius_pos (n + 1))
          i 2 ξ
        *
      h3BKMCurl02Amplitude ξ g
    ) := by

  have hPartitionReal :=
    h3BKMDyadicFrequencyShell_adjacent_eq_one
      n
      hLower
      hUpper

  have hPartition :
      (
        h3BKMFrequencyShell
            (h3BKMDyadicRadius n)
            (h3BKMDyadicRadius_pos n)
            ξ : ℂ
      )
        +
      (
        h3BKMFrequencyShell
            (h3BKMDyadicRadius (n + 1))
            (h3BKMDyadicRadius_pos (n + 1))
            ξ : ℂ
      )
        =
      1 := by
    exact_mod_cast hPartitionReal

  have hShell0 :=
    h3BKM_frequencyShell_mul_gradient_component0_eq_localizedCurl
      (h3BKMDyadicRadius_pos n)
      ξ
      g
      hDiv
      i

  have hShell1 :=
    h3BKM_frequencyShell_mul_gradient_component0_eq_localizedCurl
      (h3BKMDyadicRadius_pos (n + 1))
      ξ
      g
      hDiv
      i

  calc
    h3FourierDerivativeSymbol i ξ * g 0
        =
      1 * (h3FourierDerivativeSymbol i ξ * g 0) := by
      ring

    _ =
      (
        (
          h3BKMFrequencyShell
              (h3BKMDyadicRadius n)
              (h3BKMDyadicRadius_pos n)
              ξ : ℂ
        )
          +
        (
          h3BKMFrequencyShell
              (h3BKMDyadicRadius (n + 1))
              (h3BKMDyadicRadius_pos (n + 1))
              ξ : ℂ
        )
      )
        *
      (h3FourierDerivativeSymbol i ξ * g 0) := by
      rw [hPartition]

    _ =
      (
        h3BKMFrequencyShell
            (h3BKMDyadicRadius n)
            (h3BKMDyadicRadius_pos n)
            ξ : ℂ
      )
        *
      (h3FourierDerivativeSymbol i ξ * g 0)
        +
      (
        h3BKMFrequencyShell
            (h3BKMDyadicRadius (n + 1))
            (h3BKMDyadicRadius_pos (n + 1))
            ξ : ℂ
      )
        *
      (h3FourierDerivativeSymbol i ξ * g 0) := by
      ring

    _ =
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
      )
        +
      (
        h3BKMLocalizedCoordinateMultiplier
            (h3BKMDyadicRadius (n + 1))
            (h3BKMDyadicRadius_pos (n + 1))
            i 1 ξ
          *
        h3BKMCurl01Amplitude ξ g
          +
        h3BKMLocalizedCoordinateMultiplier
            (h3BKMDyadicRadius (n + 1))
            (h3BKMDyadicRadius_pos (n + 1))
            i 2 ξ
          *
        h3BKMCurl02Amplitude ξ g
      ) := by
      rw [hShell0, hShell1]

/--
Exact adjacent-shell reconstruction of target gradient component `1`.
-/
theorem h3BKMDyadicGradientComponent1_reconstruct_on_annulus
    (n : ℕ)
    (ξ : H3FourierPoint3)
    (g : Fin 3 → ℂ)
    (
      hDiv :
        (∑ j : Fin 3,
          h3FourierDerivativeSymbol j ξ * g j)
          =
        0
    )
    (i : Fin 3)
    (
      hLower :
        h3BKMDyadicRadius (n + 1) ≤ ‖ξ‖
    )
    (
      hUpper :
        ‖ξ‖ ≤ h3BKMDyadicRadius (n + 2)
    ) :
    h3FourierDerivativeSymbol i ξ * g 1
      =
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
    )
      +
    (
      -
        (
          h3BKMLocalizedCoordinateMultiplier
              (h3BKMDyadicRadius (n + 1))
              (h3BKMDyadicRadius_pos (n + 1))
              i 0 ξ
            *
          h3BKMCurl01Amplitude ξ g
        )
        +
      h3BKMLocalizedCoordinateMultiplier
          (h3BKMDyadicRadius (n + 1))
          (h3BKMDyadicRadius_pos (n + 1))
          i 2 ξ
        *
      h3BKMCurl12Amplitude ξ g
    ) := by

  have hPartitionReal :=
    h3BKMDyadicFrequencyShell_adjacent_eq_one
      n
      hLower
      hUpper

  have hPartition :
      (
        h3BKMFrequencyShell
            (h3BKMDyadicRadius n)
            (h3BKMDyadicRadius_pos n)
            ξ : ℂ
      )
        +
      (
        h3BKMFrequencyShell
            (h3BKMDyadicRadius (n + 1))
            (h3BKMDyadicRadius_pos (n + 1))
            ξ : ℂ
      )
        =
      1 := by
    exact_mod_cast hPartitionReal

  have hShell0 :=
    h3BKM_frequencyShell_mul_gradient_component1_eq_localizedCurl
      (h3BKMDyadicRadius_pos n)
      ξ
      g
      hDiv
      i

  have hShell1 :=
    h3BKM_frequencyShell_mul_gradient_component1_eq_localizedCurl
      (h3BKMDyadicRadius_pos (n + 1))
      ξ
      g
      hDiv
      i

  calc
    h3FourierDerivativeSymbol i ξ * g 1
        =
      1 * (h3FourierDerivativeSymbol i ξ * g 1) := by
      ring

    _ =
      (
        (
          h3BKMFrequencyShell
              (h3BKMDyadicRadius n)
              (h3BKMDyadicRadius_pos n)
              ξ : ℂ
        )
          +
        (
          h3BKMFrequencyShell
              (h3BKMDyadicRadius (n + 1))
              (h3BKMDyadicRadius_pos (n + 1))
              ξ : ℂ
        )
      )
        *
      (h3FourierDerivativeSymbol i ξ * g 1) := by
      rw [hPartition]

    _ =
      (
        h3BKMFrequencyShell
            (h3BKMDyadicRadius n)
            (h3BKMDyadicRadius_pos n)
            ξ : ℂ
      )
        *
      (h3FourierDerivativeSymbol i ξ * g 1)
        +
      (
        h3BKMFrequencyShell
            (h3BKMDyadicRadius (n + 1))
            (h3BKMDyadicRadius_pos (n + 1))
            ξ : ℂ
      )
        *
      (h3FourierDerivativeSymbol i ξ * g 1) := by
      ring

    _ =
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
      )
        +
      (
        -
          (
            h3BKMLocalizedCoordinateMultiplier
                (h3BKMDyadicRadius (n + 1))
                (h3BKMDyadicRadius_pos (n + 1))
                i 0 ξ
              *
            h3BKMCurl01Amplitude ξ g
          )
          +
        h3BKMLocalizedCoordinateMultiplier
            (h3BKMDyadicRadius (n + 1))
            (h3BKMDyadicRadius_pos (n + 1))
            i 2 ξ
          *
        h3BKMCurl12Amplitude ξ g
      ) := by
      rw [hShell0, hShell1]

/--
Exact adjacent-shell reconstruction of target gradient component `2`.
-/
theorem h3BKMDyadicGradientComponent2_reconstruct_on_annulus
    (n : ℕ)
    (ξ : H3FourierPoint3)
    (g : Fin 3 → ℂ)
    (
      hDiv :
        (∑ j : Fin 3,
          h3FourierDerivativeSymbol j ξ * g j)
          =
        0
    )
    (i : Fin 3)
    (
      hLower :
        h3BKMDyadicRadius (n + 1) ≤ ‖ξ‖
    )
    (
      hUpper :
        ‖ξ‖ ≤ h3BKMDyadicRadius (n + 2)
    ) :
    h3FourierDerivativeSymbol i ξ * g 2
      =
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
    )
      +
    (
      -
        (
          h3BKMLocalizedCoordinateMultiplier
              (h3BKMDyadicRadius (n + 1))
              (h3BKMDyadicRadius_pos (n + 1))
              i 0 ξ
            *
          h3BKMCurl02Amplitude ξ g
        )
        -
      h3BKMLocalizedCoordinateMultiplier
          (h3BKMDyadicRadius (n + 1))
          (h3BKMDyadicRadius_pos (n + 1))
          i 1 ξ
        *
      h3BKMCurl12Amplitude ξ g
    ) := by

  have hPartitionReal :=
    h3BKMDyadicFrequencyShell_adjacent_eq_one
      n
      hLower
      hUpper

  have hPartition :
      (
        h3BKMFrequencyShell
            (h3BKMDyadicRadius n)
            (h3BKMDyadicRadius_pos n)
            ξ : ℂ
      )
        +
      (
        h3BKMFrequencyShell
            (h3BKMDyadicRadius (n + 1))
            (h3BKMDyadicRadius_pos (n + 1))
            ξ : ℂ
      )
        =
      1 := by
    exact_mod_cast hPartitionReal

  have hShell0 :=
    h3BKM_frequencyShell_mul_gradient_component2_eq_localizedCurl
      (h3BKMDyadicRadius_pos n)
      ξ
      g
      hDiv
      i

  have hShell1 :=
    h3BKM_frequencyShell_mul_gradient_component2_eq_localizedCurl
      (h3BKMDyadicRadius_pos (n + 1))
      ξ
      g
      hDiv
      i

  calc
    h3FourierDerivativeSymbol i ξ * g 2
        =
      1 * (h3FourierDerivativeSymbol i ξ * g 2) := by
      ring

    _ =
      (
        (
          h3BKMFrequencyShell
              (h3BKMDyadicRadius n)
              (h3BKMDyadicRadius_pos n)
              ξ : ℂ
        )
          +
        (
          h3BKMFrequencyShell
              (h3BKMDyadicRadius (n + 1))
              (h3BKMDyadicRadius_pos (n + 1))
              ξ : ℂ
        )
      )
        *
      (h3FourierDerivativeSymbol i ξ * g 2) := by
      rw [hPartition]

    _ =
      (
        h3BKMFrequencyShell
            (h3BKMDyadicRadius n)
            (h3BKMDyadicRadius_pos n)
            ξ : ℂ
      )
        *
      (h3FourierDerivativeSymbol i ξ * g 2)
        +
      (
        h3BKMFrequencyShell
            (h3BKMDyadicRadius (n + 1))
            (h3BKMDyadicRadius_pos (n + 1))
            ξ : ℂ
      )
        *
      (h3FourierDerivativeSymbol i ξ * g 2) := by
      ring

    _ =
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
      )
        +
      (
        -
          (
            h3BKMLocalizedCoordinateMultiplier
                (h3BKMDyadicRadius (n + 1))
                (h3BKMDyadicRadius_pos (n + 1))
                i 0 ξ
              *
            h3BKMCurl02Amplitude ξ g
          )
          -
        h3BKMLocalizedCoordinateMultiplier
            (h3BKMDyadicRadius (n + 1))
            (h3BKMDyadicRadius_pos (n + 1))
            i 1 ξ
          *
        h3BKMCurl12Amplitude ξ g
      ) := by
      rw [hShell0, hShell1]

/--
Canonical H³ adjacent-shell reconstruction for target component `0`, almost
everywhere on each dyadic annulus.
-/
theorem velocityH3BaseFourier_dyadicGradientComponent0_reconstruct_ae
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (n : ℕ) :
    ∀ᵐ ξ ∂(volume : Measure H3FourierPoint3),
      ∀ i : Fin 3,
        h3BKMDyadicRadius (n + 1) ≤ ‖ξ‖
          →
        ‖ξ‖ ≤ h3BKMDyadicRadius (n + 2)
          →
        h3FourierDerivativeSymbol i ξ
            *
          velocityH3BaseFourierAt
            u t hInt hMeas 0 ξ
          =
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
        )
          +
        (
          h3BKMLocalizedCoordinateMultiplier
              (h3BKMDyadicRadius (n + 1))
              (h3BKMDyadicRadius_pos (n + 1))
              i 1 ξ
            *
          h3BKMCanonicalCurl01Amplitude
            hInt hMeas ξ
            +
          h3BKMLocalizedCoordinateMultiplier
              (h3BKMDyadicRadius (n + 1))
              (h3BKMDyadicRadius_pos (n + 1))
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

  intro i hLower hUpper

  simpa only [
    h3BKMCanonicalCurl01Amplitude,
    h3BKMCanonicalCurl02Amplitude
  ] using
    h3BKMDyadicGradientComponent0_reconstruct_on_annulus
      n
      ξ
      (fun j =>
        velocityH3BaseFourierAt
          u t hInt hMeas j ξ)
      hDivξ
      i
      hLower
      hUpper

/--
Canonical H³ adjacent-shell reconstruction for target component `1`.
-/
theorem velocityH3BaseFourier_dyadicGradientComponent1_reconstruct_ae
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (n : ℕ) :
    ∀ᵐ ξ ∂(volume : Measure H3FourierPoint3),
      ∀ i : Fin 3,
        h3BKMDyadicRadius (n + 1) ≤ ‖ξ‖
          →
        ‖ξ‖ ≤ h3BKMDyadicRadius (n + 2)
          →
        h3FourierDerivativeSymbol i ξ
            *
          velocityH3BaseFourierAt
            u t hInt hMeas 1 ξ
          =
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
        )
          +
        (
          -
            (
              h3BKMLocalizedCoordinateMultiplier
                  (h3BKMDyadicRadius (n + 1))
                  (h3BKMDyadicRadius_pos (n + 1))
                  i 0 ξ
                *
              h3BKMCanonicalCurl01Amplitude
                hInt hMeas ξ
            )
            +
          h3BKMLocalizedCoordinateMultiplier
              (h3BKMDyadicRadius (n + 1))
              (h3BKMDyadicRadius_pos (n + 1))
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

  intro i hLower hUpper

  simpa only [
    h3BKMCanonicalCurl01Amplitude,
    h3BKMCanonicalCurl12Amplitude
  ] using
    h3BKMDyadicGradientComponent1_reconstruct_on_annulus
      n
      ξ
      (fun j =>
        velocityH3BaseFourierAt
          u t hInt hMeas j ξ)
      hDivξ
      i
      hLower
      hUpper

/--
Canonical H³ adjacent-shell reconstruction for target component `2`.
-/
theorem velocityH3BaseFourier_dyadicGradientComponent2_reconstruct_ae
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (n : ℕ) :
    ∀ᵐ ξ ∂(volume : Measure H3FourierPoint3),
      ∀ i : Fin 3,
        h3BKMDyadicRadius (n + 1) ≤ ‖ξ‖
          →
        ‖ξ‖ ≤ h3BKMDyadicRadius (n + 2)
          →
        h3FourierDerivativeSymbol i ξ
            *
          velocityH3BaseFourierAt
            u t hInt hMeas 2 ξ
          =
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
        )
          +
        (
          -
            (
              h3BKMLocalizedCoordinateMultiplier
                  (h3BKMDyadicRadius (n + 1))
                  (h3BKMDyadicRadius_pos (n + 1))
                  i 0 ξ
                *
              h3BKMCanonicalCurl02Amplitude
                hInt hMeas ξ
            )
            -
          h3BKMLocalizedCoordinateMultiplier
              (h3BKMDyadicRadius (n + 1))
              (h3BKMDyadicRadius_pos (n + 1))
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

  intro i hLower hUpper

  simpa only [
    h3BKMCanonicalCurl02Amplitude,
    h3BKMCanonicalCurl12Amplitude
  ] using
    h3BKMDyadicGradientComponent2_reconstruct_on_annulus
      n
      ξ
      (fun j =>
        velocityH3BaseFourierAt
          u t hInt hMeas j ξ)
      hDivξ
      i
      hLower
      hUpper

end

end Euclidean
end Bridge
end PrimeTensor
