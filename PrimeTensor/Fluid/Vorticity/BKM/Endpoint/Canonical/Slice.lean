import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Fourier.Bound
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Leray.Physical.Incompressibility

/-!
# BKM endpoint: canonical H³ Fourier slice

The abstract multiplier estimate is now specialized to the genuine raw Fourier
velocity attached to one classical preterminal H³ snapshot.

For

    ĝⱼ(ξ) = velocityH3BaseFourierAt ... j ξ,

physical incompressibility already gives, almost everywhere,

    Σⱼ dⱼ(ξ) ĝⱼ(ξ) = 0.

Therefore the degree-zero Biot--Savart estimates from `FourierBound` apply
directly to the canonical velocity slice.

This file deliberately stops one layer before the physical `L∞` vorticity
estimate.  The pairwise curl amplitudes defined here are Fourier-side
quantities.  Turning a physical componentwise bound

    |ωₖ(x)| ≤ g(t)

into an estimate for a frequency-localized inverse Fourier curl operator
requires the band-limited kernel argument; it is not a pointwise bound on the
Fourier transform of an `L∞` function.

That kernel/localization step is the next analytic increment.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointCanonicalSlice
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Canonical pairwise curl amplitude `d₁ û₀ - d₀ û₁`. -/
def h3BKMCanonicalCurl01Amplitude
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (ξ : H3FourierPoint3) : ℂ :=
  h3BKMCurl01Amplitude
    ξ
    (fun j =>
      velocityH3BaseFourierAt
        u t hInt hMeas j ξ)

/-- Canonical pairwise curl amplitude `d₂ û₀ - d₀ û₂`. -/
def h3BKMCanonicalCurl02Amplitude
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (ξ : H3FourierPoint3) : ℂ :=
  h3BKMCurl02Amplitude
    ξ
    (fun j =>
      velocityH3BaseFourierAt
        u t hInt hMeas j ξ)

/-- Canonical pairwise curl amplitude `d₂ û₁ - d₁ û₂`. -/
def h3BKMCanonicalCurl12Amplitude
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (ξ : H3FourierPoint3) : ℂ :=
  h3BKMCurl12Amplitude
    ξ
    (fun j =>
      velocityH3BaseFourierAt
        u t hInt hMeas j ξ)

/--
For the genuine preterminal H³ velocity slice, every Fourier derivative of
component `0` is bounded almost everywhere by the two relevant pairwise curl
amplitudes.
-/
theorem velocityH3BaseFourier_gradient_component0_le_pairwiseCurl_ae
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    ∀ᵐ ξ ∂(volume : Measure H3FourierPoint3),
      ∀ i : Fin 3,
        ‖h3FourierDerivativeSymbol i ξ *
            velocityH3BaseFourierAt
              u t hInt hMeas 0 ξ‖
          ≤
        ‖h3BKMCanonicalCurl01Amplitude
            hInt hMeas ξ‖
          +
        ‖h3BKMCanonicalCurl02Amplitude
            hInt hMeas ξ‖ := by

  have hDiv :
      VelocityH3BaseFourierDivergenceFreeAt
        u t hInt hMeas :=
    velocityH3BaseFourierDivergenceFreeAt_of_preterminal
      hNS ht hFourier

  filter_upwards [hDiv] with ξ hDivξ

  intro i

  by_cases hξ : ξ = 0

  · subst ξ

    simp [
      h3FourierDerivativeSymbol,
      h3BKMCanonicalCurl01Amplitude,
      h3BKMCanonicalCurl02Amplitude,
      h3BKMCurl01Amplitude,
      h3BKMCurl02Amplitude
    ]

  · exact
      norm_h3BKM_gradient_component0_le_curl
        ξ
        hξ
        (fun j =>
          velocityH3BaseFourierAt
            u t hInt hMeas j ξ)
        hDivξ
        i

/--
Canonical-slice multiplier estimate for target velocity component `1`.
-/
theorem velocityH3BaseFourier_gradient_component1_le_pairwiseCurl_ae
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    ∀ᵐ ξ ∂(volume : Measure H3FourierPoint3),
      ∀ i : Fin 3,
        ‖h3FourierDerivativeSymbol i ξ *
            velocityH3BaseFourierAt
              u t hInt hMeas 1 ξ‖
          ≤
        ‖h3BKMCanonicalCurl01Amplitude
            hInt hMeas ξ‖
          +
        ‖h3BKMCanonicalCurl12Amplitude
            hInt hMeas ξ‖ := by

  have hDiv :
      VelocityH3BaseFourierDivergenceFreeAt
        u t hInt hMeas :=
    velocityH3BaseFourierDivergenceFreeAt_of_preterminal
      hNS ht hFourier

  filter_upwards [hDiv] with ξ hDivξ

  intro i

  by_cases hξ : ξ = 0

  · subst ξ

    simp [
      h3FourierDerivativeSymbol,
      h3BKMCanonicalCurl01Amplitude,
      h3BKMCanonicalCurl12Amplitude,
      h3BKMCurl01Amplitude,
      h3BKMCurl12Amplitude
    ]

  · exact
      norm_h3BKM_gradient_component1_le_curl
        ξ
        hξ
        (fun j =>
          velocityH3BaseFourierAt
            u t hInt hMeas j ξ)
        hDivξ
        i

/--
Canonical-slice multiplier estimate for target velocity component `2`.
-/
theorem velocityH3BaseFourier_gradient_component2_le_pairwiseCurl_ae
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    ∀ᵐ ξ ∂(volume : Measure H3FourierPoint3),
      ∀ i : Fin 3,
        ‖h3FourierDerivativeSymbol i ξ *
            velocityH3BaseFourierAt
              u t hInt hMeas 2 ξ‖
          ≤
        ‖h3BKMCanonicalCurl02Amplitude
            hInt hMeas ξ‖
          +
        ‖h3BKMCanonicalCurl12Amplitude
            hInt hMeas ξ‖ := by

  have hDiv :
      VelocityH3BaseFourierDivergenceFreeAt
        u t hInt hMeas :=
    velocityH3BaseFourierDivergenceFreeAt_of_preterminal
      hNS ht hFourier

  filter_upwards [hDiv] with ξ hDivξ

  intro i

  by_cases hξ : ξ = 0

  · subst ξ

    simp [
      h3FourierDerivativeSymbol,
      h3BKMCanonicalCurl02Amplitude,
      h3BKMCanonicalCurl12Amplitude,
      h3BKMCurl02Amplitude,
      h3BKMCurl12Amplitude
    ]

  · exact
      norm_h3BKM_gradient_component2_le_curl
        ξ
        hξ
        (fun j =>
          velocityH3BaseFourierAt
            u t hInt hMeas j ξ)
        hDivξ
        i

/--
All three canonical-slice Biot--Savart bounds hold simultaneously almost
everywhere.
-/
theorem velocityH3BaseFourier_gradient_le_pairwiseCurl_all_ae
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    ∀ᵐ ξ ∂(volume : Measure H3FourierPoint3),
      (
        ∀ i : Fin 3,
          ‖h3FourierDerivativeSymbol i ξ *
              velocityH3BaseFourierAt
                u t hInt hMeas 0 ξ‖
            ≤
          ‖h3BKMCanonicalCurl01Amplitude
              hInt hMeas ξ‖
            +
          ‖h3BKMCanonicalCurl02Amplitude
              hInt hMeas ξ‖
      )
      ∧
      (
        ∀ i : Fin 3,
          ‖h3FourierDerivativeSymbol i ξ *
              velocityH3BaseFourierAt
                u t hInt hMeas 1 ξ‖
            ≤
          ‖h3BKMCanonicalCurl01Amplitude
              hInt hMeas ξ‖
            +
          ‖h3BKMCanonicalCurl12Amplitude
              hInt hMeas ξ‖
      )
      ∧
      (
        ∀ i : Fin 3,
          ‖h3FourierDerivativeSymbol i ξ *
              velocityH3BaseFourierAt
                u t hInt hMeas 2 ξ‖
            ≤
          ‖h3BKMCanonicalCurl02Amplitude
              hInt hMeas ξ‖
            +
          ‖h3BKMCanonicalCurl12Amplitude
              hInt hMeas ξ‖
      ) := by

  filter_upwards [
    velocityH3BaseFourier_gradient_component0_le_pairwiseCurl_ae
      hNS ht hFourier,
    velocityH3BaseFourier_gradient_component1_le_pairwiseCurl_ae
      hNS ht hFourier,
    velocityH3BaseFourier_gradient_component2_le_pairwiseCurl_ae
      hNS ht hFourier
  ] with ξ h0 h1 h2

  exact
    ⟨
      h0,
      h1,
      h2
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
