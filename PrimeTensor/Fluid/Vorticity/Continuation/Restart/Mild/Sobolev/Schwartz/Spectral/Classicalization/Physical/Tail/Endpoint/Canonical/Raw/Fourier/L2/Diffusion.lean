import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Raw.Fourier.L2.Identification
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Diffusion.Fourier

/-!
# Classicalization: quotient-safe endpoint diffusion in raw Fourier L²

`PhysicalTailEndpointCanonicalRawFourierL2Identification` identifies exact H³
deweighting of the endpoint canonical path with the old solution's zeroth-order
Plancherel state.

The old H³ snapshot already contains each diagonal second spatial derivative as
a genuine Fourier `L²` jet slot.  This file packages the three diagonal slots

    F(∂₁∂₁ uⱼ) + F(∂₂∂₂ uⱼ) + F(∂₃∂₃ uⱼ)

as one quotient-safe Fourier `L²` Laplacian state.

The existing diffusion-symbol theorem says almost everywhere that the
pointwise sum of those three slot representatives is

    -|2πξ|² ûⱼ(ξ).

Combining that theorem with the standard `Lp.coeFn_add` representative
equalities gives the same statement for the packaged `L²` sum itself.  The
raw-Fourier identification then rewrites `ûⱼ` as exact deweighting of the
endpoint canonical spectral path.

No time derivative, pressure elimination, nonlinear forcing identity, or
fixed-frequency evaluation is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology BigOperators

noncomputable section

noncomputable local instance axisFintypeH3PhysicalTailEndpointCanonicalRawFourierL2Diffusion
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Quotient-safe Fourier `L²` Laplacian of one old-solution velocity
coordinate at an elapsed preterminal time. -/
noncomputable def h3PreterminalTailCanonicalVelocityLaplacianFourierL2OnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (j : Fin 3) :
    H3FourierComplexL2 :=
  h3PreterminalCanonicalFourierJetOnElapsed
      hNS ht hEnd hTail (h3JetSlot2 j 0 0) q
    +
  h3PreterminalCanonicalFourierJetOnElapsed
      hNS ht hEnd hTail (h3JetSlot2 j 1 1) q
    +
  h3PreterminalCanonicalFourierJetOnElapsed
      hNS ht hEnd hTail (h3JetSlot2 j 2 2) q

/-- The packaged Fourier `L²` Laplacian has the expected heat multiplier
representative almost everywhere. -/
theorem h3PreterminalTailCanonicalVelocityLaplacianFourierL2OnElapsed_ae
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (j : Fin 3) :
    ((h3PreterminalTailCanonicalVelocityLaplacianFourierL2OnElapsed
        hNS ht hEnd hTail q j : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun xi : H3FourierPoint3 =>
      -(h3FourierGradientSquare xi : ℂ) *
        velocityH3BaseFourierAt
          u
          (t + (q : ℝ))
          (h3PreterminalTailIntegrableOnElapsed hEnd hTail q)
          (h3PreterminalTailMeasurableOnElapsed
            hNS ht hEnd hTail q)
          j xi) := by
  let A0 : H3FourierComplexL2 :=
    h3PreterminalCanonicalFourierJetOnElapsed
      hNS ht hEnd hTail (h3JetSlot2 j 0 0) q
  let A1 : H3FourierComplexL2 :=
    h3PreterminalCanonicalFourierJetOnElapsed
      hNS ht hEnd hTail (h3JetSlot2 j 1 1) q
  let A2 : H3FourierComplexL2 :=
    h3PreterminalCanonicalFourierJetOnElapsed
      hNS ht hEnd hTail (h3JetSlot2 j 2 2) q

  have h01 :=
    MeasureTheory.Lp.coeFn_add A0 A1

  have h012 :=
    MeasureTheory.Lp.coeFn_add (A0 + A1) A2

  have hLap :=
    velocityH3FourierCompatibleAt_laplacian_ae
      (h3PreterminalTailFourierCompatibleOnElapsed
        hNS ht hEnd hTail q)
      j

  filter_upwards [h01, h012, hLap] with xi h01xi h012xi hLapxi

  have h01xi' :
      ((A0 + A1 : H3FourierComplexL2) : H3FourierPoint3 → ℂ) xi
        =
      (A0 : H3FourierPoint3 → ℂ) xi
        +
      (A1 : H3FourierPoint3 → ℂ) xi := by
    simpa only [Pi.add_apply] using h01xi

  have h012xi' :
      ((A0 + A1 + A2 : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ) xi
        =
      ((A0 + A1 : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ) xi
        +
      (A2 : H3FourierPoint3 → ℂ) xi := by
    simpa only [Pi.add_apply] using h012xi

  calc
    ((A0 + A1 + A2 : H3FourierComplexL2) xi)
        =
      ((A0 + A1 : H3FourierComplexL2) xi) + A2 xi :=
      h012xi'
    _ =
      (A0 xi + A1 xi) + A2 xi := by
        rw [h01xi']
    _ =
      -(h3FourierGradientSquare xi : ℂ) *
        velocityH3BaseFourierAt
          u
          (t + (q : ℝ))
          (h3PreterminalTailIntegrableOnElapsed hEnd hTail q)
          (h3PreterminalTailMeasurableOnElapsed
            hNS ht hEnd hTail q)
          j xi := by
        simpa only [
          A0,
          A1,
          A2,
          h3PreterminalCanonicalFourierJetOnElapsed,
          Fin.sum_univ_three
        ] using hLapxi

/-- On the actual endpoint canonical physical path, the quotient-safe
Laplacian is almost everywhere `-|2πξ|²` times exact H³ deweighting of the
path state. -/
theorem h3PreterminalTailCanonicalVelocityLaplacianFourierL2OnElapsed_ae_eq_endpointRawFourierL2
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (q : Set.Icc (0 : ℝ) tau)
    (j : Fin 3) :
    ((h3PreterminalTailCanonicalVelocityLaplacianFourierL2OnElapsed
        hNS ht hEnd hTail q j : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun xi : H3FourierPoint3 =>
      -(h3FourierGradientSquare xi : ℂ) *
        h3SpectralScalarRawFourierL2
          ((h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
            hNS ht hEnd hE hTail hEndpoint q) j)
          xi) := by
  have hLap :=
    h3PreterminalTailCanonicalVelocityLaplacianFourierL2OnElapsed_ae
      hNS ht hEnd hTail q j

  have hIdentify :=
    h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint_rawFourierL2_eq_baseFourierAt
      hNS ht hEnd hE hTail hEndpoint q j

  rw [← hIdentify] at hLap

  exact hLap

/-- The same multiplier identity written directly for the globally indexed
normalized real path at a physical time `s ∈ [0,τ]`. -/
theorem h3PreterminalTailCanonicalVelocityLaplacianFourierL2OnElapsed_ae_eq_normalizedRealPath
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (s : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) tau)
    (j : Fin 3) :
    ((h3PreterminalTailCanonicalVelocityLaplacianFourierL2OnElapsed
        hNS ht hEnd hTail ⟨s, hs⟩ j : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun xi : H3FourierPoint3 =>
      -(h3FourierGradientSquare xi : ℂ) *
        h3SpectralScalarRawFourierL2
          ((h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
            hNS ht htau.le hEnd hE hTail hEndpoint s) j)
          xi) := by
  have hLap :=
    h3PreterminalTailCanonicalVelocityLaplacianFourierL2OnElapsed_ae
      hNS ht hEnd hTail ⟨s, hs⟩ j

  have hIdentify :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_rawFourierL2_eq_baseFourierAt
      hNS ht htau hEnd hE hTail hEndpoint s hs j

  rw [← hIdentify] at hLap

  exact hLap

end

end Euclidean
end Bridge
end PrimeTensor
