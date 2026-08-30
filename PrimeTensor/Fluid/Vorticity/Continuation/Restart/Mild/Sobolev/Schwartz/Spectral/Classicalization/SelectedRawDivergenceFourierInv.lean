import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedRawFourierIncompressibility

/-!
# Vanishing inverse Fourier transform of the selected raw divergence

`SelectedRawFourierIncompressibility` removes the common H³ Sobolev weight and
shows that the genuine raw Fourier velocity of the canonical selected restart
satisfies

    Σ_j d_j(ξ) û_j(ξ) = 0

almost everywhere.

This file packages that sum as one scalar Fourier-side function and records the
immediate inverse-Fourier consequence: its inverse transform vanishes
everywhere.

This is deliberately separated from the spatial differentiation theorem.  The
next rung only has to identify the physical divergence of the smooth selected
representative with the real part of this already-zero inverse Fourier
transform.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3SelectedRawDivergenceFourierInv
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The raw Fourier divergence of a three-component weighted H³ spectral
state, after removing the common Sobolev weight coordinatewise. -/
noncomputable def h3SpectralFinRawDivergenceFourier
    (G : H3SpectralFinVectorState) :
    H3FourierPoint3 → ℂ :=
  fun ξ =>
    ∑ j : Fin 3,
      h3FourierDerivativeSymbol j ξ *
        h3SpectralScalarRawFourier (G j) ξ

/-- Raw spectral incompressibility is exactly almost-everywhere vanishing of
the packaged raw Fourier divergence function. -/
theorem h3SpectralFinRawDivergenceFourier_ae_eq_zero
    {G : H3SpectralFinVectorState}
    (hG : H3SpectralFinRawDivergenceFree G) :
    h3SpectralFinRawDivergenceFourier G
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (0 : H3FourierPoint3 → ℂ) := by
  filter_upwards [hG] with ξ hξ
  unfold h3SpectralFinRawDivergenceFourier
  exact hξ

/-- The inverse Fourier transform of the raw divergence of a divergence-free
H³ spectral state vanishes pointwise everywhere.

No integrability hypothesis is needed here: the ordinary Fourier integral is
defined as a total operator, and Mathlib's inverse Fourier transform respects
almost-everywhere equality. -/
theorem h3SpectralFinRawDivergenceFourierInv_eq_zero
    {G : H3SpectralFinVectorState}
    (hG : H3SpectralFinRawDivergenceFree G)
    (x : H3FourierPoint3) :
    FourierTransformInv.fourierInv
        (h3SpectralFinRawDivergenceFourier G)
        x
      =
    0 := by
  have hCongr :=
    Real.fourierInv_congr_ae
      (h3SpectralFinRawDivergenceFourier_ae_eq_zero hG)
      x

  have hZero :
      FourierTransformInv.fourierInv
          (0 : H3FourierPoint3 → ℂ)
          x
        =
      0 := by
    rw [Real.fourierInv_eq_fourier_neg]
    simp [Real.fourier_eq]

  exact hCongr.trans hZero

/-- The canonical selected restart therefore has identically zero inverse
Fourier raw divergence at every time in the full restart interval. -/
theorem h3PreterminalTailCanonicalSelectedRestart_rawDivergenceFourierInv_eq_zero
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    {s : ℝ}
    (hs0 : 0 ≤ s)
    (hsR : s ≤ h3FinHeatLerayRestartRadius ν E)
    (x : H3FourierPoint3) :
    FourierTransformInv.fourierInv
        (h3SpectralFinRawDivergenceFourier
          (h3PreterminalTailCanonicalSelectedRestart
            hν hNS ht hE hTail s))
        x
      =
    0 := by
  exact
    h3SpectralFinRawDivergenceFourierInv_eq_zero
      (h3PreterminalTailCanonicalSelectedRestart_rawDivergenceFree
        hν hNS ht hE hTail hs0 hsR)
      x

/-- Positive half-open restart-window form for the selected smooth
inverse-Fourier representative. -/
theorem h3PreterminalTailCanonicalSelectedRestart_rawDivergenceFourierInv_eq_zeroOn_Ioc
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) :
    ∀ s : ℝ,
      s ∈ Set.Ioc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius ν E) →
      ∀ x : H3FourierPoint3,
        FourierTransformInv.fourierInv
            (h3SpectralFinRawDivergenceFourier
              (h3PreterminalTailCanonicalSelectedRestart
                hν hNS ht hE hTail s))
            x
          =
        0 := by
  intro s hs x

  exact
    h3PreterminalTailCanonicalSelectedRestart_rawDivergenceFourierInv_eq_zero
      hν hNS ht hE hTail
      hs.1.le
      hs.2
      x

end
end Euclidean
end Bridge
end PrimeTensor
