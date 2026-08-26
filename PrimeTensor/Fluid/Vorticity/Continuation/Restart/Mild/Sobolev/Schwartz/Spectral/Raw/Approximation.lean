import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Compact.Deweighting
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Raw.Fourier.L2

/-!
# Raw Fourier Schwartz approximation from weighted H³ states

Smooth compact density is available in the weighted spectral H³ state, and
`SchwartzSpectralCompactDeweighting` turns each such representative into a genuine
Schwartz raw Fourier function.  This file closes the remaining topological bridge:
deweighting is contractive in `L²`, so weighted approximation implies raw Fourier
`L²` approximation by Schwartz functions.

No new harmonic-analysis estimate is introduced here.  The only analytic input is the
already-proved pointwise bound `W₃⁻¹ ≤ 1`, packaged by `RawFourierL2` as an `L²`
contraction.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped ENNReal ContDiff

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralRawApproximation
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Contractivity of bundled raw Fourier differences -/

/-- Raw Fourier `L²` distance is bounded by weighted spectral `L²` distance. -/
theorem norm_h3SpectralScalarRawFourierL2_sub_le
    (F G : H3SpectralScalarState) :
    ‖h3SpectralScalarRawFourierL2 F -
        h3SpectralScalarRawFourierL2 G‖
      ≤
    ‖F - G‖ := by
  rw [← h3SpectralScalarRawFourierL2_sub]
  exact norm_h3SpectralScalarRawFourierL2_le (F - G)

/-! ## Identification of a compact weighted approximant with its deweighted Schwartz function -/

/-- If a bundled weighted spectral state is represented by a smooth compact function `g`,
then its bundled raw Fourier `L²` state is exactly the `L²` package of the canonical
deweighted Schwartz function. -/
theorem h3SpectralScalarRawFourierL2_eq_deweightedSchwartz_toLp
    (F : H3SpectralScalarState)
    (g : H3FourierPoint3 → ℂ)
    (hF : (F : H3FourierPoint3 → ℂ) =ᵐ[volume] g)
    (hcompact : HasCompactSupport g)
    (hsmooth : ContDiff ℝ ∞ g) :
    h3SpectralScalarRawFourierL2 F
      =
    (h3SmoothCompactDeweightedSchwartz g hcompact hsmooth).toLp
      2 (volume : Measure H3FourierPoint3) := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    h3SpectralScalarRawFourierL2_ae F,
    hF,
    (h3SmoothCompactDeweightedSchwartz g hcompact hsmooth).coeFn_toLp
      2 (volume : Measure H3FourierPoint3)
  ] with ξ hRaw hRep hSchwartz
  rw [hRaw, hSchwartz]
  unfold h3SpectralScalarRawFourier
  rw [hRep]
  rfl

/-! ## Schwartz approximation of arbitrary raw Fourier states -/

/-- Every weighted H³ scalar state has raw Fourier amplitude approximable in `L²` by
Schwartz functions.  The approximation error is no larger than the weighted spectral
approximation error from smooth compact density. -/
theorem exists_h3Schwartz_rawFourierApprox_norm
    (G : H3SpectralScalarState)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ S : SchwartzMap H3FourierPoint3 ℂ,
      ‖h3SpectralScalarRawFourierL2 G -
          S.toLp 2 (volume : Measure H3FourierPoint3)‖ < ε := by
  obtain ⟨F, ⟨g, hF, hcompact, hsmooth⟩, hApprox⟩ :=
    exists_h3SmoothCompact_spectralApprox_norm G hε

  let S : SchwartzMap H3FourierPoint3 ℂ :=
    h3SmoothCompactDeweightedSchwartz g hcompact hsmooth

  have hRawF :
      h3SpectralScalarRawFourierL2 F
        =
      S.toLp 2 (volume : Measure H3FourierPoint3) := by
    simpa [S] using
      h3SpectralScalarRawFourierL2_eq_deweightedSchwartz_toLp
        F g hF hcompact hsmooth

  refine ⟨S, ?_⟩
  rw [← hRawF]
  exact
    (norm_h3SpectralScalarRawFourierL2_sub_le G F).trans_lt
      hApprox

/-- Distance form of raw Fourier Schwartz approximation. -/
theorem exists_h3Schwartz_rawFourierApprox_dist
    (G : H3SpectralScalarState)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ S : SchwartzMap H3FourierPoint3 ℂ,
      dist (h3SpectralScalarRawFourierL2 G)
          (S.toLp 2 (volume : Measure H3FourierPoint3)) < ε := by
  simpa only [dist_eq_norm] using
    exists_h3Schwartz_rawFourierApprox_norm G hε

end

end Euclidean
end Bridge
end PrimeTensor
