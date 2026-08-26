import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Density
import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
# Smooth compact spectral density for the H³ solver state

`SchwartzSpectralDensity` records ordinary Schwartz density in the weighted
spectral `L²` state.  For the deweighting step we can use a stronger Mathlib
fact: finite-`p` `Lp` spaces are dense in functions admitting a smooth,
compactly-supported representative.

This is preferable to proving that the exact reciprocal Sobolev weight is a
global temperate multiplier.  If a weighted approximant has compact support,
then deweighting preserves compact support automatically, and only ordinary
smoothness of the reciprocal weight is needed to conclude that the deweighted
representative is Schwartz.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory
open scoped ENNReal ContDiff

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralCompactDensity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Smooth compactly-supported representatives are dense in the exact weighted
scalar H³ spectral state space.  The bundled state `F` is accompanied by an
actual function `g` representing it almost everywhere. -/
theorem exists_h3SmoothCompact_spectralApprox_dist
    (G : H3SpectralScalarState)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ F : H3SpectralScalarState,
      (∃ g : H3FourierPoint3 → ℂ,
        (F : H3FourierPoint3 → ℂ) =ᵐ[volume] g ∧
        HasCompactSupport g ∧
        ContDiff ℝ ∞ g) ∧
      dist G F < ε := by
  have hDense :
      Dense
        {F : H3SpectralScalarState |
          ∃ g : H3FourierPoint3 → ℂ,
            (F : H3FourierPoint3 → ℂ) =ᵐ[volume] g ∧
            HasCompactSupport g ∧
            ContDiff ℝ ∞ g} := by
    simpa using
      (MeasureTheory.Lp.dense_hasCompactSupport_contDiff
        (E := H3FourierPoint3)
        (F := ℂ)
        (μ := (volume : Measure H3FourierPoint3))
        (p := (2 : ENNReal))
        ENNReal.ofNat_ne_top)

  obtain ⟨F, hF, hdist⟩ := hDense.exists_dist_lt G hε
  exact ⟨F, hF, hdist⟩

/-- Norm form of smooth compact spectral density. -/
theorem exists_h3SmoothCompact_spectralApprox_norm
    (G : H3SpectralScalarState)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ F : H3SpectralScalarState,
      (∃ g : H3FourierPoint3 → ℂ,
        (F : H3FourierPoint3 → ℂ) =ᵐ[volume] g ∧
        HasCompactSupport g ∧
        ContDiff ℝ ∞ g) ∧
      ‖G - F‖ < ε := by
  simpa only [dist_eq_norm] using
    exists_h3SmoothCompact_spectralApprox_dist G hε

end

end Euclidean
end Bridge
end PrimeTensor
