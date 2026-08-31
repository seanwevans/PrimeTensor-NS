import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.CubicDifferenceInterpolation

/-!
# H³ inverse-Fourier point-evaluation bound

The selected spectral mild path is already continuous in the weighted H³
state norm.  To turn that Banach-space continuity into ordinary pointwise
continuity of the reconstructed physical velocity, we need a quantitative
zero-order evaluation map.

For a weighted H³ scalar state `G`, its classical representative is

    x ↦ 𝓕⁻¹[(1 + |ξ|²)^(-3/2) G(ξ)](x).

The Fourier integral is bounded pointwise by the `L¹` norm of its integrand,
and the existing H³ deweighting theorem controls that raw Fourier `L¹` mass by
the weighted H³ norm.  Hence

    ‖u_G(x)‖ ≤ C_dw ‖G‖

uniformly in `x`.

This is the zero-order companion to the already-established derivative
evaluation estimates.  It is the direct topology bridge needed for selected
physical-velocity time continuity.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

/-- Keep the Fourier-space norm and volume definitionally aligned with the
existing H³ deweighting/moment layer. -/
noncomputable local instance axisFintypeH3SchwartzClassicalizationC1PointEvaluationBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

/-- Point evaluation of the ordinary inverse-Fourier H³ representative is
bounded by the raw Fourier `L¹` mass. -/
theorem norm_h3SpectralScalarC1Representative_apply_le_rawFourierL1Mass
    (G : H3SpectralScalarState)
    (x : H3FourierPoint3) :
    ‖h3SpectralScalarC1Representative G x‖
      ≤
    h3SpectralScalarRawFourierL1Mass G := by
  unfold h3SpectralScalarC1Representative
  rw [
    Real.fourierInv_eq_fourier_neg
      (h3SpectralScalarRawFourier G)
      x
  ]

  change
    ‖VectorFourier.fourierIntegral
        Real.fourierChar
        (volume : Measure H3FourierPoint3)
        (innerₗ H3FourierPoint3)
        (h3SpectralScalarRawFourier G)
        (-x)‖
      ≤
    h3SpectralScalarRawFourierL1Mass G

  simpa only [
    h3SpectralScalarRawFourierL1Mass,
    axisFintypeH3SchwartzClassicalizationC1PointEvaluationBound,
    axisFintypeH3SchwartzFrechetInductionMomentAlgebra,
    axisFintypeH3SpectralL1,
    axisFintypeH3SchwartzNineQuarterConvolutionMajorantMass
  ] using
    (VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar
      (volume : Measure H3FourierPoint3)
      (innerₗ H3FourierPoint3)
      (h3SpectralScalarRawFourier G)
      (-x))

/-- Uniform H³-to-point-evaluation bound for the classical inverse-Fourier
representative. -/
theorem norm_h3SpectralScalarC1Representative_apply_le
    (G : H3SpectralScalarState)
    (x : H3FourierPoint3) :
    ‖h3SpectralScalarC1Representative G x‖
      ≤
    h3RawFourierL1DeweightingCoefficient * ‖G‖ := by
  exact
    (norm_h3SpectralScalarC1Representative_apply_le_rawFourierL1Mass
      G x).trans
      (h3SpectralScalarRawFourierL1Mass_le_norm G)

end
end Euclidean
end Bridge
end PrimeTensor
