import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SpectralEndpointInterpolationAlgebra

/-!
# Classicalization: endpoint estimate for weighted spectral differences

`SpectralEndpointInterpolationAlgebra` isolated the scalar inequality

    1 + r + r² + r³ ≤ 3 (1 + r³),    r ≥ 0.

The H³ Sobolev Fourier weight is defined natively through
`h3FourierGradientSquare`.  Applying the scalar inequality directly at

    r = h3FourierGradientSquare ξ

gives a pointwise estimate for the complete weighted spectral difference in
terms of only the zeroth and cubic endpoint energies.

This native formulation is intentionally aligned with the already-compiled
symbol identities `sum_norm_h3FourierDerivativeSymbol_sq` and
`sum_norm_h3FourierDerivativeSymbol3_sq`.  The next bridge can therefore
replace the cubic endpoint term directly by the finite ordered third-symbol
square sum.

No Navier--Stokes evolution theorem is used here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

/-- Use the same axis `Fintype` as the H³ Fourier moment/classicalization
files.  This supplies the finite symbol sums and the product structures used
by `H3FourierPoint3`. -/
noncomputable local instance axisFintypeH3SchwartzClassicalizationSpectralEndpointDifferenceEstimate
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

/-- The complete H³ weighted Fourier difference is pointwise controlled by
three times the zeroth-plus-cubic endpoint energy, expressed in the native
gradient-square coordinate of the Sobolev encoder. -/
theorem h3SobolevFrequencyWeight_mul_sub_norm_sq_le_three_endpoint
    (ξ : H3FourierPoint3)
    (F G : ℂ) :
    ‖(h3SobolevFrequencyWeight ξ : ℂ) * F
        -
      (h3SobolevFrequencyWeight ξ : ℂ) * G‖ ^ 2
      ≤
    3 *
      (‖F - G‖ ^ 2
        +
       h3FourierGradientSquare ξ ^ 3 * ‖F - G‖ ^ 2) := by
  have hr :
      0 ≤ h3FourierGradientSquare ξ := by
    rw [← sum_norm_h3FourierDerivativeSymbol_sq ξ]
    positivity

  have hEndpoint :=
    h3_radial_complex_norm_sq_full_weight_le_three_endpoint_weight
      (h3FourierGradientSquare ξ)
      hr
      (F - G)

  rw [← mul_sub]
  simp_rw [norm_mul, mul_pow]

  have hW :
      0 ≤ h3SobolevFrequencyWeight ξ :=
    le_of_lt (h3SobolevFrequencyWeight_pos ξ)

  simp only [
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg hW
  ]

  rw [h3SobolevFrequencyWeight_sq]
  unfold h3SobolevFrequencyWeightSq

  ring_nf at hEndpoint ⊢
  exact hEndpoint

end

end Euclidean
end Bridge
end PrimeTensor
