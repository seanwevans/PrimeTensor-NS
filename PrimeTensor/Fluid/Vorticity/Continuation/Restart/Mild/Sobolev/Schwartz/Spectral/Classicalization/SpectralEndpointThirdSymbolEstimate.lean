import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SpectralEndpointDifferenceEstimate

/-!
# Classicalization: third-symbol endpoint estimate for spectral differences

`SpectralEndpointDifferenceEstimate` controls the complete weighted H³ Fourier
difference by the zeroth term and the cubic power of
`h3FourierGradientSquare`.

The cubic frequency factor is not an additional analytic quantity.  The
already-compiled third-symbol identity says that it is exactly the finite
ordered square sum of the third derivative symbols.  Multiplying that identity
by the squared base Fourier difference therefore gives

    (gradientSquare ξ)^3 |F-G|²
      =
    Σᵢₖₗ |symbol₃(i,k,l,ξ) (F-G)|².

Substituting this into the endpoint estimate produces the pointwise form needed
for Fourier compatibility: complete weighted H³ difference is controlled by
only the base difference and the ordered third-jet symbol differences.

No Navier--Stokes evolution theorem is used here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

/-- Keep the Fourier carrier and finite symbol sums definitionally aligned with
the generic moment algebra used by the existing symbol identities. -/
noncomputable local instance axisFintypeH3SchwartzClassicalizationSpectralEndpointThirdSymbolEstimate
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

/-- The cubic endpoint density is exactly the ordered third-derivative symbol
square density of the base Fourier difference. -/
theorem h3FourierGradientSquare_cube_mul_sub_norm_sq_eq_sum_symbol3
    (ξ : H3FourierPoint3)
    (F G : ℂ) :
    h3FourierGradientSquare ξ ^ 3 * ‖F - G‖ ^ 2
      =
    ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
      ‖h3FourierDerivativeSymbol3 i k l ξ * (F - G)‖ ^ 2 := by
  rw [← sum_norm_h3FourierDerivativeSymbol3_sq ξ]
  simp_rw [norm_mul, mul_pow]
  simp_rw [← Finset.sum_mul]

/-- Pointwise endpoint interpolation in the exact ordered third-symbol
coordinate required by Fourier compatibility. -/
theorem h3SobolevFrequencyWeight_mul_sub_norm_sq_le_three_base_third_symbol
    (ξ : H3FourierPoint3)
    (F G : ℂ) :
    ‖(h3SobolevFrequencyWeight ξ : ℂ) * F
        -
      (h3SobolevFrequencyWeight ξ : ℂ) * G‖ ^ 2
      ≤
    3 *
      (‖F - G‖ ^ 2
        +
       ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
         ‖h3FourierDerivativeSymbol3 i k l ξ * (F - G)‖ ^ 2) := by
  calc
    ‖(h3SobolevFrequencyWeight ξ : ℂ) * F
        -
      (h3SobolevFrequencyWeight ξ : ℂ) * G‖ ^ 2
        ≤
      3 *
        (‖F - G‖ ^ 2
          +
         h3FourierGradientSquare ξ ^ 3 * ‖F - G‖ ^ 2) :=
      h3SobolevFrequencyWeight_mul_sub_norm_sq_le_three_endpoint
        ξ F G
    _ =
      3 *
        (‖F - G‖ ^ 2
          +
         ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
           ‖h3FourierDerivativeSymbol3 i k l ξ * (F - G)‖ ^ 2) := by
      rw [h3FourierGradientSquare_cube_mul_sub_norm_sq_eq_sum_symbol3]

end

end Euclidean
end Bridge
end PrimeTensor
