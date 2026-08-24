import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.FinHeatLeraySpectralHeatIntertwining

/-!
# Reality algebra of the H³ spectral heat symbol

The decoder intertwining theorem reduces spectral heat realizability to a
statement about the ordinary Fourier heat multiplier.  The remaining analytic
step lives in `L²`, but its scalar algebra is completely elementary: the heat
symbol is real and even in frequency.

This file isolates that algebra before any measure-theoretic reflection
bookkeeping.  In particular, multiplication by the heat symbol preserves the
usual pointwise Hermitian condition

    f (-ξ) = conj (f ξ).

The next layer can lift this identity through the volume-preserving reflection
`ξ ↦ -ξ` on the Euclidean Fourier carrier.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

noncomputable local instance axisFintypeH3SpectralHeatRealitySymbol
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Real and even heat symbol -/

/-- The scalar heat multiplier is even in frequency. -/
@[simp]
theorem h3HeatFourierSymbol_neg
    (ν t : ℝ)
    (ξ : H3FourierPoint3) :
    h3HeatFourierSymbol ν t (-ξ)
      =
    h3HeatFourierSymbol ν t ξ := by
  unfold h3HeatFourierSymbol
  simp

/-- The scalar heat multiplier is fixed by complex conjugation. -/
@[simp]
theorem conj_h3HeatFourierSymbol
    (ν t : ℝ)
    (ξ : H3FourierPoint3) :
    conj (h3HeatFourierSymbol ν t ξ)
      =
    h3HeatFourierSymbol ν t ξ := by
  unfold h3HeatFourierSymbol
  exact Complex.conj_ofReal _

/-- Combined scalar identity used by Hermitian-symmetry preservation. -/
@[simp]
theorem h3HeatFourierSymbol_mul_conj
    (ν t : ℝ)
    (ξ : H3FourierPoint3)
    (z : ℂ) :
    h3HeatFourierSymbol ν t (-ξ) * conj z
      =
    conj (h3HeatFourierSymbol ν t ξ * z) := by
  simp

/-! ## Pointwise Hermitian symmetry -/

/-- Pointwise form of the Fourier reality condition. -/
def H3FourierPointwiseHermitian
    (f : H3FourierPoint3 → ℂ) : Prop :=
  ∀ ξ : H3FourierPoint3, f (-ξ) = conj (f ξ)

/-- Multiplication by the real-even heat symbol preserves pointwise Hermitian
symmetry. -/
theorem h3HeatFourierMultiplier_preserves_pointwiseHermitian
    (ν t : ℝ)
    {f : H3FourierPoint3 → ℂ}
    (hf : H3FourierPointwiseHermitian f) :
    H3FourierPointwiseHermitian
      (fun ξ => h3HeatFourierSymbol ν t ξ * f ξ) := by
  intro ξ
  change
    h3HeatFourierSymbol ν t (-ξ) * f (-ξ)
      =
    conj (h3HeatFourierSymbol ν t ξ * f ξ)
  rw [hf ξ]
  exact h3HeatFourierSymbol_mul_conj ν t ξ (f ξ)

end

end Euclidean
end Bridge
end PrimeTensor
