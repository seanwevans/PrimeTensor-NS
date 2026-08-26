import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Spectral.Heat.Reality.Symbol
import Mathlib.MeasureTheory.Group.Prod

/-!
# L² Hermitian reality for the H³ spectral heat flow

The scalar heat-symbol file proves the exact pointwise algebra: the multiplier
is real and even, hence preserves Hermitian symmetry.  The only extra issue for
`L²` classes is that their pointwise formulas hold almost everywhere.

Negation on the Euclidean Fourier carrier is quasi-measure-preserving for
volume, so any a.e. formula may also be used at `-ξ`.  This file packages that
single measure-theoretic step and lifts the pointwise heat result to complex
Fourier `L²`.

No Fourier inversion/reality equivalence is asserted here yet.  The next layer
can identify this a.e. Hermitian condition with the decoder-based realizability
predicate.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

noncomputable local instance axisFintypeH3SpectralHeatRealityL2
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Reflection preserves almost-everywhere statements -/

/-- Any volume-a.e. property on the Euclidean Fourier carrier also holds after
frequency reflection `ξ ↦ -ξ`. -/
theorem h3Fourier_ae_neg
    {p : H3FourierPoint3 → Prop}
    (hp : ∀ᵐ ξ : H3FourierPoint3 ∂volume, p ξ) :
    ∀ᵐ ξ : H3FourierPoint3 ∂volume, p (-ξ) := by
  exact
    (MeasureTheory.quasiMeasurePreserving_neg
      (volume : Measure H3FourierPoint3)).ae hp

/-! ## Hermitian `L²` states -/

/-- A complex Fourier `L²` state is Hermitian when its canonical representative
satisfies the Fourier reality relation almost everywhere. -/
def H3FourierL2Hermitian
    (F : H3FourierComplexL2) : Prop :=
  ∀ᵐ ξ : H3FourierPoint3 ∂volume,
    F (-ξ) = conj (F ξ)

/-- The frequency-space heat multiplier preserves a.e. Hermitian symmetry. -/
theorem h3HeatFrequencyApplyNN_preserves_hermitian
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : ℝ≥0)
    {F : H3FourierComplexL2}
    (hF : H3FourierL2Hermitian F) :
    H3FourierL2Hermitian
      (h3HeatFrequencyApplyNN ν hν t F) := by
  unfold H3FourierL2Hermitian at hF ⊢
  have hHeat := h3HeatFrequencyApplyNN_coeFn ν hν t F
  have hHeatNeg :
      ∀ᵐ ξ : H3FourierPoint3 ∂volume,
        h3HeatFrequencyApplyNN ν hν t F (-ξ)
          =
        h3HeatFourierSymbol ν (t : ℝ) (-ξ) * F (-ξ) := by
    exact h3Fourier_ae_neg hHeat
  filter_upwards [hHeat, hHeatNeg, hF] with ξ hAt hNeg hHerm
  rw [hNeg, hAt, hHerm]
  exact h3HeatFourierSymbol_mul_conj ν (t : ℝ) ξ (F ξ)

/-! ## Weighted spectral states -/

/-- Hermitian reality of the exact deweighted Fourier representative of one
weighted H³ spectral scalar state. -/
def H3SpectralScalarRawHermitian
    (G : H3SpectralScalarState) : Prop :=
  H3FourierL2Hermitian (h3SpectralScalarRawFourierL2 G)

/-- Hermitian reality of every deweighted component of a weighted H³ spectral
velocity state. -/
def H3SpectralVelocityRawHermitian
    (U : H3SpectralVelocityState) : Prop :=
  ∀ j : Fin 3, H3SpectralScalarRawHermitian (U j)

/-- Weighted scalar heat evolution preserves Hermitian reality after exact
Sobolev deweighting. -/
theorem h3SpectralScalarHeatApplyNN_preserves_rawHermitian
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : ℝ≥0)
    {G : H3SpectralScalarState}
    (hG : H3SpectralScalarRawHermitian G) :
    H3SpectralScalarRawHermitian
      (h3SpectralScalarHeatApplyNN ν hν t G) := by
  unfold H3SpectralScalarRawHermitian at hG ⊢
  rw [h3SpectralScalarRawFourierL2_heatApplyNN]
  exact h3HeatFrequencyApplyNN_preserves_hermitian ν hν t hG

/-- Coordinatewise weighted velocity heat evolution preserves Hermitian
reality after exact Sobolev deweighting. -/
theorem h3SpectralVelocityHeatApplyNN_preserves_rawHermitian
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : ℝ≥0)
    {U : H3SpectralVelocityState}
    (hU : H3SpectralVelocityRawHermitian U) :
    H3SpectralVelocityRawHermitian
      (h3SpectralVelocityHeatApplyNN ν hν t U) := by
  intro j
  change
    H3SpectralScalarRawHermitian
      (h3SpectralScalarHeatApplyNN ν hν t (U j))
  exact
    h3SpectralScalarHeatApplyNN_preserves_rawHermitian
      ν hν t (hU j)

end

end Euclidean
end Bridge
end PrimeTensor
