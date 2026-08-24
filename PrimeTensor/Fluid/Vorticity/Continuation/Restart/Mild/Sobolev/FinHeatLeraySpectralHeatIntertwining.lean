import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.FinHeatLeraySpectralRealizabilityClosure
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.SpectralHeatSemigroup

/-!
# Exact decoder intertwining for spectral H³ heat evolution

The realizability closure layer isolates the linear algebra of the real spectral
subspace.  Before proving that heat preserves that subspace, we remove the H³
weight from the problem completely.

Because the Sobolev weight and the heat symbol are scalar Fourier multipliers,
deweighting commutes exactly with spectral heat evolution.  Applying inverse
Fourier transform then gives the exact identity

    decode (H_t G) = heatComplex_t (decode G).

Thus the remaining reality-preservation theorem is purely a statement about the
already-existing complex physical-space heat operator.  No weighted H³
bookkeeping remains in that step.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter FourierTransform
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3SpectralHeatIntertwining
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Deweighting commutes with heat -/

/--
Stripping the exact H³ Sobolev weight after spectral heat evolution is the same
as applying the ordinary Fourier heat multiplier to the stripped state.
-/
@[simp]
theorem h3SpectralScalarRawFourierL2_heatApplyNN
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : ℝ≥0)
    (G : H3SpectralScalarState) :
    h3SpectralScalarRawFourierL2
        (h3SpectralScalarHeatApplyNN ν hν t G)
      =
    h3HeatFrequencyApplyNN ν hν t
      (h3SpectralScalarRawFourierL2 G) := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    h3SpectralScalarRawFourierL2_ae
      (h3SpectralScalarHeatApplyNN ν hν t G),
    h3HeatFrequencyApplyNN_coeFn ν hν t G,
    h3HeatFrequencyApplyNN_coeFn
      ν hν t (h3SpectralScalarRawFourierL2 G),
    h3SpectralScalarRawFourierL2_ae G
  ] with ξ hRawHeat hHeatG hHeatRaw hRawG
  rw [hRawHeat, hHeatRaw]
  unfold h3SpectralScalarRawFourier
  unfold h3SpectralScalarHeatApplyNN
  rw [hHeatG, hRawG]
  unfold h3SpectralScalarRawFourier
  ac_rfl

/-! ## Exact inverse-Fourier intertwining -/

/--
The exact complex decoder intertwines weighted spectral heat evolution with the
existing complex physical-space heat evolution.
-/
@[simp]
theorem h3SpectralScalarDecodeComplexL2_heatApplyNN
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : ℝ≥0)
    (G : H3SpectralScalarState) :
    h3SpectralScalarDecodeComplexL2
        (h3SpectralScalarHeatApplyNN ν hν t G)
      =
    h3ComplexHeatApplyNN ν hν t
      (h3SpectralScalarDecodeComplexL2 G) := by
  unfold h3SpectralScalarDecodeComplexL2
  unfold h3ComplexHeatApplyNN h3ComplexHeatApply
  rw [h3SpectralScalarRawFourierL2_heatApplyNN]
  unfold h3HeatFrequencyApplyNN
  simp

/-- Coordinatewise velocity version of decoder/heat intertwining. -/
theorem h3SpectralVelocityDecodeComplexL2_heatApplyNN
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : ℝ≥0)
    (U : H3SpectralVelocityState)
    (j : Fin 3) :
    h3SpectralVelocityDecodeComplexL2
        (h3SpectralVelocityHeatApplyNN ν hν t U) j
      =
    h3ComplexHeatApplyNN ν hν t
      (h3SpectralVelocityDecodeComplexL2 U j) := by
  change
    h3SpectralScalarDecodeComplexL2
        (h3SpectralScalarHeatApplyNN ν hν t (U j))
      =
    h3ComplexHeatApplyNN ν hν t
      (h3SpectralScalarDecodeComplexL2 (U j))
  exact h3SpectralScalarDecodeComplexL2_heatApplyNN ν hν t (U j)

end

end Euclidean
end Bridge
end PrimeTensor
