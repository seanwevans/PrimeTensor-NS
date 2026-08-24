import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.FinHeatLerayPhysicalSolution
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.RawFourierL2

/-!
# Exact complex L² decoder for weighted spectral H³ states

A weighted spectral scalar state stores `W₃ * f̂`.  `RawFourierL2` already
constructs the deweighted amplitude `f̂` as an honest complex `L²` class.
This file applies Mathlib's inverse `L²` Fourier isometry to that raw state.

The result is an exact complex physical-space `L²` decoder for every spectral
state.  No reality claim is made here: an arbitrary complex spectral state
need not be the Fourier transform of a real field.  Reality/conjugate symmetry
is therefore left as an explicit invariant for the next layer.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform Set
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3SpectralDecoder
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Complex scalar `L²` on the Euclidean physical carrier.

The carrier is definitionally the same Euclidean space used by the Fourier
transform, but this alias records the physical-space interpretation after
inverse Fourier transform.
-/
abbrev H3ComplexPhysicalScalarL2 : Type :=
  H3FourierComplexL2

/-- Three-component complex physical `L²` velocity state. -/
abbrev H3ComplexPhysicalVelocityL2 : Type :=
  Fin 3 → H3ComplexPhysicalScalarL2

/--
Decode one weighted spectral H³ scalar state into complex physical `L²`:
first strip the exact H³ weight, then apply the inverse `L²` Fourier isometry.
-/
noncomputable def h3SpectralScalarDecodeComplexL2
    (G : H3SpectralScalarState) :
    H3ComplexPhysicalScalarL2 :=
  (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ).symm
    (h3SpectralScalarRawFourierL2 G)

/-- Fourier transforming the decoded state returns the exact deweighted state. -/
@[simp]
theorem h3Fourier_h3SpectralScalarDecodeComplexL2
    (G : H3SpectralScalarState) :
    (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ)
        (h3SpectralScalarDecodeComplexL2 G)
      =
    h3SpectralScalarRawFourierL2 G := by
  simp [h3SpectralScalarDecodeComplexL2]

/-- Inverse Fourier decoding preserves the raw `L²` norm exactly. -/
theorem norm_h3SpectralScalarDecodeComplexL2_eq
    (G : H3SpectralScalarState) :
    ‖h3SpectralScalarDecodeComplexL2 G‖
      =
    ‖h3SpectralScalarRawFourierL2 G‖ := by
  unfold h3SpectralScalarDecodeComplexL2
  exact
    (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ).symm.norm_map _

/-- Decoding is norm-controlled by the original weighted H³ state. -/
theorem norm_h3SpectralScalarDecodeComplexL2_le
    (G : H3SpectralScalarState) :
    ‖h3SpectralScalarDecodeComplexL2 G‖ ≤ ‖G‖ := by
  rw [norm_h3SpectralScalarDecodeComplexL2_eq]
  exact norm_h3SpectralScalarRawFourierL2_le G

/-- Decode a three-component weighted spectral velocity state coordinatewise. -/
noncomputable def h3SpectralVelocityDecodeComplexL2
    (U : H3SpectralVelocityState) :
    H3ComplexPhysicalVelocityL2 :=
  fun j => h3SpectralScalarDecodeComplexL2 (U j)

@[simp]
theorem h3SpectralVelocityDecodeComplexL2_apply
    (U : H3SpectralVelocityState)
    (j : Fin 3) :
    h3SpectralVelocityDecodeComplexL2 U j
      =
    h3SpectralScalarDecodeComplexL2 (U j) :=
  rfl

/-- Each decoded physical component is controlled by the spectral state norm. -/
theorem norm_h3SpectralVelocityDecodeComplexL2_apply_le
    (U : H3SpectralVelocityState)
    (j : Fin 3) :
    ‖h3SpectralVelocityDecodeComplexL2 U j‖ ≤ ‖U‖ := by
  calc
    ‖h3SpectralVelocityDecodeComplexL2 U j‖
        ≤ ‖U j‖ :=
      norm_h3SpectralScalarDecodeComplexL2_le (U j)
    _ ≤ ‖U‖ :=
      h3SpectralVelocity_coordinate_norm_le U j

/-- The Fourier transform of every decoded velocity component is exactly the
corresponding raw (deweighted) spectral component. -/
@[simp]
theorem h3Fourier_h3SpectralVelocityDecodeComplexL2_apply
    (U : H3SpectralVelocityState)
    (j : Fin 3) :
    (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ)
        (h3SpectralVelocityDecodeComplexL2 U j)
      =
    h3SpectralScalarRawFourierL2 (U j) := by
  exact h3Fourier_h3SpectralScalarDecodeComplexL2 (U j)

/-- Decode the Banach-selected physical-time spectral mild solution at one
physical time.  This is an unconditional complex `L²` realization. -/
noncomputable def h3SpectralFinHeatLerayPhysicalDecodedComplexL2
    {ν τ A : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hsmall :
      8 * h3HeatLerayDuhamelPathCoefficient ν * A * Real.sqrt τ ≤ 1)
    (q : Set.Icc (0 : ℝ) τ) :
    H3ComplexPhysicalVelocityL2 :=
  h3SpectralVelocityDecodeComplexL2
    (h3SpectralFinHeatLerayPhysicalMildSolution
      hν hτ U₀ hA hU₀ hsmall q)

@[simp]
theorem h3SpectralFinHeatLerayPhysicalDecodedComplexL2_apply
    {ν τ A : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hsmall :
      8 * h3HeatLerayDuhamelPathCoefficient ν * A * Real.sqrt τ ≤ 1)
    (q : Set.Icc (0 : ℝ) τ)
    (j : Fin 3) :
    h3SpectralFinHeatLerayPhysicalDecodedComplexL2
        hν hτ U₀ hA hU₀ hsmall q j
      =
    h3SpectralScalarDecodeComplexL2
      (h3SpectralFinHeatLerayPhysicalMildSolution
        hν hτ U₀ hA hU₀ hsmall q j) :=
  rfl

/-- The inherited Banach ball bound controls every decoded complex physical
`L²` velocity component. -/
theorem norm_h3SpectralFinHeatLerayPhysicalDecodedComplexL2_apply_le_twoA
    {ν τ A : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hsmall :
      8 * h3HeatLerayDuhamelPathCoefficient ν * A * Real.sqrt τ ≤ 1)
    (q : Set.Icc (0 : ℝ) τ)
    (j : Fin 3) :
    ‖h3SpectralFinHeatLerayPhysicalDecodedComplexL2
        hν hτ U₀ hA hU₀ hsmall q j‖
      ≤ 2 * A := by
  calc
    ‖h3SpectralFinHeatLerayPhysicalDecodedComplexL2
        hν hτ U₀ hA hU₀ hsmall q j‖
        ≤
      ‖h3SpectralFinHeatLerayPhysicalMildSolution
        hν hτ U₀ hA hU₀ hsmall q‖ :=
      norm_h3SpectralVelocityDecodeComplexL2_apply_le
        (h3SpectralFinHeatLerayPhysicalMildSolution
          hν hτ U₀ hA hU₀ hsmall q)
        j
    _ ≤ 2 * A :=
      norm_h3SpectralFinHeatLerayPhysicalMildSolution_apply_le_twoA
        hν hτ U₀ hA hU₀ hsmall q

end

end Euclidean
end Bridge
end PrimeTensor
