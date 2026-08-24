import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.FinHeatLeraySpectralRoundTrip

/-!
# Realizable weighted spectral H³ velocity states

The spectral Picard problem is solved in a complex weighted Fourier space, while
physical velocity data are real.  The previous decoder and round-trip files give
an exact way to state the missing range condition without introducing a second
Fourier transform convention.

A weighted spectral scalar state is called `realizable` when its exact complex
inverse-Fourier decoder is already the complexification of its own real part.
Equivalently, the decoded complex physical `L²` field has no imaginary part.
This is the physical-space form of the usual Fourier conjugate-symmetry
condition.

This file packages that invariant, proves that every genuine H³ spectral
snapshot produced by the existing encoder satisfies it, and exposes the
canonical real decoded state together with its norm control.  No claim is made
here yet that the nonlinear heat--Leray Picard map preserves realizability; that
is the next invariant theorem.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3SpectralRealizability
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Real physical decoded states -/

/-- Real scalar `L²` on the Euclidean physical carrier.  The carrier is the
same Euclidean space used by the Fourier isometry; after inverse transform the
interpretation is physical rather than frequency space. -/
abbrev H3RealPhysicalScalarL2 : Type :=
  H3FourierRealL2

/-- Three-component real physical `L²` velocity state. -/
abbrev H3RealPhysicalVelocityL2 : Type :=
  Fin 3 → H3RealPhysicalScalarL2

/-- Canonical real projection of the exact complex spectral decoder. -/
noncomputable def h3SpectralScalarDecodeRealL2
    (G : H3SpectralScalarState) :
    H3RealPhysicalScalarL2 :=
  h3RealPartFourierL2 (h3SpectralScalarDecodeComplexL2 G)

/-- Canonical real projection of a decoded spectral velocity state. -/
noncomputable def h3SpectralVelocityDecodeRealL2
    (U : H3SpectralVelocityState) :
    H3RealPhysicalVelocityL2 :=
  fun j => h3SpectralScalarDecodeRealL2 (U j)

@[simp]
theorem h3SpectralVelocityDecodeRealL2_apply
    (U : H3SpectralVelocityState)
    (j : Fin 3) :
    h3SpectralVelocityDecodeRealL2 U j
      =
    h3SpectralScalarDecodeRealL2 (U j) :=
  rfl

/-- Real projection of the decoded scalar is controlled by the weighted
spectral H³ norm. -/
theorem norm_h3SpectralScalarDecodeRealL2_le
    (G : H3SpectralScalarState) :
    ‖h3SpectralScalarDecodeRealL2 G‖ ≤ ‖G‖ := by
  calc
    ‖h3SpectralScalarDecodeRealL2 G‖
        ≤ ‖h3SpectralScalarDecodeComplexL2 G‖ :=
      norm_h3RealPartFourierL2_le _
    _ ≤ ‖G‖ :=
      norm_h3SpectralScalarDecodeComplexL2_le G

/-- Each real-decoded velocity component is controlled by the spectral state
norm. -/
theorem norm_h3SpectralVelocityDecodeRealL2_apply_le
    (U : H3SpectralVelocityState)
    (j : Fin 3) :
    ‖h3SpectralVelocityDecodeRealL2 U j‖ ≤ ‖U‖ := by
  calc
    ‖h3SpectralVelocityDecodeRealL2 U j‖
        ≤ ‖U j‖ :=
      norm_h3SpectralScalarDecodeRealL2_le (U j)
    _ ≤ ‖U‖ :=
      h3SpectralVelocity_coordinate_norm_le U j

/-! ## Realizability predicate -/

/-- A weighted spectral scalar state is physically realizable when its exact
complex inverse-Fourier decoder equals the complexification of its real part. -/
def H3SpectralScalarRealizable
    (G : H3SpectralScalarState) : Prop :=
  h3SpectralScalarDecodeComplexL2 G
    =
  h3ComplexifyFourierL2 (h3SpectralScalarDecodeRealL2 G)

/-- A weighted spectral velocity state is realizable when every component is. -/
def H3SpectralVelocityRealizable
    (U : H3SpectralVelocityState) : Prop :=
  ∀ j : Fin 3, H3SpectralScalarRealizable (U j)

/-- For a realizable scalar state, complex decoding loses no information when
we pass through the canonical real decoder. -/
theorem h3SpectralScalarDecodeComplexL2_eq_complexify_real
    {G : H3SpectralScalarState}
    (hG : H3SpectralScalarRealizable G) :
    h3SpectralScalarDecodeComplexL2 G
      =
    h3ComplexifyFourierL2 (h3SpectralScalarDecodeRealL2 G) :=
  hG

/-- Coordinatewise form of realizability for velocity states. -/
theorem h3SpectralVelocityDecodeComplexL2_eq_complexify_real
    {U : H3SpectralVelocityState}
    (hU : H3SpectralVelocityRealizable U)
    (j : Fin 3) :
    h3SpectralVelocityDecodeComplexL2 U j
      =
    h3ComplexifyFourierL2 (h3SpectralVelocityDecodeRealL2 U j) := by
  exact hU j

/-! ## Genuine encoder states are realizable -/

/-- Every scalar component produced by the genuine H³ spectral encoder is
realizable. -/
theorem velocityH3SpectralScalarAt_realizable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j : Fin 3) :
    H3SpectralScalarRealizable
      (velocityH3SpectralScalarAt u t hInt hMeas hFourier j) := by
  unfold H3SpectralScalarRealizable h3SpectralScalarDecodeRealL2
  rw [
    h3SpectralScalarDecodeComplexL2_velocityH3SpectralScalarAt_eq
      hFourier j,
    h3RealPartFourierL2_complexify_eq
  ]

/-- Every genuine encoded H³ velocity snapshot lies in the realizable spectral
subspace. -/
theorem velocityH3SpectralStateAt_realizable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    H3SpectralVelocityRealizable
      (velocityH3SpectralStateAt u t hInt hMeas hFourier) := by
  intro j
  change
    H3SpectralScalarRealizable
      (velocityH3SpectralScalarAt u t hInt hMeas hFourier j)
  exact velocityH3SpectralScalarAt_realizable hFourier j

/-- On a genuine encoded snapshot, the canonical real decoder is exactly the
transported zeroth-order real velocity component already identified by the
round-trip theorem. -/
theorem h3SpectralVelocityDecodeRealL2_velocityH3SpectralStateAt_apply_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j : Fin 3) :
    h3SpectralVelocityDecodeRealL2
        (velocityH3SpectralStateAt u t hInt hMeas hFourier) j
      =
    h3ToFourierRealL2
      (velocityH3L2JetAt u t hInt hMeas (h3JetSlot0 j)) := by
  change
    h3RealPartFourierL2
      (h3SpectralScalarDecodeComplexL2
        (velocityH3SpectralScalarAt u t hInt hMeas hFourier j))
      = _
  exact
    h3RealPartFourierL2_h3SpectralScalarDecodeComplexL2_velocityH3SpectralScalarAt_eq
      hFourier j

/-! ## The selected solution always has a canonical real projection -/

/-- Real projection of the decoded Banach-selected physical-time solution.  It
is defined unconditionally; once realizability of the Picard solution is
proved, this projection is the exact physical solution rather than merely its
real part. -/
noncomputable def h3SpectralFinHeatLerayPhysicalDecodedRealL2
    {ν τ A : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hsmall :
      8 * h3HeatLerayDuhamelPathCoefficient ν * A * Real.sqrt τ ≤ 1)
    (q : Set.Icc (0 : ℝ) τ) :
    H3RealPhysicalVelocityL2 :=
  h3SpectralVelocityDecodeRealL2
    (h3SpectralFinHeatLerayPhysicalMildSolution
      hν hτ U₀ hA hU₀ hsmall q)

@[simp]
theorem h3SpectralFinHeatLerayPhysicalDecodedRealL2_apply
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
    h3SpectralFinHeatLerayPhysicalDecodedRealL2
        hν hτ U₀ hA hU₀ hsmall q j
      =
    h3SpectralScalarDecodeRealL2
      (h3SpectralFinHeatLerayPhysicalMildSolution
        hν hτ U₀ hA hU₀ hsmall q j) :=
  rfl

/-- The same Banach ball estimate controls every component of the canonical
real decoded solution. -/
theorem norm_h3SpectralFinHeatLerayPhysicalDecodedRealL2_apply_le_twoA
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
    ‖h3SpectralFinHeatLerayPhysicalDecodedRealL2
        hν hτ U₀ hA hU₀ hsmall q j‖
      ≤ 2 * A := by
  calc
    ‖h3SpectralFinHeatLerayPhysicalDecodedRealL2
        hν hτ U₀ hA hU₀ hsmall q j‖
        ≤
      ‖h3SpectralFinHeatLerayPhysicalMildSolution
        hν hτ U₀ hA hU₀ hsmall q‖ :=
      norm_h3SpectralVelocityDecodeRealL2_apply_le
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
