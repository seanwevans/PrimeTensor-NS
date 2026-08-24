import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.FinHeatLeraySpectralDuhamelReality
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.FinHeatLerayPicardSolution

/-!
# Hermitian reality of the finite heat--Leray Picard solution

The spatial and temporal analytic work is now complete: the free heat
semigroup preserves the exact raw-Hermitian invariant, and the genuine
retarded finite heat--Leray Duhamel operator preserves it as well.

This file wires those facts through the concrete normalized Picard map.
Starting from zero, every Picard iterate is raw-Hermitian whenever the restart
state is.  The abstract Banach theorem already proves that these iterates
converge in the normalized bounded-continuous path norm.

For the limit step we deliberately use the weighted Hermitian formulation.
Path convergence is sent through bounded-path evaluation and then through a
coordinate projection.  The weighted Fourier Hermitian subset is norm closed,
so every coordinate of every time slice of the Banach-selected limit remains
Hermitian.  The positive real even Sobolev weight then converts this back to
the exact deweighted raw-Hermitian invariant.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Interval ComplexConjugate

noncomputable section

noncomputable local instance axisFintypeH3SpectralPicardReality
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Reality as a path invariant -/

/-- Every normalized slice of a spectral velocity path is raw-Hermitian. -/
def H3SpectralVelocityPathRawHermitian
    (U : H3SpectralVelocityPath) : Prop :=
  ∀ s : H3UnitTime, H3SpectralVelocityRawHermitian (U s)

@[simp]
theorem h3SpectralVelocityPathRawHermitian_zero :
    H3SpectralVelocityPathRawHermitian
      (0 : H3SpectralVelocityPath) := by
  intro s
  change H3SpectralVelocityRawHermitian (0 : H3SpectralVelocityState)
  exact h3SpectralVelocityRawHermitian_zero

/-- Pointwise addition preserves the path invariant. -/
theorem H3SpectralVelocityPathRawHermitian.add
    {U V : H3SpectralVelocityPath}
    (hU : H3SpectralVelocityPathRawHermitian U)
    (hV : H3SpectralVelocityPathRawHermitian V) :
    H3SpectralVelocityPathRawHermitian (U + V) := by
  intro s
  change H3SpectralVelocityRawHermitian (U s + V s)
  exact (hU s).add (hV s)

/-! ## Free heat and physical extension -/

/-- The normalized free heat path preserves raw-Hermitian reality. -/
theorem h3SpectralVelocityHeatFreePath_preserves_rawHermitian
    {ν τ : ℝ}
    (hν : 0 ≤ ν)
    (hτ : 0 ≤ τ)
    {U₀ : H3SpectralVelocityState}
    (hU₀ : H3SpectralVelocityRawHermitian U₀) :
    H3SpectralVelocityPathRawHermitian
      (h3SpectralVelocityHeatFreePath ν τ hν hτ U₀) := by
  intro s
  rw [h3SpectralVelocityHeatFreePath_apply]
  exact
    h3SpectralVelocityHeatApplyNN_preserves_rawHermitian
      ν hν (h3PhysicalTimeNN τ hτ s) hU₀

/-- Rescaling and clamping a normalized real path does not change its reality
invariant. -/
theorem h3PathPhysicalRealExtension_preserves_rawHermitian
    {τ : ℝ}
    {U : H3SpectralVelocityPath}
    (hU : H3SpectralVelocityPathRawHermitian U)
    (q : ℝ) :
    H3SpectralVelocityRawHermitian
      (h3PathPhysicalRealExtension τ U q) := by
  unfold h3PathPhysicalRealExtension h3PathRealExtension
  exact hU (h3ClampUnitTime (q / τ))

/-! ## Concrete Duhamel path operator -/

/-- The concrete normalized Duhamel path operator preserves the path
raw-Hermitian invariant. -/
theorem h3SpectralFinHeatLerayDuhamelPathOperator_preserves_rawHermitian
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    {U V : H3SpectralVelocityPath}
    (hU : H3SpectralVelocityPathRawHermitian U)
    (hV : H3SpectralVelocityPathRawHermitian V) :
    H3SpectralVelocityPathRawHermitian
      (h3SpectralFinHeatLerayDuhamelPathOperator hν hτ U V) := by
  intro s
  unfold h3SpectralFinHeatLerayDuhamelPathOperator
  exact
    h3SpectralFinHeatLerayDuhamelPath_preserves_rawHermitian
      hν hτ
      (norm_nonneg U)
      (norm_nonneg V)
      (h3PathPhysicalRealExtension τ U)
      (h3PathPhysicalRealExtension τ V)
      (continuous_h3PathPhysicalRealExtension τ U)
      (continuous_h3PathPhysicalRealExtension τ V)
      (fun q => norm_h3PathPhysicalRealExtension_le τ U q)
      (fun q => norm_h3PathPhysicalRealExtension_le τ V q)
      (h3PathPhysicalRealExtension_preserves_rawHermitian hU)
      (h3PathPhysicalRealExtension_preserves_rawHermitian hV)
      s

/-- The totalized Duhamel family used by the abstract estimate package also
preserves reality for every real lifespan. -/
theorem h3SpectralFinHeatLerayDuhamelPathOperatorTotal_preserves_rawHermitian
    {ν τ : ℝ}
    (hν : 0 < ν)
    {U V : H3SpectralVelocityPath}
    (hU : H3SpectralVelocityPathRawHermitian U)
    (hV : H3SpectralVelocityPathRawHermitian V) :
    H3SpectralVelocityPathRawHermitian
      (h3SpectralFinHeatLerayDuhamelPathOperatorTotal hν τ U V) := by
  by_cases hτ : 0 ≤ τ
  · rw [h3SpectralFinHeatLerayDuhamelPathOperatorTotal_of_nonneg hν hτ]
    exact
      h3SpectralFinHeatLerayDuhamelPathOperator_preserves_rawHermitian
        hν hτ hU hV
  · simp only [h3SpectralFinHeatLerayDuhamelPathOperatorTotal, hτ, ↓reduceDIte]
    exact h3SpectralVelocityPathRawHermitian_zero

/-! ## Concrete mild map and its iterates -/

/-- One application of the actual concrete Picard map preserves the path
reality invariant. -/
theorem h3SpectralFinHeatLerayPicardMap_preserves_rawHermitian
    {ν τ A : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀bound : ‖U₀‖ ≤ A)
    (hsmall :
      8 * h3HeatLerayDuhamelPathCoefficient ν * A * Real.sqrt τ ≤ 1)
    (hU₀real : H3SpectralVelocityRawHermitian U₀)
    {U : H3SpectralVelocityPath}
    (hU : H3SpectralVelocityPathRawHermitian U) :
    H3SpectralVelocityPathRawHermitian
      (((h3SpectralFinHeatLerayEstimateData
          hν hτ U₀ hA hU₀bound).toMildQuadraticPicardData
            τ hτ
            (h3SpectralFinHeatLerayEstimateData_smallTime
              hν hτ U₀ hA hU₀bound hsmall)).map U) := by
  intro s
  change
    H3SpectralVelocityRawHermitian
      ((h3SpectralVelocityHeatFreePath ν τ hν.le hτ U₀) s +
        (h3SpectralFinHeatLerayDuhamelPathOperatorTotal hν τ U U) s)
  exact
    (h3SpectralVelocityHeatFreePath_preserves_rawHermitian
      hν.le hτ hU₀real s).add
    (h3SpectralFinHeatLerayDuhamelPathOperatorTotal_preserves_rawHermitian
      hν hU hU s)

/-- Every Picard iterate from zero is raw-Hermitian. -/
theorem h3SpectralFinHeatLerayPicardIterate_preserves_rawHermitian
    {ν τ A : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀bound : ‖U₀‖ ≤ A)
    (hsmall :
      8 * h3HeatLerayDuhamelPathCoefficient ν * A * Real.sqrt τ ≤ 1)
    (hU₀real : H3SpectralVelocityRawHermitian U₀)
    (n : ℕ) :
    H3SpectralVelocityPathRawHermitian
      (((h3SpectralFinHeatLerayEstimateData
          hν hτ U₀ hA hU₀bound).toMildQuadraticPicardData
            τ hτ
            (h3SpectralFinHeatLerayEstimateData_smallTime
              hν hτ U₀ hA hU₀bound hsmall)).map^[n]
        (0 : H3SpectralVelocityPath)) := by
  induction n with
  | zero =>
      simpa only [Function.iterate_zero_apply] using
        h3SpectralVelocityPathRawHermitian_zero
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact
        h3SpectralFinHeatLerayPicardMap_preserves_rawHermitian
          hν hτ U₀ hA hU₀bound hsmall hU₀real ih

/-! ## Closed-limit inheritance -/

/-- A norm limit of raw-Hermitian normalized velocity paths is raw-Hermitian.
The proof uses weighted Hermitian closedness coordinatewise and converts back
only after taking the limit. -/
theorem h3SpectralVelocityPathRawHermitian_of_tendsto
    {ι : Type*}
    {l : Filter ι}
    [l.NeBot]
    {U : ι → H3SpectralVelocityPath}
    {V : H3SpectralVelocityPath}
    (hUV : Tendsto U l (nhds V))
    (hU : ∀ᶠ i in l, H3SpectralVelocityPathRawHermitian (U i)) :
    H3SpectralVelocityPathRawHermitian V := by
  intro s
  apply h3SpectralVelocityHermitian_to_rawHermitian
  intro j
  let Es : H3SpectralVelocityPath →L[ℝ] H3SpectralVelocityState :=
    BoundedContinuousFunction.evalCLM ℝ s
  let Pj : H3SpectralVelocityState →L[ℝ] H3FourierComplexL2 :=
    ContinuousLinearMap.proj j
  have hState :
      Tendsto (fun i => U i s) l (nhds (V s)) := by
    have hEval := (Es.continuous.tendsto V).comp hUV
    simpa only [Es, BoundedContinuousFunction.evalCLM_apply, Function.comp_def] using hEval
  have hCoord :
      Tendsto (fun i => U i s j) l (nhds (V s j)) := by
    have hProj := (Pj.continuous.tendsto (V s)).comp hState
    simpa only [Pj, ContinuousLinearMap.proj_apply, Function.comp_def] using hProj
  apply h3FourierL2Hermitian_of_tendsto hCoord
  filter_upwards [hU] with i hi
  exact h3SpectralVelocityRawHermitian_to_hermitian (hi s) j

/-! ## Banach-selected solution -/

/-- The Banach-selected finite heat--Leray mild solution is raw-Hermitian at
every normalized time whenever the restart datum is raw-Hermitian. -/
theorem h3SpectralFinHeatLerayMildSolution_preserves_rawHermitian
    {ν τ A : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀bound : ‖U₀‖ ≤ A)
    (hsmall :
      8 * h3HeatLerayDuhamelPathCoefficient ν * A * Real.sqrt τ ≤ 1)
    (hU₀real : H3SpectralVelocityRawHermitian U₀) :
    H3SpectralVelocityPathRawHermitian
      (h3SpectralFinHeatLerayMildSolution
        hν hτ U₀ hA hU₀bound hsmall) := by
  apply h3SpectralVelocityPathRawHermitian_of_tendsto
    (ι := ℕ) (l := Filter.atTop)
  · have h :=
      (h3SpectralFinHeatLerayEstimateData
        hν hτ U₀ hA hU₀bound).tendsto_iterate_heatLeray_solution
          τ hτ
          (h3SpectralFinHeatLerayEstimateData_smallTime
            hν hτ U₀ hA hU₀bound hsmall)
    simpa only [
      h3SpectralFinHeatLerayMildSolution,
      h3SpectralFinHeatLerayRestartPicardProblem
    ] using h
  · exact Filter.Eventually.of_forall
      (h3SpectralFinHeatLerayPicardIterate_preserves_rawHermitian
        hν hτ U₀ hA hU₀bound hsmall hU₀real)

end

end Euclidean
end Bridge
end PrimeTensor
