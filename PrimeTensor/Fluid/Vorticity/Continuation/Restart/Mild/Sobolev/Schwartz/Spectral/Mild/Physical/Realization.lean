import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Physical.Realization
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Physical.Solution
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Spectral.Heat.Intertwining

/-!
# Physical Schwartz realization of the selected mild restart solution

The Duhamel term has now been realized physically as the closure of finite
convex combinations of genuine positive-lag Schwartz heat--Leray anchors.
The concrete restart solver already supplies the exact spectral mild equation
at every physical time.

This file is the first direct consumer of both developments.  At every
positive physical slice of the Banach-selected restart path, decoding the mild
equation gives

    decoded solution = physical heat evolution + realized Duhamel remainder.

The second theorem replaces the nonlinear remainder by an arbitrarily close
`t`-scaled point of the finite real convex hull of genuine Schwartz
heat--Leray anchors.  Thus the physical realization machinery is now attached
directly to the selected mild restart solution rather than only to an abstract
pair of input paths.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

/-- Physical complex heat evolution of a decoded spectral H³ velocity state. -/
noncomputable def h3ComplexPhysicalVelocityHeatApplyNN
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : ℝ≥0)
    (U : H3SpectralVelocityState) :
    H3ComplexPhysicalFinVectorL2 :=
  fun j =>
    h3ComplexHeatApplyNN ν hν t
      (h3SpectralScalarDecodeComplexL2 (U j))

@[simp]
theorem h3ComplexPhysicalVelocityHeatApplyNN_apply
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : ℝ≥0)
    (U : H3SpectralVelocityState)
    (j : Fin 3) :
    h3ComplexPhysicalVelocityHeatApplyNN ν hν t U j
      =
    h3ComplexHeatApplyNN ν hν t
      (h3SpectralScalarDecodeComplexL2 (U j)) :=
  rfl

/-- Exact finite-vector form of the spectral/physical heat intertwining. -/
@[simp]
theorem h3SpectralFinVectorDecodeComplexL2_velocityHeatApplyNN
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : ℝ≥0)
    (U : H3SpectralVelocityState) :
    h3SpectralFinVectorDecodeComplexL2
        (h3SpectralVelocityHeatApplyNN ν hν t U)
      =
    h3ComplexPhysicalVelocityHeatApplyNN ν hν t U := by
  funext j
  change
    h3SpectralScalarDecodeComplexL2
        (h3SpectralScalarHeatApplyNN ν hν t (U j))
      =
    h3ComplexHeatApplyNN ν hν t
      (h3SpectralScalarDecodeComplexL2 (U j))
  exact h3SpectralScalarDecodeComplexL2_heatApplyNN ν hν t (U j)

/-- The globally clamped selected mild path is continuous and uniformly
bounded by `2A`.  This packages the hypotheses needed by the automatic
Duhamel physical-realization theorem. -/
theorem h3SpectralFinHeatLerayMildSolutionPhysicalExtension_continuous_bounded
    {ν τ A : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hsmall :
      8 * h3HeatLerayDuhamelPathCoefficient ν * A * Real.sqrt τ ≤ 1) :
    Continuous
        (h3SpectralFinHeatLerayMildSolutionPhysicalExtension
          hν hτ U₀ hA hU₀ hsmall)
      ∧
    ∀ s : ℝ,
      ‖h3SpectralFinHeatLerayMildSolutionPhysicalExtension
          hν hτ U₀ hA hU₀ hsmall s‖
        ≤ 2 * A := by
  constructor
  · exact
      continuous_h3PathPhysicalRealExtension τ
        (h3SpectralFinHeatLerayMildSolution
          hν hτ U₀ hA hU₀ hsmall)
  · intro s
    change
      ‖h3SpectralFinHeatLerayMildSolution
          hν hτ U₀ hA hU₀ hsmall
          (h3ClampUnitTime (s / τ))‖
        ≤ 2 * A
    exact
      norm_h3SpectralFinHeatLerayMildSolution_apply_le_twoA
        hν hτ U₀ hA hU₀ hsmall
        (h3ClampUnitTime (s / τ))

/-- Every positive physical slice of the selected mild restart solution has an
exact physical decomposition into the heat evolution of the decoded initial
state plus a Duhamel remainder belonging to the genuine Schwartz physical
realization set. -/
theorem h3SpectralFinHeatLerayPhysicalMildSolution_decodeComplexL2_exists_realized_remainder
    {ν τ A : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hsmall :
      8 * h3HeatLerayDuhamelPathCoefficient ν * A * Real.sqrt τ ≤ 1)
    (q : Set.Icc (0 : ℝ) τ)
    (hq : 0 < (q : ℝ)) :
    ∃ R : H3ComplexPhysicalFinVectorL2,
      R ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization
        ν (q : ℝ) hν ∧
      h3SpectralFinVectorDecodeComplexL2
          (h3SpectralFinHeatLerayPhysicalMildSolution
            hν hτ U₀ hA hU₀ hsmall q)
        =
      h3ComplexPhysicalVelocityHeatApplyNN
          ν hν.le (h3PhysicalTimePointNN q) U₀
        + R := by
  let U : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionPhysicalExtension
      hν hτ U₀ hA hU₀ hsmall

  have hUb :=
    h3SpectralFinHeatLerayMildSolutionPhysicalExtension_continuous_bounded
      hν hτ U₀ hA hU₀ hsmall
  have hUcont : Continuous U := by
    simpa only [U] using hUb.1
  have hUbound : ∀ s : ℝ, ‖U s‖ ≤ 2 * A := by
    intro s
    simpa only [U] using hUb.2 s
  have htwoA : 0 ≤ 2 * A :=
    mul_nonneg (by norm_num) hA.le

  let R : H3ComplexPhysicalFinVectorL2 :=
    h3SpectralFinVectorDecodeComplexL2
      (h3SpectralFinHeatLerayDuhamel
        ν (q : ℝ) hν U U)

  have hR :
      R ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization
        ν (q : ℝ) hν := by
    dsimp [R]
    exact
      h3SpectralFinHeatLerayDuhamel_decodeComplexL2_mem_physicalRealization_of_continuous
        hν hq htwoA htwoA U U
        hUcont hUcont hUbound hUbound

  refine ⟨R, hR, ?_⟩

  have hMild :=
    h3SpectralFinHeatLerayPhysicalMildSolution_satisfies_mild_at
      hν hτ U₀ hA hU₀ hsmall q
  have hDecoded :=
    congrArg h3SpectralFinVectorDecodeComplexL2 hMild

  rw [h3SpectralFinVectorDecodeComplexL2_add] at hDecoded
  rw [h3SpectralFinVectorDecodeComplexL2_velocityHeatApplyNN] at hDecoded
  dsimp [R, U]
  exact hDecoded.symm

/-- Restart-ready epsilon realization.  At every positive physical time, the
decoded selected mild solution is arbitrarily close to the physical heat
flow plus `q` times a finite real convex combination of genuine positive-lag
Schwartz heat--Leray anchors. -/
theorem exists_h3SpectralFinHeatLerayPhysicalMildSolution_schwartz_convexHull_dist_lt
    {ν τ A : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hsmall :
      8 * h3HeatLerayDuhamelPathCoefficient ν * A * Real.sqrt τ ≤ 1)
    (q : Set.Icc (0 : ℝ) τ)
    (hq : 0 < (q : ℝ))
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ v : H3ComplexPhysicalFinVectorL2,
      v ∈ convexHull ℝ
        (H3SchwartzHeatLerayDuhamelPhysicalAnchorRange
          ν (q : ℝ) hν) ∧
      dist
        (h3SpectralFinVectorDecodeComplexL2
          (h3SpectralFinHeatLerayPhysicalMildSolution
            hν hτ U₀ hA hU₀ hsmall q))
        (h3ComplexPhysicalVelocityHeatApplyNN
            ν hν.le (h3PhysicalTimePointNN q) U₀
          + (q : ℝ) • v)
        < ε := by
  let U : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionPhysicalExtension
      hν hτ U₀ hA hU₀ hsmall

  have hUb :=
    h3SpectralFinHeatLerayMildSolutionPhysicalExtension_continuous_bounded
      hν hτ U₀ hA hU₀ hsmall
  have hUcont : Continuous U := by
    simpa only [U] using hUb.1
  have hUbound : ∀ s : ℝ, ‖U s‖ ≤ 2 * A := by
    intro s
    simpa only [U] using hUb.2 s
  have htwoA : 0 ≤ 2 * A :=
    mul_nonneg (by norm_num) hA.le

  have hInt :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand
          ν (q : ℝ) hν U U)
        volume
        0
        (q : ℝ) := by
    exact
      h3SpectralFinHeatLerayDuhamelIntegrand_intervalIntegrable_of_continuous
        hν hq.le htwoA htwoA U U hUcont hUcont
        (fun s _ => hUbound s)
        (fun s _ => hUbound s)

  obtain ⟨v, hv, hvdist⟩ :=
    exists_h3SchwartzHeatLerayDuhamel_convexHull_dist_lt
      hν hq U U hInt hε
  refine ⟨v, hv, ?_⟩

  have hMild :=
    h3SpectralFinHeatLerayPhysicalMildSolution_satisfies_mild_at
      hν hτ U₀ hA hU₀ hsmall q
  have hDecoded :=
    congrArg h3SpectralFinVectorDecodeComplexL2 hMild
  rw [h3SpectralFinVectorDecodeComplexL2_add] at hDecoded
  rw [h3SpectralFinVectorDecodeComplexL2_velocityHeatApplyNN] at hDecoded

  have hEq :
      h3SpectralFinVectorDecodeComplexL2
          (h3SpectralFinHeatLerayPhysicalMildSolution
            hν hτ U₀ hA hU₀ hsmall q)
        =
      h3ComplexPhysicalVelocityHeatApplyNN
          ν hν.le (h3PhysicalTimePointNN q) U₀
        +
      h3SpectralFinVectorDecodeComplexL2
        (h3SpectralFinHeatLerayDuhamel
          ν (q : ℝ) hν U U) := by
    simpa only [U] using hDecoded.symm

  rw [hEq]
  simpa only [dist_add_left] using hvdist

end

end Euclidean
end Bridge
end PrimeTensor
