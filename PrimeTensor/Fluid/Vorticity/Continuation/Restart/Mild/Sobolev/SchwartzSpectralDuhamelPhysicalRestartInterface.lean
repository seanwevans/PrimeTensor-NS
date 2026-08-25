import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.SchwartzSpectralDuhamelPhysicalPartitionInvariance

/-!
# Mesh-independent physical Duhamel restart interface

The finite restart cocycle and partition-invariance theorem show that a restart
remainder depends only on its origin and total elapsed time, not on a chosen
positive finite partition.  This file packages that fact as a canonical
restart interface.

Downstream continuation arguments can therefore carry one elapsed duration
instead of a restart mesh.  Any positive finite partition with that total
folds to the same canonical spectral remainder, and the decoded canonical
remainder lies in the Schwartz physical-realization set for that duration.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

/-- Canonical spectral nonlinear remainder beginning at restart origin `a` and
running for elapsed duration `T`. -/
def h3SpectralFinHeatLerayDuhamelRestartRemainder
    (ν a : ℝ)
    (hν : 0 < ν)
    (U V : ℝ → H3SpectralFinVectorState)
    (T : NNReal) : H3SpectralFinVectorState :=
  h3SpectralFinHeatLerayDuhamel
    ν (T : ℝ) hν
    (fun q => U (q + a))
    (fun q => V (q + a))

/-- Every positive finite restart partition computes the canonical remainder
for its total elapsed duration. -/
theorem h3SpectralFinHeatLerayDuhamelRestartFold_eq_restartRemainder_of_continuous
    {ν a MU MV : ℝ}
    (hν : 0 < ν)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s : ℝ, ‖U s‖ ≤ MU)
    (hV : ∀ s : ℝ, ‖V s‖ ≤ MV)
    (T : NNReal)
    (ds : List NNReal)
    (hne : ds ≠ [])
    (hpos : ∀ d ∈ ds, 0 < d)
    (hsum : ds.sum = T) :
    h3SpectralFinHeatLerayDuhamelRestartFold ν a hν U V ds =
      h3SpectralFinHeatLerayDuhamelRestartRemainder ν a hν U V T := by
  have hcollapse :=
    h3SpectralFinHeatLerayDuhamel_shifted_eq_restartFold_of_continuous
      (a := a)
      hν hMU hMV U V hUcont hVcont hU hV ds hne hpos
  calc
    h3SpectralFinHeatLerayDuhamelRestartFold ν a hν U V ds =
        h3SpectralFinHeatLerayDuhamel
          ν (((ds.sum : NNReal) : ℝ)) hν
          (fun q => U (q + a))
          (fun q => V (q + a)) := hcollapse.symm
    _ = h3SpectralFinHeatLerayDuhamel
          ν (T : ℝ) hν
          (fun q => U (q + a))
          (fun q => V (q + a)) := by rw [hsum]
    _ = h3SpectralFinHeatLerayDuhamelRestartRemainder ν a hν U V T := rfl

/-- The canonical positive-time restart remainder has a Schwartz physical
realization, independently of any partition. -/
theorem h3SpectralFinHeatLerayDuhamelRestartRemainder_decodeComplexL2_mem_physicalRealization_of_continuous
    {ν a MU MV : ℝ}
    (hν : 0 < ν)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s : ℝ, ‖U s‖ ≤ MU)
    (hV : ∀ s : ℝ, ‖V s‖ ≤ MV)
    (T : NNReal)
    (hT : 0 < T) :
    h3SpectralFinVectorDecodeComplexL2
        (h3SpectralFinHeatLerayDuhamelRestartRemainder ν a hν U V T)
      ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization ν (T : ℝ) hν := by
  have hTReal : 0 < (T : ℝ) := by
    exact_mod_cast hT

  let Ua : ℝ → H3SpectralFinVectorState := fun q => U (q + a)
  let Va : ℝ → H3SpectralFinVectorState := fun q => V (q + a)

  have hUaCont : Continuous Ua := by
    dsimp [Ua]
    exact hUcont.comp (continuous_id.add continuous_const)
  have hVaCont : Continuous Va := by
    dsimp [Va]
    exact hVcont.comp (continuous_id.add continuous_const)
  have hUa : ∀ q : ℝ, ‖Ua q‖ ≤ MU := by
    intro q
    exact hU (q + a)
  have hVa : ∀ q : ℝ, ‖Va q‖ ≤ MV := by
    intro q
    exact hV (q + a)

  have hmem :=
    h3SpectralFinHeatLerayDuhamel_decodeComplexL2_mem_physicalRealization_of_continuous
      hν hTReal hMU hMV Ua Va hUaCont hVaCont hUa hVa

  simpa only [h3SpectralFinHeatLerayDuhamelRestartRemainder, Ua, Va] using hmem

/-- Mesh-independent restart interface: a positive finite partition folds to
the canonical remainder, whose decoded value is physically realized. -/
theorem h3SpectralFinHeatLerayDuhamelRestartRemainder_partition_interface_of_continuous
    {ν a MU MV : ℝ}
    (hν : 0 < ν)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s : ℝ, ‖U s‖ ≤ MU)
    (hV : ∀ s : ℝ, ‖V s‖ ≤ MV)
    (T : NNReal)
    (hT : 0 < T)
    (ds : List NNReal)
    (hne : ds ≠ [])
    (hpos : ∀ d ∈ ds, 0 < d)
    (hsum : ds.sum = T) :
    h3SpectralFinHeatLerayDuhamelRestartFold ν a hν U V ds =
        h3SpectralFinHeatLerayDuhamelRestartRemainder ν a hν U V T
      ∧
    h3SpectralFinVectorDecodeComplexL2
        (h3SpectralFinHeatLerayDuhamelRestartRemainder ν a hν U V T)
      ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization ν (T : ℝ) hν := by
  constructor
  · exact
      h3SpectralFinHeatLerayDuhamelRestartFold_eq_restartRemainder_of_continuous
        hν hMU hMV U V hUcont hVcont hU hV T ds hne hpos hsum
  · exact
      h3SpectralFinHeatLerayDuhamelRestartRemainder_decodeComplexL2_mem_physicalRealization_of_continuous
        hν hMU hMV U V hUcont hVcont hU hV T hT

/-- The Banach-selected globally clamped mild path exposes the same canonical,
mesh-independent restart remainder at every origin. -/
theorem h3SpectralFinHeatLerayMildSolutionPhysicalExtension_restartRemainder_partition_interface
    {ν τ A a : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hsmall :
      8 * h3HeatLerayDuhamelPathCoefficient ν * A * Real.sqrt τ ≤ 1)
    (T : NNReal)
    (hT : 0 < T)
    (ds : List NNReal)
    (hne : ds ≠ [])
    (hpos : ∀ d ∈ ds, 0 < d)
    (hsum : ds.sum = T) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionPhysicalExtension
        hν hτ U₀ hA hU₀ hsmall
    h3SpectralFinHeatLerayDuhamelRestartFold ν a hν W W ds =
        h3SpectralFinHeatLerayDuhamelRestartRemainder ν a hν W W T
      ∧
    h3SpectralFinVectorDecodeComplexL2
        (h3SpectralFinHeatLerayDuhamelRestartRemainder ν a hν W W T)
      ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization ν (T : ℝ) hν := by
  dsimp only
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionPhysicalExtension
      hν hτ U₀ hA hU₀ hsmall

  have hWb :=
    h3SpectralFinHeatLerayMildSolutionPhysicalExtension_continuous_bounded
      hν hτ U₀ hA hU₀ hsmall
  have hWcont : Continuous W := by
    simpa only [W] using hWb.1
  have hWbound : ∀ s : ℝ, ‖W s‖ ≤ 2 * A := by
    intro s
    simpa only [W] using hWb.2 s
  have htwoA : 0 ≤ 2 * A :=
    mul_nonneg (by norm_num) hA.le

  simpa only [W] using
    (h3SpectralFinHeatLerayDuhamelRestartRemainder_partition_interface_of_continuous
      (a := a)
      hν htwoA htwoA W W hWcont hWcont hWbound hWbound
      T hT ds hne hpos hsum)

end

end Euclidean
end Bridge
end PrimeTensor
