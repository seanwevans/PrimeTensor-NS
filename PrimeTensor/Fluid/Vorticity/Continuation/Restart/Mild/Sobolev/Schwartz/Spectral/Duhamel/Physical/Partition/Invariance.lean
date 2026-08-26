import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Physical.Cocycle.Finite

/-!
# Physical Duhamel restart partition invariance

The finite cocycle collapses every positive finite restart chain to the single
Duhamel remainder over its total elapsed time.  This file records the restart
interface that follows immediately: the recursive physical remainder is
independent of how that elapsed time is partitioned.

Thus a continuation argument may refine or coarsen a finite positive restart
mesh without changing the nonlinear remainder.  We also expose physical
realization membership directly for the folded remainder itself, so downstream
proofs no longer need to unfold the single-interval Duhamel representative.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

/-- The decoded finite restart fold itself is physically realized over its
total elapsed time. -/
theorem h3SpectralFinHeatLerayDuhamelRestartFold_decodeComplexL2_mem_physicalRealization_of_continuous
    {ν a MU MV : ℝ}
    (hν : 0 < ν)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s : ℝ, ‖U s‖ ≤ MU)
    (hV : ∀ s : ℝ, ‖V s‖ ≤ MV)
    (ds : List NNReal)
    (hne : ds ≠ [])
    (hpos : ∀ d ∈ ds, 0 < d) :
    h3SpectralFinVectorDecodeComplexL2
        (h3SpectralFinHeatLerayDuhamelRestartFold ν a hν U V ds)
      ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization
          ν (((ds.sum : NNReal) : ℝ)) hν := by
  have h :=
    h3SpectralFinHeatLerayDuhamel_shifted_decodeComplexL2_realized_finite_cocycle_of_continuous
      (a := a)
      hν hMU hMV U V hUcont hVcont hU hV ds hne hpos
  rw [← h.2]
  exact h.1

/-- Two positive finite restart partitions with the same total duration produce
exactly the same recursively folded spectral Duhamel remainder. -/
theorem h3SpectralFinHeatLerayDuhamelRestartFold_eq_of_sum_eq_of_continuous
    {ν a MU MV : ℝ}
    (hν : 0 < ν)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s : ℝ, ‖U s‖ ≤ MU)
    (hV : ∀ s : ℝ, ‖V s‖ ≤ MV)
    (ds es : List NNReal)
    (hneDs : ds ≠ [])
    (hneEs : es ≠ [])
    (hposDs : ∀ d ∈ ds, 0 < d)
    (hposEs : ∀ d ∈ es, 0 < d)
    (hsum : ds.sum = es.sum) :
    h3SpectralFinHeatLerayDuhamelRestartFold ν a hν U V ds =
      h3SpectralFinHeatLerayDuhamelRestartFold ν a hν U V es := by
  have hds :=
    h3SpectralFinHeatLerayDuhamel_shifted_eq_restartFold_of_continuous
      (a := a)
      hν hMU hMV U V hUcont hVcont hU hV ds hneDs hposDs
  have hes :=
    h3SpectralFinHeatLerayDuhamel_shifted_eq_restartFold_of_continuous
      (a := a)
      hν hMU hMV U V hUcont hVcont hU hV es hneEs hposEs
  calc
    h3SpectralFinHeatLerayDuhamelRestartFold ν a hν U V ds =
        h3SpectralFinHeatLerayDuhamel
          ν (((ds.sum : NNReal) : ℝ)) hν
          (fun q => U (q + a))
          (fun q => V (q + a)) := hds.symm
    _ = h3SpectralFinHeatLerayDuhamel
          ν (((es.sum : NNReal) : ℝ)) hν
          (fun q => U (q + a))
          (fun q => V (q + a)) := by rw [hsum]
    _ = h3SpectralFinHeatLerayDuhamelRestartFold ν a hν U V es := hes

/-- Partition invariance after decoding to physical `L²`. -/
theorem h3SpectralFinHeatLerayDuhamelRestartFold_decodeComplexL2_eq_of_sum_eq_of_continuous
    {ν a MU MV : ℝ}
    (hν : 0 < ν)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s : ℝ, ‖U s‖ ≤ MU)
    (hV : ∀ s : ℝ, ‖V s‖ ≤ MV)
    (ds es : List NNReal)
    (hneDs : ds ≠ [])
    (hneEs : es ≠ [])
    (hposDs : ∀ d ∈ ds, 0 < d)
    (hposEs : ∀ d ∈ es, 0 < d)
    (hsum : ds.sum = es.sum) :
    h3SpectralFinVectorDecodeComplexL2
        (h3SpectralFinHeatLerayDuhamelRestartFold ν a hν U V ds) =
      h3SpectralFinVectorDecodeComplexL2
        (h3SpectralFinHeatLerayDuhamelRestartFold ν a hν U V es) := by
  exact congrArg h3SpectralFinVectorDecodeComplexL2
    (h3SpectralFinHeatLerayDuhamelRestartFold_eq_of_sum_eq_of_continuous
      hν hMU hMV U V hUcont hVcont hU hV
      ds es hneDs hneEs hposDs hposEs hsum)

/-- The Banach-selected globally clamped mild path is independent of the
chosen positive finite restart partition, provided the total elapsed times
agree. -/
theorem h3SpectralFinHeatLerayMildSolutionPhysicalExtension_restartFold_partition_invariant
    {ν τ A a : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hsmall :
      8 * h3HeatLerayDuhamelPathCoefficient ν * A * Real.sqrt τ ≤ 1)
    (ds es : List NNReal)
    (hneDs : ds ≠ [])
    (hneEs : es ≠ [])
    (hposDs : ∀ d ∈ ds, 0 < d)
    (hposEs : ∀ d ∈ es, 0 < d)
    (hsum : ds.sum = es.sum) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionPhysicalExtension
        hν hτ U₀ hA hU₀ hsmall
    h3SpectralFinHeatLerayDuhamelRestartFold ν a hν W W ds =
      h3SpectralFinHeatLerayDuhamelRestartFold ν a hν W W es := by
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

  exact
    h3SpectralFinHeatLerayDuhamelRestartFold_eq_of_sum_eq_of_continuous
      (a := a)
      hν htwoA htwoA W W hWcont hWcont hWbound hWbound
      ds es hneDs hneEs hposDs hposEs hsum

end

end Euclidean
end Bridge
end PrimeTensor
