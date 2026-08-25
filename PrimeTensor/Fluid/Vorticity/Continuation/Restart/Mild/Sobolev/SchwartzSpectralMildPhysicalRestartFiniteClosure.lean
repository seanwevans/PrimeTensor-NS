import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.SchwartzSpectralMildPhysicalRestartClosure
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.SchwartzSpectralDuhamelPhysicalRestartInterface

/-!
# Finite physical restart closure for the selected mild path

The two-step restart closure and the finite Duhamel cocycle are already
available.  This file packages the continuation-facing finite statement.

For any nonempty finite list of strictly positive restart durations, if the
corresponding endpoint remains inside the physical interval, then the selected
mild path advances from the initial restart origin by exactly the heat flow over
the total elapsed duration plus one canonical nonlinear restart remainder.

The recursively folded remainder for the chosen restart list is exactly that
canonical remainder, and its decoded value lies in the Schwartz heat--Leray
physical-realization set for the total duration.  Consequently downstream
continuation arguments may use an arbitrary finite restart mesh and immediately
forget the mesh after this theorem.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

/-- Any positive finite restart mesh for the Banach-selected mild path collapses
to the canonical mesh-independent physical restart evolution over its total
elapsed duration. -/
theorem h3SpectralFinHeatLerayMildSolutionPhysicalExtension_restart_physical_closed_finite
    {ν τ A a : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hsmall :
      8 * h3HeatLerayDuhamelPathCoefficient ν * A * Real.sqrt τ ≤ 1)
    (ds : List NNReal)
    (hne : ds ≠ [])
    (hpos : ∀ d ∈ ds, 0 < d)
    (ha : 0 ≤ a)
    (haSum : a + ((ds.sum : NNReal) : ℝ) ≤ τ) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionPhysicalExtension
        hν hτ U₀ hA hU₀ hsmall
    let T : NNReal := ds.sum
    let R :=
      h3SpectralFinHeatLerayDuhamelRestartRemainder
        ν a hν W W T
    h3SpectralFinVectorDecodeComplexL2 (W (a + (T : ℝ)))
        = h3ComplexPhysicalVelocityHeatApplyNN ν hν.le T (W a)
          + h3SpectralFinVectorDecodeComplexL2 R
      ∧
    h3SpectralFinHeatLerayDuhamelRestartFold ν a hν W W ds = R
      ∧
    h3SpectralFinVectorDecodeComplexL2 R
        ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization
            ν (T : ℝ) hν := by
  dsimp only
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionPhysicalExtension
      hν hτ U₀ hA hU₀ hsmall
  let T : NNReal := ds.sum
  let R : H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayDuhamelRestartRemainder
      ν a hν W W T

  have hT : 0 < T := by
    dsimp only [T]
    exact
      h3NNRealList_sum_pos_of_nonempty_of_forall_mem_pos
        ds hne hpos

  have hEvolution0 :=
    h3SpectralFinHeatLerayMildSolutionPhysicalExtension_restart_decodeComplexL2_realized
      (a := a)
      hν hτ U₀ hA hU₀ hsmall T ha hT (by
        simpa only [T] using haSum)
  have hEvolution :
      h3SpectralFinVectorDecodeComplexL2 (W (a + (T : ℝ)))
          = h3ComplexPhysicalVelocityHeatApplyNN ν hν.le T (W a)
            + h3SpectralFinVectorDecodeComplexL2 R
        ∧
      h3SpectralFinVectorDecodeComplexL2 R
          ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization
              ν (T : ℝ) hν := by
    simpa only [W, R] using hEvolution0

  have hPartition0 :=
    h3SpectralFinHeatLerayMildSolutionPhysicalExtension_restartRemainder_partition_interface
      (a := a)
      hν hτ U₀ hA hU₀ hsmall T hT ds hne hpos (by
        dsimp only [T])
  have hPartition :
      h3SpectralFinHeatLerayDuhamelRestartFold ν a hν W W ds = R
        ∧
      h3SpectralFinVectorDecodeComplexL2 R
          ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization
              ν (T : ℝ) hν := by
    simpa only [W, R] using hPartition0

  exact ⟨hEvolution.1, hPartition.1, hEvolution.2⟩

end

end Euclidean
end Bridge
end PrimeTensor
