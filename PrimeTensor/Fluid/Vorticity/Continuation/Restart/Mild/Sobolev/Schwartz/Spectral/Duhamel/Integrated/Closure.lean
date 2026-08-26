import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Integral.Bridge

/-!
# Integrated physical closure for the heat--Leray Duhamel term

The decoder now commutes exactly with the Bochner interval integral, while the
strict retarded integrand has already been shown to lie in the physical `L²`
closure of genuine Schwartz heat--Leray anchors at the corresponding positive
lag.

This file combines those two facts without introducing any measurable
selection assumption.  The resulting predicate records that a physical vector
is an interval integral of a physical integrand whose value at every strict
pre-endpoint time belongs to the already established heat--Leray Schwartz
closure.

For the actual Duhamel term the witness is simply the decoded spectral
retarded integrand.  A second theorem discharges interval integrability
automatically on the continuous globally bounded path class used throughout
the restart argument.

The next analytic rung can therefore focus only on upgrading this integrated
pointwise closure to a closed convex / finite-anchor realization; all
spectral-to-physical and Bochner bookkeeping is complete here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

/-- A physical finite vector belongs to the integrated heat--Leray Schwartz
closure at final time `t` when it is an interval integral of a physical
integrand that lies, at every strict pre-endpoint time `s < t`, in the closure
of genuine Schwartz heat--Leray anchors at lag `t - s`. -/
def H3SchwartzHeatLerayDuhamelPhysicalIntegratedClosure
    (ν t : ℝ)
    (hν : 0 < ν)
    (u : H3ComplexPhysicalFinVectorL2) : Prop :=
  ∃ k : ℝ → H3ComplexPhysicalFinVectorL2,
    (∀ (s : ℝ) (hs : s < t),
      k s ∈ closure
        {v : H3ComplexPhysicalFinVectorL2 |
          H3SchwartzHeatLerayPhysicalFinVectorL2Anchor
            ν (t - s) hν (sub_pos.mpr hs) v}) ∧
    u = ∫ s in (0 : ℝ)..t, k s

/-- The decoded Duhamel term has an exact integrated physical-closure
representation whenever the spectral retarded integrand is interval
integrable. -/
theorem h3SpectralFinHeatLerayDuhamel_decodeComplexL2_mem_integratedClosure
    {ν t : ℝ}
    (hν : 0 < ν)
    (U V : ℝ → H3SpectralFinVectorState)
    (hInt :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand ν t hν U V)
        volume
        0
        t) :
    H3SchwartzHeatLerayDuhamelPhysicalIntegratedClosure
      ν t hν
      (h3SpectralFinVectorDecodeComplexL2
        (h3SpectralFinHeatLerayDuhamel ν t hν U V)) := by
  let k : ℝ → H3ComplexPhysicalFinVectorL2 :=
    fun s =>
      h3SpectralFinVectorDecodeComplexL2
        (h3SpectralFinHeatLerayDuhamelIntegrand ν t hν U V s)

  refine ⟨k, ?_, ?_⟩
  · intro s hs
    dsimp [k]
    exact
      h3SpectralFinHeatLerayDuhamelIntegrand_decodeComplexL2_mem_closure
        hν hs U V
  · dsimp [k]
    exact
      h3SpectralFinHeatLerayDuhamel_decodeComplexL2_eq_intervalIntegral
        hν U V hInt

/-- On the continuous globally bounded path class used by the restart
argument, the integrated physical-closure representation requires no explicit
integrability hypothesis. -/
theorem h3SpectralFinHeatLerayDuhamel_decodeComplexL2_mem_integratedClosure_of_continuous
    {ν t MU MV : ℝ}
    (hν : 0 < ν)
    (ht : 0 ≤ t)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s : ℝ, ‖U s‖ ≤ MU)
    (hV : ∀ s : ℝ, ‖V s‖ ≤ MV) :
    H3SchwartzHeatLerayDuhamelPhysicalIntegratedClosure
      ν t hν
      (h3SpectralFinVectorDecodeComplexL2
        (h3SpectralFinHeatLerayDuhamel ν t hν U V)) := by
  have hUint :
      ∀ s ∈ Set.Ioc (0 : ℝ) t,
        ‖U s‖ ≤ MU := by
    intro s _hs
    exact hU s

  have hVint :
      ∀ s ∈ Set.Ioc (0 : ℝ) t,
        ‖V s‖ ≤ MV := by
    intro s _hs
    exact hV s

  have hInt :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand ν t hν U V)
        volume
        0
        t :=
    h3SpectralFinHeatLerayDuhamelIntegrand_intervalIntegrable_of_continuous
      hν ht hMU hMV U V
      hUcont hVcont hUint hVint

  exact
    h3SpectralFinHeatLerayDuhamel_decodeComplexL2_mem_integratedClosure
      hν U V hInt

end

end Euclidean
end Bridge
end PrimeTensor
