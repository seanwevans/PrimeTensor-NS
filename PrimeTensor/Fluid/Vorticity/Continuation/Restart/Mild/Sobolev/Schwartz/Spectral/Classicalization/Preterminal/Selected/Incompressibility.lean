import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.PreterminalIncompressibility
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Leray.Encoded.SelectedIncompressibility
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Evolution

/-!
# Incompressibility of the canonical preterminal selected restart

The spectral incompressibility chain is now complete at both ends.

`PreterminalIncompressibility` proves that every H³-integrable interior
preterminal Navier--Stokes slice has a divergence-free canonical weighted
spectral encoding.  `SelectedIncompressibility` proves that a divergence-free
anchor remains divergence-free along every physical-time slice of the
Banach-selected heat--Leray mild solution.

This file composes those results for the exact restart object used by the
classicalization stack.

In particular:

* the retained-tail canonical anchor is automatically Fourier divergence-free;
* the canonical restart-radius physical extension preserves that property at
  every `s ∈ [0,R]`;
* therefore the selected restart launched from the old preterminal tail is
  Fourier divergence-free throughout the whole canonical restart interval.

No evolution-frontier hypothesis is needed: incompressibility is intrinsic to
the Leray-selected mild flow once the genuine preterminal anchor has been
encoded.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3PreterminalSelectedSpectralIncompressibility
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The canonical spectral restart anchor extracted from retained preterminal
H³ tail data is Fourier divergence-free. -/
theorem h3PreterminalTailCanonicalAnchorSpectralState_divergenceFree
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hTail : CanonicalH3TailDataFrom u t T E) :
    H3SpectralFinDivergenceFree
      (h3PreterminalTailCanonicalAnchorSpectralState
        hNS ht hTail) := by
  unfold h3PreterminalTailCanonicalAnchorSpectralState
  unfold h3PreterminalCanonicalAnchorSpectralState

  exact
    velocityH3SpectralStateAt_divergenceFree_of_loggedPreterminalNavierStokes
      hNS
      ht
      (canonicalH3TailDataFrom_at_anchor ht hTail).1

/-- The canonical restart-radius physical extension preserves Fourier
incompressibility at every physical time in its selected interval. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_divergenceFree
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hDiv₀ : H3SpectralFinDivergenceFree U₀)
    (hs0 : 0 ≤ s)
    (hsR : s ≤ h3FinHeatLerayRestartRadius ν A) :
    H3SpectralFinDivergenceFree
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀ s) := by
  let q :
      Set.Icc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius ν A) :=
    ⟨s, hs0, hsR⟩

  have hSelected :
      H3SpectralFinDivergenceFree
        (h3SpectralFinHeatLerayPhysicalMildSolution
          hν
          (h3FinHeatLerayRestartRadius_pos ν hA).le
          U₀
          hA
          hU₀
          (h3FinHeatLerayRestartRadius_smallness ν hA.le)
          q) :=
    h3SpectralFinHeatLerayPhysicalMildSolution_divergenceFree
      hν
      (h3FinHeatLerayRestartRadius_pos ν hA).le
      U₀
      hA
      hU₀
      (h3FinHeatLerayRestartRadius_smallness ν hA.le)
      hDiv₀
      q

  simpa only [
    q,
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension,
    h3SpectralFinHeatLerayPhysicalMildSolution_apply
  ] using hSelected

/-- The actual canonical selected restart launched from a retained preterminal
H³ tail is Fourier divergence-free at every time in the full canonical restart
interval. -/
theorem h3PreterminalTailCanonicalSelectedRestart_divergenceFree
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    {s : ℝ}
    (hs0 : 0 ≤ s)
    (hsR : s ≤ h3FinHeatLerayRestartRadius ν E) :
    H3SpectralFinDivergenceFree
      (h3PreterminalTailCanonicalSelectedRestart
        hν hNS ht hE hTail s) := by
  unfold h3PreterminalTailCanonicalSelectedRestart

  exact
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_divergenceFree
      hν
      (h3PreterminalTailCanonicalAnchorSpectralState
        hNS ht hTail)
      (lt_of_lt_of_le zero_lt_one hE)
      (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
        hNS ht hE hTail)
      (h3PreterminalTailCanonicalAnchorSpectralState_divergenceFree
        hNS ht hTail)
      hs0
      hsR

/-- Half-open positive-window form used by the selected classical
reconstruction layer. -/
theorem h3PreterminalTailCanonicalSelectedRestart_divergenceFreeOn_Ioc
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) :
    ∀ s : ℝ,
      s ∈ Set.Ioc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius ν E) →
      H3SpectralFinDivergenceFree
        (h3PreterminalTailCanonicalSelectedRestart
          hν hNS ht hE hTail s) := by
  intro s hs

  exact
    h3PreterminalTailCanonicalSelectedRestart_divergenceFree
      hν hNS ht hE hTail
      hs.1.le
      hs.2

end
end Euclidean
end Bridge
end PrimeTensor
