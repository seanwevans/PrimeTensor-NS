import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Raw.Outer.Divergence.Advection.Bridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Encoded.Restart.Radius.Closure

/-!
# Classicalization: selected raw outer divergence is physical advection

The generic nonlinear bridge now says that a realizable, raw-divergence-free
spectral slice reconstructs the unprojected raw outer-product divergence
exactly as the physical `RealFluid.advection` term.

For the canonical preterminal restart, both hypotheses are already intrinsic.

* The retained H³ tail is encoded from a genuine real physical velocity
  snapshot.  The canonical-radius encoded restart theorem therefore makes every
  selected physical-time slice realizable.
* The selected Leray evolution preserves raw Fourier incompressibility.

This file composes those facts.  Hence throughout the full canonical restart
interval the unprojected nonlinear Fourier term is no longer an abstract
spectral object: after inverse Fourier reconstruction it is exactly the
ordinary physical advection term used by the Navier--Stokes momentum equation.

The remaining nonlinear distinction is solely the Leray projection.  Its
complement is therefore the pressure-gradient term to be reconstructed next.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3SelectedRawOuterDivergenceAdvection
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Every slice of the canonical selected preterminal restart is physically
realizable throughout the full closed restart interval. -/
theorem h3PreterminalTailCanonicalSelectedRestart_realizable
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
    H3SpectralVelocityRealizable
      (h3PreterminalTailCanonicalSelectedRestart
        hν hNS ht hE hTail s) := by
  let hInt : VelocityH3IntegrableAt u t :=
    (canonicalH3TailDataFrom_at_anchor ht hTail).1

  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hNS ht

  let hFourier :
      VelocityH3FourierCompatibleAt u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hNS ht hInt

  have hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  have hU₀ :
      ‖velocityH3SpectralStateAt
          u t hInt hMeas hFourier‖ ≤ E := by
    change
      ‖h3PreterminalTailCanonicalAnchorSpectralState
          hNS ht hTail‖ ≤ E
    exact
      norm_h3PreterminalTailCanonicalAnchorSpectralState_le
        hNS ht hE hTail

  let q : Set.Icc
      (0 : ℝ)
      (h3FinHeatLerayRestartRadius ν E) :=
    ⟨s, hs0, hsR⟩

  have hReal :
      H3SpectralVelocityRealizable
        (h3SpectralFinHeatLerayPhysicalMildSolution
          hν
          (h3FinHeatLerayRestartRadius_pos ν hA).le
          (velocityH3SpectralStateAt
            u t hInt hMeas hFourier)
          hA
          hU₀
          (h3FinHeatLerayRestartRadius_smallness ν hA.le)
          q) := by
    exact
      h3SpectralFinHeatLerayPhysicalMildSolution_encoded_realizable
        hν
        (h3FinHeatLerayRestartRadius_pos ν hA).le
        hFourier
        hA
        hU₀
        (h3FinHeatLerayRestartRadius_smallness ν hA.le)
        q

  rw [
    h3SpectralFinHeatLerayPhysicalMildSolution_apply
  ] at hReal

  change
    H3SpectralVelocityRealizable
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν
        (velocityH3SpectralStateAt
          u t hInt hMeas hFourier)
        hA
        hU₀
        s)

  simpa only [
    q,
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
  ] using hReal

/-- On every canonical selected restart slice, the real inverse Fourier
reconstruction of the unprojected raw outer-product divergence is exactly the
physical advection component. -/
theorem h3PreterminalTailCanonicalSelectedRestart_rawOuterDivergence_fourierInv_re_eq_advection
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
    (hsR : s ≤ h3FinHeatLerayRestartRadius ν E)
    (i : Fin 3)
    (x : Point3) :
    (FourierTransformInv.fourierInv
      (h3RawFinOuterProductDivergence
        (h3PreterminalTailCanonicalSelectedRestart
          hν hNS ht hE hTail s)
        (h3PreterminalTailCanonicalSelectedRestart
          hν hNS ht hE hTail s)
        i)
      ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re
      =
    (PrimeTensor.Bridge.RealFluid.advection
      spatial3
      (h3SpectralRealVelocityOfPath
        (h3PreterminalTailCanonicalSelectedRestart
          hν hNS ht hE hTail))
      s x).component
        (h3AxisOfFin3 i) := by
  exact
    h3RawFinOuterProductDivergence_fourierInv_re_eq_advection_of_realizable_of_rawDivergenceFree
      (h3PreterminalTailCanonicalSelectedRestart
        hν hNS ht hE hTail)
      s
      (h3PreterminalTailCanonicalSelectedRestart_realizable
        hν hNS ht hE hTail hs0 hsR)
      (h3PreterminalTailCanonicalSelectedRestart_rawDivergenceFree
        hν hNS ht hE hTail hs0 hsR)
      i
      x

/-- Named selected-real-velocity form of the same nonlinear identity.  This is
the form consumed by the physical PDE and pressure reconstruction layers. -/
theorem h3PreterminalTailCanonicalSelectedRealVelocity_rawOuterDivergence_fourierInv_re_eq_advection
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
    (hsR : s ≤ h3FinHeatLerayRestartRadius ν E)
    (i : Fin 3)
    (x : Point3) :
    (FourierTransformInv.fourierInv
      (h3RawFinOuterProductDivergence
        (h3PreterminalTailCanonicalSelectedRestart
          hν hNS ht hE hTail s)
        (h3PreterminalTailCanonicalSelectedRestart
          hν hNS ht hE hTail s)
        i)
      ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re
      =
    (PrimeTensor.Bridge.RealFluid.advection
      spatial3
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
        hν
        (h3PreterminalTailCanonicalAnchorSpectralState
          hNS ht hTail)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
          hNS ht hE hTail))
      s x).component
        (h3AxisOfFin3 i) := by
  simpa only [
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity,
    h3PreterminalTailCanonicalSelectedRestart
  ] using
    h3PreterminalTailCanonicalSelectedRestart_rawOuterDivergence_fourierInv_re_eq_advection
      hν hNS ht hE hTail hs0 hsR i x

end

end Euclidean
end Bridge
end PrimeTensor
