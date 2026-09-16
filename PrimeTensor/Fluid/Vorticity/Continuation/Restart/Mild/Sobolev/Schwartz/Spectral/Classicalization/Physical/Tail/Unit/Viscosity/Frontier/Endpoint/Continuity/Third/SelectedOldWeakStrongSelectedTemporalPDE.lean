import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongWeakFTCReduction
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Real.Spatial.PDE.Form
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Time.Continuity

/-!
# Canonical selected temporal PDE on the restart branch

`SelectedOldWeakStrongWeakFTCReduction` isolates one remaining branch-local
temporal statement: the selected restart must satisfy its weak projected-RHS
FTC.

The general selected classicalization stack has already proved both ingredients
needed for the scalar FTC argument:

* every selected real velocity coordinate is continuous in elapsed time;
* at each strict positive interior restart time its ordinary time derivative is

      Δ S_i - N_i(S,S)

  in concrete `Point3` spatial derivatives.

This file specializes those general theorems to the canonical unit-viscosity
restart launched from the old H³ anchor.  The resulting statements mention
only the preterminal data used by the weak--strong comparison.

No old temporal regularity, endpoint continuity, or selected--old agreement is
used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology
  InnerProductSpace RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongSelectedTemporalPDE
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The canonical unit-viscosity selected real velocity coordinate is
continuous for all real elapsed times. -/
theorem h3PreterminalSelectedUnitRealVelocity_component_continuous
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (x : Point3)
    (i : Fin 3) :
    Continuous
      (fun s : ℝ =>
        h3SpectralScalarRealC1RepresentativeOnPoint3
          ((h3PreterminalTailCanonicalSelectedRestart
            (one_pos : (0 : ℝ) < 1)
            hNS ht hE hTail) s i)
          x) := by
  have h :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_component_continuous
      (one_pos : (0 : ℝ) < 1)
      (h3PreterminalTailCanonicalAnchorSpectralState
        hNS ht hTail)
      (lt_of_lt_of_le zero_lt_one hE)
      (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
        hNS ht hE hTail)
      x
      (h3AxisOfFin3 i)

  simpa only [
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity,
    h3PreterminalTailCanonicalSelectedRestart,
    h3SpectralRealVelocityOfPath_component_h3AxisOfFin3,
    h3SpectralVelocityRealC1RepresentativeOnPoint3
  ] using h

/-- At every strict positive interior restart time, the canonical selected
coordinate satisfies the exact unit-viscosity pressure-free temporal PDE

    ∂ₜ S_i
      =
    Σ_j ∂_j² S_i - N_i(S,S).

The nonlinear term is kept as the already-classicalized real representative of
the finite Leray forcing. -/
theorem h3PreterminalSelectedUnitRealVelocity_temporal_d_eq_spatialLaplacian_sub_forcing
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hs0 : 0 < s)
    (hsR :
      s < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (x : Point3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalSelectedRestart
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail
    temporal.d
        (fun r : ℝ =>
          h3SpectralScalarRealC1RepresentativeOnPoint3
            (W r i) x)
        s
      =
    (∑ j : Fin 3,
      spatial3.d
        (h3AxisOfFin3 j)
        (spatial3.d
          (h3AxisOfFin3 j)
          (h3SpectralScalarRealC1RepresentativeOnPoint3
            (W s i)))
        x)
      -
    (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
      (W s) (W s) i x).re := by
  dsimp only

  have hPDE :=
    temporal_d_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_eq_spatialLaplacian_sub_forcing
      (one_pos : (0 : ℝ) < 1)
      (h3PreterminalTailCanonicalAnchorSpectralState
        hNS ht hTail)
      (lt_of_lt_of_le zero_lt_one hE)
      (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
        hNS ht hE hTail)
      hs0
      hsR
      i
      x

  simpa only [
    one_mul,
    h3PreterminalTailCanonicalSelectedRestart
  ] using hPDE

end

end Euclidean
end Bridge
end PrimeTensor
