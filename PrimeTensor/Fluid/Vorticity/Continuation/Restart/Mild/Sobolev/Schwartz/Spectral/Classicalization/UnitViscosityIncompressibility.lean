import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.UnitViscosityPDEDecomposition
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedPhysicalIncompressibility

/-!
# Unit-viscosity incompressibility of the canonical local fill

`SelectedPhysicalIncompressibility` proves genuine pointwise physical
incompressibility of the smooth real representative of the canonical selected
restart.

The unit-viscosity PDE frontier is formulated instead for the absolute-time
old/selected overlap glue, wrapped in a total local-fill field.  This file
transports incompressibility through those two bookkeeping layers.

There are only two time regions.

* Before the old terminal time `T`, the glue is exactly the original logged
  preterminal Navier--Stokes solution, whose `PreterminalNavierStokes3`
  witness already contains pointwise incompressibility.
* At and after `T`, the glue is definitionally the selected real restart at
  elapsed time `s - t`.  The local endpoint hypothesis
  `S - t < h3FinHeatLerayRestartRadius ν E` keeps every such elapsed time
  inside the interval covered by `SelectedPhysicalIncompressibility`.

Consequently the `H3PreterminalTailUnitViscosityIncompressibleAt` field of the
decomposed local PDE frontier is no longer an independent analytic assumption.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityIncompressibility
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- On every local interval lying strictly inside the selected restart radius,
the canonical old/selected overlap glue is pointwise incompressible.

Before `T` this is inherited from the original preterminal Navier--Stokes
solution.  At and after `T` it is inherited from the selected real restart. -/
theorem h3PreterminalTailCanonicalSelectedOverlapGlue_divergence_eq_zero_on_localInterval
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t S s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hSR :
      S - t < h3FinHeatLerayRestartRadius ν E)
    (hs : s ∈ Set.Ioo (0 : ℝ) S)
    (x : Point3) :
    PrimeTensor.Bridge.RealFluid.divergence
        spatial3
        (h3PreterminalTailCanonicalSelectedOverlapGlue
          hν hNS ht hE hTail s)
        x
      =
    0 := by
  by_cases hBefore : s < T

  · have hsOld :
        s ∈ Set.Ioo (0 : ℝ) T :=
      ⟨hs.1, hBefore⟩

    have hAgree :
        logSpaceTimeVectorField u s
          =
        h3PreterminalTailCanonicalSelectedOverlapGlue
          hν hNS ht hE hTail s :=
      h3PreterminalTailCanonicalSelectedOverlapGlue_agreesBeforeT
        hν hNS ht hE hTail
        s hsOld

    let p :
        SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
      Classical.choose hNS

    have hPDE :
        PreterminalNavierStokes3
          (logSpaceTimeVectorField u)
          p
          T :=
      Classical.choose_spec hNS

    rw [← hAgree]

    exact
      hPDE.incompressible
        s hsOld x

  · have hsT : T ≤ s :=
      le_of_not_gt hBefore

    have hs0 : 0 ≤ s - t :=
      sub_nonneg.mpr
        (le_trans ht.2.le hsT)

    have hsR :
        s - t ≤ h3FinHeatLerayRestartRadius ν E :=
      (lt_trans
        (sub_lt_sub_right hs.2 t)
        hSR).le

    have hEq :
        h3PreterminalTailCanonicalSelectedOverlapGlue
            hν hNS ht hE hTail s
          =
        h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
          hν
          (h3PreterminalTailCanonicalAnchorSpectralState
            hNS ht hTail)
          (lt_of_lt_of_le zero_lt_one hE)
          (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
            hNS ht hE hTail)
          (s - t) := by
      unfold h3PreterminalTailCanonicalSelectedOverlapGlue
      unfold h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedOverlapGlue
      simp only [dif_neg hBefore]

    rw [hEq]

    exact
      h3PreterminalTailCanonicalSelectedRealVelocity_divergence_eq_zero
        hν hNS ht hE hTail
        hs0 hsR x

/-- The total local-fill wrapper is incompressible throughout its actual local
PDE interval as soon as that interval lies strictly inside the canonical
selected restart radius.

This discharges `H3PreterminalTailUnitViscosityIncompressibleAt` from the
existing local endpoint bound; no physical-evolution hypothesis is needed. -/
theorem h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill_incompressible
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t S : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hSR :
      S - t <
        h3FinHeatLerayRestartRadius (1 : ℝ) E) :
    H3PreterminalTailUnitViscosityIncompressibleAt
      hNS ht hE hTail S := by
  intro s hs x

  rw [
    h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill_eq_glue_of_mem
      hNS ht hE hTail hs
  ]

  exact
    h3PreterminalTailCanonicalSelectedOverlapGlue_divergence_eq_zero_on_localInterval
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail
      hSR hs x

end
end Euclidean
end Bridge
end PrimeTensor
