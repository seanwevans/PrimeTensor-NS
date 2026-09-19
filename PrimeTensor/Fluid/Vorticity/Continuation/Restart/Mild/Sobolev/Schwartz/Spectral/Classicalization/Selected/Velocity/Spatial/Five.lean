import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Spatial.Regularity
import PrimeTensor.Bridge.Euclidean.Partials.Third

/-!
# Selected positive-time velocity: spatial order five

`Classicalization.Spatial.Regularity` already proves much more than the older
selected-velocity `SpatialC3` API exposes: every positive-time selected mild
coordinate is `ContDiff ℝ m` for every finite natural order `m`.

The high-order energy-class interface later asks for the equivalent order-five
statement in intrinsic coordinate language: every pure/mixed second coordinate
partial of one velocity component is spatially `C³`.

This file is only an API bridge.  No new Fourier estimate is introduced.

We:

1. expose `ContDiff ℝ 5` for each intrinsic selected velocity component;
2. prove the generic calculus fact `C⁵ -> C³` for every second coordinate
   partial;
3. package that fact on the positive restart window `(0,R]`.

This is precisely the velocity regularity shape used by
`VelocitySpatialC5OnTail`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open scoped Topology

noncomputable section

noncomputable local instance axisFintypeH3SelectedVelocitySpatialFive
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

/-! ## Generic C5 coordinate calculus -/

/--
A spatially `C⁵` scalar field has spatially `C³` second coordinate partials.
-/
private theorem secondPartial_spatialC3_of_contDiff_five
    {f : ScalarField3}
    (hf : ContDiff ℝ 5 f)
    (i k : PrimeTensor.Axis Depth.three) :
    SpatialC3
      (spatial3.d i
        (spatial3.d k f)) := by

  have hf3 :
      SpatialC3 f := by
    unfold SpatialC3
    exact hf.of_le (by norm_num)

  have hFirst4 :
      ContDiff ℝ 4
        (fun y : Point3 =>
          partialDeriv k f y) := by

    rw [
      PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_fun_eq
        hf3 k
    ]

    exact
      (hf.fderiv_right (by norm_num)).clm_apply
        contDiff_const

  have hFirst3 :
      SpatialC3
        (fun y : Point3 =>
          partialDeriv k f y) := by
    unfold SpatialC3
    exact hFirst4.of_le (by norm_num)

  have hSecond3 :
      ContDiff ℝ 3
        (fun y : Point3 =>
          partialDeriv i
            (fun z : Point3 =>
              partialDeriv k f z)
            y) := by

    rw [
      PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_fun_eq
        hFirst3 i
    ]

    exact
      (hFirst4.fderiv_right (by norm_num)).clm_apply
        contDiff_const

  change
    ContDiff ℝ 3
      (fun y : Point3 =>
        partialDeriv i
          (fun z : Point3 =>
            partialDeriv k f z)
          y)

  exact hSecond3

/-! ## Selected velocity C5 -/

/--
Every intrinsic component of the selected positive-time reconstructed velocity
is spatially `C⁵`.
-/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_contDiff_fiveAt
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s ≤ h3FinHeatLerayRestartRadius ν A)
    (j : PrimeTensor.Axis Depth.three) :
    ContDiff ℝ 5
      (fun y =>
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
          hν U₀ hA hU₀ s y).component j) := by

  change
    ContDiff ℝ 5
      (h3SpectralVelocityRealC1RepresentativeOnPoint3
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀ s)
        (h3ClassicalizationFinOfAxis j))

  exact
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_velocityRealC1RepresentativeOnPoint3_contDiff_nat
      5 hν U₀ hA hU₀ hs hsR
      (h3ClassicalizationFinOfAxis j)

/--
The selected velocity satisfies the exact second-partial `SpatialC3` condition
used by the H³ energy-class `VelocitySpatialC5OnTail` interface.
-/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_secondPartial_spatialC3At
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s ≤ h3FinHeatLerayRestartRadius ν A)
    (j i k : PrimeTensor.Axis Depth.three) :
    SpatialC3
      (spatial3.d i
        (spatial3.d k
          (fun y =>
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
              hν U₀ hA hU₀ s y).component j))) := by

  exact
    secondPartial_spatialC3_of_contDiff_five
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_contDiff_fiveAt
        hν U₀ hA hU₀ hs hsR j)
      i k

/--
Selected velocity order-five regularity on the whole positive half-open restart
window `(0,R]`, already packaged in the exact intrinsic shape needed by the
energy class.
-/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_spatialFiveOn_Ioc
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A) :
    ∀ s : ℝ,
      s ∈ Set.Ioc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius ν A) →
      ∀ j i k : PrimeTensor.Axis Depth.three,
        SpatialC3
          (spatial3.d i
            (spatial3.d k
              (fun y =>
                (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                  hν U₀ hA hU₀ s y).component j))) := by

  intro s hs j i k

  exact
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_secondPartial_spatialC3At
      hν U₀ hA hU₀ hs.1 hs.2 j i k

/--
In particular, the selected restart-radius endpoint has the exact spatial
order-five regularity required by the H³ energy class.
-/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_secondPartial_spatialC3At_radius
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (j i k : PrimeTensor.Axis Depth.three) :
    SpatialC3
      (spatial3.d i
        (spatial3.d k
          (fun y =>
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
              hν U₀ hA hU₀
              (h3FinHeatLerayRestartRadius ν A)
              y).component j))) := by

  exact
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_secondPartial_spatialC3At
      hν U₀ hA hU₀
      (h3FinHeatLerayRestartRadius_pos ν hA)
      le_rfl
      j i k

end

end Euclidean
end Bridge
end PrimeTensor
