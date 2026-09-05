import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Overlap.Gluing
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Spatial.Regularity

/-!
# Classicalization: pointwise selected/preterminal overlap

The overlap uniqueness stack currently produces equality almost everywhere in
space between

* the canonical real `L²` decoder of the selected restart, and
* the old logged preterminal velocity.

At every *positive* restart time both sides have continuous, in fact spatially
`C³`, representatives:

* the selected inverse-Fourier representative is spatially `C³` by positive
  time smoothing;
* the old logged velocity is spatially `C³` because it is still strictly
  preterminal.

For Euclidean volume, equality almost everywhere between continuous functions
is equality everywhere.  This file performs that upgrade coordinatewise.

This is the key seam-removal step for later gluing regularity: on every
positive genuine overlap slice, the classical selected representative and the
old classical branch are literally the same spatial function, not merely the
same `L²` class.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzClassicalizationPhysicalTailPointwiseOverlap
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- At every strictly positive selected time still lying before the old
terminal time, one selected real velocity component agrees pointwise in space
with the corresponding old logged component.

The a.e. overlap theorem supplies equality of `L²` representatives.  Spatial
`C³` on both sides then upgrades that equality to equality of the actual
continuous functions. -/
theorem h3PreterminalTailCanonicalSelectedRestart_component_eq_old_on_positiveOverlap
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEvolution :
      H3PreterminalTailPhysicalEvolutionOnRestartRadius
        ν E hν u T t hNS ht hE hTail)
    (q : Set.Icc
      (0 : ℝ)
      (h3FinHeatLerayRestartRadius ν E))
    (hq : 0 < (q : ℝ))
    (hBefore : t + (q : ℝ) < T)
    (i : Fin 3) :
    (fun x : Point3 =>
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
        hν
        (h3PreterminalTailCanonicalAnchorSpectralState
          hNS ht hTail)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
          hNS ht hE hTail)
        (q : ℝ)
        x).component
          (h3AxisOfFin3 i))
      =
    (fun x : Point3 =>
      (logSpaceTimeVectorField
        u
        (t + (q : ℝ))
        x).component
          (h3AxisOfFin3 i)) := by
  let U₀ : H3SpectralVelocityState :=
    h3PreterminalTailCanonicalAnchorSpectralState
      hNS ht hTail

  let hEpos : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalTailCanonicalAnchorSpectralState_le
      hNS ht hE hTail

  have hOverlap :
      H3SelectedRestartDecoderAgreesWithPreterminalOnOverlap
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hEpos hU₀)
        u
        t
        T
        (h3FinHeatLerayRestartRadius ν E) := by
    have hCanonical :=
      h3PreterminalTailCanonicalSelectedRestart_decoderAgreesOnOverlap
        hν hNS ht hE hTail hEvolution

    simpa only [
      U₀,
      hEpos,
      hU₀,
      h3PreterminalTailCanonicalSelectedRestart
    ] using hCanonical

  have hDecoderOld :
      (fun x : Point3 =>
        h3FromFourierRealL2
          (h3SpectralVelocityDecodeRealL2
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν U₀ hEpos hU₀ (q : ℝ))
            i)
          x)
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        (logSpaceTimeVectorField
          u
          (t + (q : ℝ))
          x).component
            (h3AxisOfFin3 i)) :=
    hOverlap q i hBefore

  have hRepresentativeDecoder :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_velocityRealC1RepresentativeOnPoint3_ae_eq_decodeRealL2
      (s := (q : ℝ))
      hν U₀ hEpos hU₀ i

  have hSelectedDecoder :
      (fun x : Point3 =>
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
          hν U₀ hEpos hU₀ (q : ℝ) x).component
            (h3AxisOfFin3 i))
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        h3FromFourierRealL2
          (h3SpectralVelocityDecodeRealL2
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν U₀ hEpos hU₀ (q : ℝ))
            i)
          x) := by
    simpa only [
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity,
      h3SpectralRealVelocityOfPath_component_h3AxisOfFin3
    ] using hRepresentativeDecoder

  have hSelectedOld :
      (fun x : Point3 =>
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
          hν U₀ hEpos hU₀ (q : ℝ) x).component
            (h3AxisOfFin3 i))
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        (logSpaceTimeVectorField
          u
          (t + (q : ℝ))
          x).component
            (h3AxisOfFin3 i)) :=
    hSelectedDecoder.trans hDecoderOld

  have hSelectedC3 :
      SpatialC3
        (fun x : Point3 =>
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
            hν U₀ hEpos hU₀ (q : ℝ) x).component
              (h3AxisOfFin3 i)) :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_spatialC3At
      hν U₀ hEpos hU₀
      hq
      q.property.2
      (h3AxisOfFin3 i)

  let p :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  have hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        p
        T :=
    Classical.choose_spec hNS

  have hOldTime :
      t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) T := by
    exact
      ⟨
        by linarith [ht.1, q.property.1],
        hBefore
      ⟩

  have hOldC3 :
      SpatialC3
        (fun x : Point3 =>
          (logSpaceTimeVectorField
            u
            (t + (q : ℝ))
            x).component
              (h3AxisOfFin3 i)) :=
    hPDE.regularity.velocity_spatial_three
      (t + (q : ℝ))
      hOldTime
      (h3AxisOfFin3 i)

  unfold SpatialC3 at hSelectedC3 hOldC3

  have hPointwise :
      (fun x : Point3 =>
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
          hν U₀ hEpos hU₀ (q : ℝ) x).component
            (h3AxisOfFin3 i))
        =
      (fun x : Point3 =>
        (logSpaceTimeVectorField
          u
          (t + (q : ℝ))
          x).component
            (h3AxisOfFin3 i)) :=
    MeasureTheory.Measure.eq_of_ae_eq
      hSelectedOld
      hSelectedC3.continuous
      hOldC3.continuous

  simpa only [
    U₀,
    hEpos,
    hU₀
  ] using hPointwise

/-- Pointwise form of the same theorem at an individual spatial point. -/
theorem h3PreterminalTailCanonicalSelectedRestart_component_apply_eq_old_on_positiveOverlap
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEvolution :
      H3PreterminalTailPhysicalEvolutionOnRestartRadius
        ν E hν u T t hNS ht hE hTail)
    (q : Set.Icc
      (0 : ℝ)
      (h3FinHeatLerayRestartRadius ν E))
    (hq : 0 < (q : ℝ))
    (hBefore : t + (q : ℝ) < T)
    (i : Fin 3)
    (x : Point3) :
    (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
      hν
      (h3PreterminalTailCanonicalAnchorSpectralState
        hNS ht hTail)
      (lt_of_lt_of_le zero_lt_one hE)
      (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
        hNS ht hE hTail)
      (q : ℝ)
      x).component
        (h3AxisOfFin3 i)
      =
    (logSpaceTimeVectorField
      u
      (t + (q : ℝ))
      x).component
        (h3AxisOfFin3 i) := by
  have hFunctions :=
    h3PreterminalTailCanonicalSelectedRestart_component_eq_old_on_positiveOverlap
      hν hNS ht hE hTail hEvolution
      q hq hBefore i

  exact congrFun hFunctions x

end
end Euclidean
end Bridge
end PrimeTensor
