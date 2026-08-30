import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedInitialState
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Spectral.Realizability

/-!
# Classicalization: selected initial decoder

`SelectedInitialState` proves that the Banach-selected restart path begins
exactly at its supplied weighted spectral state.

For the canonical continuation construction that supplied state is not
arbitrary: it is the genuine H³ spectral encoding of a preterminal velocity
slice.  This file closes the corresponding decoder endpoint.

There are three representation layers.

1. `h3ToFourierRealL2` and `h3FromFourierRealL2` are inverse transports
   between the ordinary `Point3` carrier and the Euclidean Fourier carrier.
2. The existing encoder/decoder round trip identifies the real decoder of a
   genuinely encoded spectral state with the transported zeroth H³ jet slot.
3. The zeroth H³ jet slot is exactly the logged velocity component, as an
   `L²` equivalence class.

Consequently the classical real `C¹` representative of an encoded snapshot is
almost everywhere equal to the original logged velocity component on
`Point3`.  Combining this with `W 0 = U₀` gives the same endpoint identity for
the selected restart velocity.

No pointwise upgrade is needed here.  The frontier's decoder-matching
predicate is itself an a.e. spatial statement, and the later global `C³`
packaging can choose the original classical slice exactly at the restart
interface.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzClassicalizationSelectedInitialDecoder
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

noncomputable local instance point3MeasureSpaceH3SchwartzClassicalizationSelectedInitialDecoder :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Transporting a real `L²(Point3)` class to the Euclidean `PiLp 2` carrier
and immediately transporting it back recovers the original class exactly. -/
@[simp]
theorem h3FromFourierRealL2_h3ToFourierRealL2
    (f : H3ScalarL2) :
    h3FromFourierRealL2 (h3ToFourierRealL2 f) = f := by
  apply MeasureTheory.Lp.ext

  have hFrom :
      ((h3FromFourierRealL2
          (h3ToFourierRealL2 f) : H3ScalarL2) :
        Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        (h3ToFourierRealL2 f : H3FourierPoint3 → ℝ)
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)) := by
    unfold h3FromFourierRealL2
    exact
      MeasureTheory.Lp.coeFn_compMeasurePreserving
        (h3ToFourierRealL2 f)
        (PiLp.volume_preserving_toLp
          (PrimeTensor.Axis Depth.three))

  have hTo :
      ((h3ToFourierRealL2 f : H3FourierRealL2) :
        H3FourierPoint3 → ℝ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        (f : Point3 → ℝ)
          (WithLp.ofLp ξ)) := by
    unfold h3ToFourierRealL2
    exact
      MeasureTheory.Lp.coeFn_compMeasurePreserving
        f
        (PiLp.volume_preserving_ofLp
          (PrimeTensor.Axis Depth.three))

  have hToComp :
      (fun x : Point3 =>
        (h3ToFourierRealL2 f : H3FourierPoint3 → ℝ)
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x))
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        (f : Point3 → ℝ)
          (WithLp.ofLp
            ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x))) := by
    exact
      (PiLp.volume_preserving_toLp
        (PrimeTensor.Axis Depth.three)).quasiMeasurePreserving.ae_eq_comp
          hTo

  filter_upwards [hFrom, hToComp] with x hxFrom hxTo

  rw [hxFrom, hxTo]

/-- The real `Point3` decoder of a genuine encoded H³ snapshot is exactly the
zeroth H³ jet `L²` class. -/
theorem h3FromFourierRealL2_h3SpectralVelocityDecodeRealL2_velocityH3SpectralStateAt_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j : Fin 3) :
    h3FromFourierRealL2
        (h3SpectralVelocityDecodeRealL2
          (velocityH3SpectralStateAt u t hInt hMeas hFourier)
          j)
      =
    velocityH3L2JetAt
      u t hInt hMeas
      (h3JetSlot0 j) := by
  rw [
    h3SpectralVelocityDecodeRealL2_velocityH3SpectralStateAt_apply_eq
      hFourier j,
    h3FromFourierRealL2_h3ToFourierRealL2
  ]

/-- The zeroth concrete H³ jet slot is represented almost everywhere by the
corresponding logged velocity component. -/
theorem velocityH3L2JetAt_slot0_ae_eq_loggedVelocityComponent
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (j : Fin 3) :
    ((velocityH3L2JetAt
        u t hInt hMeas
        (h3JetSlot0 j) : H3ScalarL2) :
      Point3 → ℝ)
      =ᵐ[(volume : Measure Point3)]
    loggedVelocityComponent
      u t (h3AxisOfFin3 j) := by
  unfold velocityH3L2JetAt
  dsimp only

  simpa [
    velocityH3JetFieldAt,
    h3JetSlot0
  ] using
    (MeasureTheory.MemLp.coeFn_toLp
      (velocityH3JetFieldAt_memLp2
        hInt hMeas (h3JetSlot0 j)))

/-- The classical real `Point3` representative of a genuine encoded H³
snapshot agrees almost everywhere with the original logged velocity
component. -/
theorem h3SpectralVelocityRealC1RepresentativeOnPoint3_velocityH3SpectralStateAt_ae_eq_loggedVelocityComponent
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j : Fin 3) :
    h3SpectralVelocityRealC1RepresentativeOnPoint3
        (velocityH3SpectralStateAt
          u t hInt hMeas hFourier)
        j
      =ᵐ[(volume : Measure Point3)]
    loggedVelocityComponent
      u t (h3AxisOfFin3 j) := by
  have hRep :=
    h3SpectralVelocityRealC1RepresentativeOnPoint3_ae_eq_decodeRealL2
      (velocityH3SpectralStateAt
        u t hInt hMeas hFourier)
      j

  have hDecode :
      h3FromFourierRealL2
          (h3SpectralVelocityDecodeRealL2
            (velocityH3SpectralStateAt
              u t hInt hMeas hFourier)
            j)
        =
      velocityH3L2JetAt
        u t hInt hMeas
        (h3JetSlot0 j) :=
    h3FromFourierRealL2_h3SpectralVelocityDecodeRealL2_velocityH3SpectralStateAt_eq
      hFourier j

  rw [hDecode] at hRep

  exact
    hRep.trans
      (velocityH3L2JetAt_slot0_ae_eq_loggedVelocityComponent
        hInt hMeas j)

/-- If the selected restart path is launched from a genuine encoded H³
snapshot, its packaged real velocity at restart time zero agrees a.e. with the
original logged velocity component. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_zero_ae_eq_loggedVelocityComponent
    {ν A t : ℝ}
    (hν : 0 < ν)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (hA : 0 < A)
    (hU₀ :
      ‖velocityH3SpectralStateAt
          u t hInt hMeas hFourier‖ ≤ A)
    (j : Fin 3) :
    (fun x : Point3 =>
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
        hν
        (velocityH3SpectralStateAt
          u t hInt hMeas hFourier)
        hA
        hU₀
        0
        x).component
          (h3AxisOfFin3 j))
      =ᵐ[(volume : Measure Point3)]
    loggedVelocityComponent
      u t (h3AxisOfFin3 j) := by
  have hZero :
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν
          (velocityH3SpectralStateAt
            u t hInt hMeas hFourier)
          hA
          hU₀
          0
        =
      velocityH3SpectralStateAt
        u t hInt hMeas hFourier :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_zero
      hν
      (velocityH3SpectralStateAt
        u t hInt hMeas hFourier)
      hA
      hU₀

  have hRep :=
    h3SpectralVelocityRealC1RepresentativeOnPoint3_velocityH3SpectralStateAt_ae_eq_loggedVelocityComponent
      hFourier j

  filter_upwards [hRep] with x hx

  unfold
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity

  rw [
    h3SpectralRealVelocityOfPath_component_h3AxisOfFin3,
    hZero
  ]

  exact hx

end
end Euclidean
end Bridge
end PrimeTensor
