import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathSelectedPhysicalL2EnergyDerivative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.TemporalProjectedRHSMass
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedPhysicalUniquenessFrontier

/-!
# Selected physical L² energy: bridge to the old zeroth-order component sum

The selected physical Hilbert path now has an exact scalar kinetic-energy
Derivative.  To transport that identity to the old H³ path, first remove the
remaining representation layer.

At any positive selected/old overlap time, physical agreement identifies the
selected smooth representative with the old logged velocity pointwise.  The
selected decoder is almost everywhere equal to that smooth representative, so
each selected physical `L²` coordinate has exactly the old component's spatial
square energy.

Summing the three `Fin 3` coordinates gives

    ‖S(q)‖²
      = Σ i : Fin 3, spatialSquareEnergy (u_{axis(i)}(t+q)).

The next bookkeeping step can reindex this finite sum over
`Axis Depth.three`, yielding `velocityH3Energy0At` literally.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3PathSelectedPhysicalL2EnergyOldBridge
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathSelectedPhysicalL2EnergyOldBridge :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Under pointwise selected/old physical agreement, the selected physical
Hilbert norm square is exactly the sum of the three old zeroth-order component
energies. -/
theorem norm_sq_h3PreterminalSelectedVelocityPhysicalL2HilbertAt_eq_old_fin3_energy
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hAgreement :
      H3PreterminalSelectedPhysicalAgreementAt
        (one_pos : (0 : ℝ) < 1)
        q
        hNS ht hE hTail) :
    ‖h3PreterminalSelectedVelocityPhysicalL2HilbertAt
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail q‖ ^ 2
      =
    ∑ i : Fin 3,
      spatialSquareEnergy
        (loggedVelocityComponent u (t + q) (h3AxisOfFin3 i)) := by
  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState
      hNS ht hTail

  let hEpos : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht hE hTail

  let S : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalSelectedVelocityPhysicalL2HilbertAt
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail q

  have hNorm :
      ‖S‖ ^ 2
        =
      ∑ i : Fin 3, ‖S i‖ ^ 2 := by
    exact
      PiLp.norm_sq_eq_of_L2
        (fun _ : Fin 3 => H3ScalarL2)
        S

  rw [show
    ‖h3PreterminalSelectedVelocityPhysicalL2HilbertAt
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail q‖ ^ 2 = ‖S‖ ^ 2 by rfl]
  rw [hNorm]

  apply Finset.sum_congr rfl
  intro i hi

  have hSelectedDecoder :
      (fun x : Point3 =>
        (S i : H3ScalarL2) x)
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
          (one_pos : (0 : ℝ) < 1)
          U₀ hEpos hU₀ q x).component
            (h3AxisOfFin3 i)) := by
    have hRep :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_velocityRealC1RepresentativeOnPoint3_ae_eq_decodeRealL2
        (s := q)
        (one_pos : (0 : ℝ) < 1)
        U₀ hEpos hU₀ i

    symm
    simpa only [
      S,
      h3PreterminalSelectedVelocityPhysicalL2HilbertAt,
      PiLp.toLp_apply,
      U₀,
      hEpos,
      hU₀,
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity,
      h3SpectralRealVelocityOfPath_component_h3AxisOfFin3
    ] using hRep

  have hSelectedOld :
      (fun x : Point3 =>
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
          (one_pos : (0 : ℝ) < 1)
          U₀ hEpos hU₀ q x).component
            (h3AxisOfFin3 i))
        =ᵐ[(volume : Measure Point3)]
      loggedVelocityComponent
        u (t + q) (h3AxisOfFin3 i) := by
    exact
      Filter.Eventually.of_forall
        (fun x => by
          simpa only [
            U₀,
            hEpos,
            hU₀,
            h3PreterminalSelectedDecoderAnchorState,
            loggedVelocityComponent
          ] using hAgreement i x)

  have hSOld :
      (fun x : Point3 => (S i : H3ScalarL2) x)
        =ᵐ[(volume : Measure Point3)]
      loggedVelocityComponent
        u (t + q) (h3AxisOfFin3 i) :=
    hSelectedDecoder.trans hSelectedOld

  rw [h3ScalarL2_norm_sq_eq_spatialSquareEnergy_coe]
  unfold spatialSquareEnergy

  apply integral_congr_ae
  filter_upwards [hSOld] with x hx
  rw [hx]

end

end Euclidean
end Bridge
end PrimeTensor
