import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.RHSPhysicalWeak
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.Curl.Vorticity.JointMeasurable
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Zeroth-order endpoint continuity: joint measurability of the old temporal derivative

The endpoint-independent weak evolution branch has reached the exact physical
`L²` projected RHS and its uniform coordinatewise bound.  To integrate the old
pointwise temporal FTC honestly, the remaining issue is product-space
measurability/integrability of the actual old temporal derivative.

The preterminal regularity package already proves:

* for fixed time, each temporal-derivative coordinate is continuous in space;
* for fixed space, the temporal derivative is the ordinary real `deriv`, hence
  is measurable in time.

The later vorticity branch contains a generic Carathéodory-style construction

    h3PreterminalContinuousSliceExtension

and theorem

    measurable_h3PreterminalContinuousSliceExtension_joint

which combine exactly those sectionwise hypotheses.  We reuse that generic
measure-theoretic infrastructure here.

For each velocity coordinate we therefore obtain a continuous-map-valued zero
extension outside `(0,T)` whose scalar evaluation is jointly measurable on

    ℝ × Point3.

We also package the elapsed-time shift `(r,x) ↦ (t+r,x)`, the compact-test
product integrand, and the spatial norm-mass path.  Thus the measurability half
of the old weak Fubini step is closed endpoint-independently; the next
checkpoint only needs a time-integrable mass envelope.

No endpoint continuity or joint spacetime continuity is asserted.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityZeroOldTemporalJointMeasurable
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3UnitViscosityZeroOldTemporalJointMeasurable :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- For fixed physical point and velocity coordinate, the actual old temporal
derivative is measurable on all absolute times.  This is simply Mathlib's
measurability theorem for `deriv`. -/
theorem measurable_loggedPreterminalTemporalDerivative_time
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) :
    Measurable
      (fun s : ℝ =>
        temporal.d
          (fun q : ℝ =>
            loggedVelocityComponent u q j x)
          s) := by
  simpa only [temporal_d] using
    (measurable_deriv
      (fun q : ℝ =>
        loggedVelocityComponent u q j x))

/-- Continuous-map-valued zero extension of one actual old velocity temporal
derivative coordinate. -/
noncomputable def h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (i : Fin 3)
    (s : ℝ) :
    C(Point3, ℝ) :=
  h3PreterminalContinuousSliceExtension
    T
    (fun r : ℝ =>
      fun x : Point3 =>
        temporal.d
          (fun q : ℝ =>
            loggedVelocityComponent
              u q (h3AxisOfFin3 i) x)
          r)
    (fun r hr =>
      loggedPreterminalTemporalDerivative_continuous_space
        hNS hr (h3AxisOfFin3 i))
    s

/-- On strict preterminal absolute times, the zero extension is the actual old
temporal derivative. -/
@[simp]
theorem h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension_apply_of_mem
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (i : Fin 3)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3) :
    h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension
        hNS i s x
      =
    temporal.d
      (fun q : ℝ =>
        loggedVelocityComponent
          u q (h3AxisOfFin3 i) x)
      s := by
  unfold
    h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension

  exact
    h3PreterminalContinuousSliceExtension_apply_of_mem
      T
      (fun r : ℝ =>
        fun y : Point3 =>
          temporal.d
            (fun q : ℝ =>
              loggedVelocityComponent
                u q (h3AxisOfFin3 i) y)
            r)
      _
      hs x

/-- The zero-extended old temporal derivative coordinate is jointly measurable
in absolute time and physical space. -/
theorem measurable_h3LoggedPreterminalVelocity_temporalDerivative_joint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (i : Fin 3) :
    Measurable
      (fun z : ℝ × Point3 =>
        h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension
          hNS i z.1 z.2) := by
  unfold
    h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension

  exact
    measurable_h3PreterminalContinuousSliceExtension_joint
      T
      (fun r : ℝ =>
        fun x : Point3 =>
          temporal.d
            (fun q : ℝ =>
              loggedVelocityComponent
                u q (h3AxisOfFin3 i) x)
            r)
      (fun x =>
        measurable_loggedPreterminalTemporalDerivative_time
          u x (h3AxisOfFin3 i))
      (fun r hr =>
        loggedPreterminalTemporalDerivative_continuous_space
          hNS hr (h3AxisOfFin3 i))

/-- After shifting from elapsed time to absolute time, the zero-extended old
temporal derivative remains jointly measurable. -/
theorem measurable_h3LoggedPreterminalVelocity_temporalDerivative_onElapsed_joint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (i : Fin 3) :
    Measurable
      (fun z : ℝ × Point3 =>
        h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension
          hNS i (t + z.1) z.2) := by
  have hShift :
      Measurable
        (fun z : ℝ × Point3 =>
          (t + z.1, z.2)) :=
    (measurable_const.add measurable_fst).prodMk
      measurable_snd

  exact
    (measurable_h3LoggedPreterminalVelocity_temporalDerivative_joint
      hNS i).comp hShift

/-- Multiplying the shifted old temporal derivative by one compact smooth test
coordinate preserves joint measurability on elapsed-time/space. -/
theorem measurable_h3WeakTest_mul_loggedPreterminalVelocity_temporalDerivative_onElapsed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (i : Fin 3)
    (ψ : H3WeakTestFunction) :
    Measurable
      (fun z : ℝ × Point3 =>
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ z.2)
          (h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension
            hNS i (t + z.1) z.2)) := by
  have hψ :
      Measurable
        (fun z : ℝ × Point3 =>
          ψ z.2) :=
    ψ.continuous.measurable.comp measurable_snd

  have hD :=
    measurable_h3LoggedPreterminalVelocity_temporalDerivative_onElapsed_joint
      hNS (t := t) i

  have hMul :
      Measurable
        (fun z : ℝ × Point3 =>
          (ψ z.2) *
          h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension
            hNS i (t + z.1) z.2) :=
    hψ.mul hD

  simpa only [
    ContinuousLinearMap.lsmul_apply,
    smul_eq_mul
  ] using hMul

/-- Spatial compact-test norm mass of one zero-extended old temporal derivative
coordinate at elapsed time `r`. -/
noncomputable def h3PreterminalLoggedVelocityTemporalSpatialNormMassOnElapsed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (t : ℝ)
    (i : Fin 3)
    (ψ : H3WeakTestFunction)
    (r : ℝ) :
    ℝ :=
  ∫ x : Point3,
    ‖(ContinuousLinearMap.lsmul ℝ ℝ)
      (ψ x)
      (h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension
        hNS i (t + r) x)‖
    ∂volume

/-- The old velocity temporal spatial norm mass is a.e.-strongly measurable as
a scalar function of elapsed time. -/
theorem h3PreterminalLoggedVelocityTemporalSpatialNormMassOnElapsed_aestronglyMeasurable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (i : Fin 3)
    (ψ : H3WeakTestFunction) :
    AEStronglyMeasurable
      (h3PreterminalLoggedVelocityTemporalSpatialNormMassOnElapsed
        hNS t i ψ)
      (volume : Measure ℝ) := by
  let g : ℝ × Point3 → ℝ :=
    fun z =>
      ‖(ContinuousLinearMap.lsmul ℝ ℝ)
        (ψ z.2)
        (h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension
          hNS i (t + z.1) z.2)‖

  have hgMeas :
      Measurable g := by
    have hBase :=
      measurable_h3WeakTest_mul_loggedPreterminalVelocity_temporalDerivative_onElapsed
        hNS (t := t) i ψ

    have hNorm :
        Measurable
          (fun z : ℝ × Point3 =>
            ‖(ContinuousLinearMap.lsmul ℝ ℝ)
              (ψ z.2)
              (h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension
                hNS i (t + z.1) z.2)‖) :=
      hBase.norm

    simpa only [g] using hNorm

  change
    AEStronglyMeasurable
      (fun r : ℝ =>
        ∫ x : Point3,
          g (r, x)
          ∂volume)
      (volume : Measure ℝ)

  exact
    hgMeas.aestronglyMeasurable.integral_prod_right'

end

end Euclidean
end Bridge
end PrimeTensor
