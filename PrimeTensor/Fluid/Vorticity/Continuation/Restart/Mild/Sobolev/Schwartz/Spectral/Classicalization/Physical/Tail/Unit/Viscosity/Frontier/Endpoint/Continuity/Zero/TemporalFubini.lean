import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.TemporalPressureFrontier
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.PointwiseFTC
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Zeroth-order endpoint continuity: endpoint-independent old temporal Fubini

`TemporalPressureFrontier` reduced the coordinatewise spacetime-integrability
problem to the old-vs-canonical pressure-gradient defect mass.

This file consumes exactly that product-integrability input and performs the
Fubini step on the old preterminal branch.

For one coordinate and one compact test component,

    ∫ φ_i(x) [∫₀^q ∂ₜu_i(t+r,x) dr] dx
      =
    ∫₀^q ∫ φ_i(x) ∂ₜu_i(t+r,x) dx dr.

The temporal derivative is represented by the measurable continuous-map-valued
zero extension already constructed in `TemporalJointMeasurable`.  On the
physical elapsed interval that extension is the actual old temporal derivative,
so the pointwise FTC from `PointwiseFTC` identifies its primitive with

    u_i(t+q,x) - u_i(t,x).

Thus product integrability yields the exact compact-test velocity-increment
identity without using endpoint `L²` continuity.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityZeroOldTemporalFubini
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3UnitViscosityZeroOldTemporalFubini :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- One coordinate of the old compactly-tested temporal primitive may be
swapped through space and time whenever the endpoint-independent product
integrand is integrable. -/
theorem h3PreterminalLoggedVelocityTemporalCoordinate_fubini_to_of_productIntegrable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (φ : H3WeakTestVector)
    (hq : q ∈ Set.Icc (0 : ℝ) tau)
    (hProd :
      H3PreterminalLoggedVelocityTemporalProductIntegrableTo
        hNS t q φ)
    (i : Fin 3) :
    (∫ x : Point3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ i x)
        (∫ r in (0 : ℝ)..q,
          h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension
            hNS i (t + r) x)
      ∂volume)
      =
    ∫ r in (0 : ℝ)..q,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension
            hNS i (t + r) x)
        ∂volume := by
  let f : ℝ → Point3 → ℝ :=
    fun r x =>
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ i x)
        (h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension
          hNS i (t + r) x)

  have hInt :
      Integrable
        (Function.uncurry f)
        (((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) q)).prod
          (volume : Measure Point3)) := by
    dsimp only [Function.uncurry, f]
    exact hProd i

  have hSwap :=
    integral_integral_swap
      (μ := (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) q))
      (ν := (volume : Measure Point3))
      (f := f)
      hInt

  have hSwapExpanded :
      (∫ r in Set.Ioo (0 : ℝ) q,
        ∫ x : Point3,
          f r x
          ∂volume)
        =
      ∫ x : Point3,
        ∫ r in Set.Ioo (0 : ℝ) q,
          f r x
        ∂volume := by
    simpa only [f] using hSwap

  have hLeft :
      (∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (∫ r in (0 : ℝ)..q,
            h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension
              hNS i (t + r) x)
        ∂volume)
        =
      ∫ x : Point3,
        ∫ r in Set.Ioo (0 : ℝ) q,
          f r x
        ∂volume := by
    apply integral_congr_ae
    filter_upwards with x

    change
      (φ i x) *
          (∫ r in (0 : ℝ)..q,
            h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension
              hNS i (t + r) x)
        =
      ∫ r in Set.Ioo (0 : ℝ) q,
        (φ i x) *
          h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension
            hNS i (t + r) x

    rw [intervalIntegral.integral_of_le hq.1]
    rw [← restrict_Ioo_eq_restrict_Ioc]
    rw [← integral_const_mul]

  have hRight :
      (∫ r in (0 : ℝ)..q,
        ∫ x : Point3,
          f r x
          ∂volume)
        =
      ∫ r in Set.Ioo (0 : ℝ) q,
        ∫ x : Point3,
          f r x
          ∂volume := by
    rw [intervalIntegral.integral_of_le hq.1]
    rw [← restrict_Ioo_eq_restrict_Ioc]

  change
    (∫ x : Point3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ i x)
        (∫ r in (0 : ℝ)..q,
          h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension
            hNS i (t + r) x)
      ∂volume)
      =
    ∫ r in (0 : ℝ)..q,
      ∫ x : Point3,
        f r x
        ∂volume

  calc
    (∫ x : Point3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ i x)
        (∫ r in (0 : ℝ)..q,
          h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension
            hNS i (t + r) x)
      ∂volume)
        =
      ∫ x : Point3,
        ∫ r in Set.Ioo (0 : ℝ) q,
          f r x
        ∂volume :=
      hLeft
    _ =
      ∫ r in Set.Ioo (0 : ℝ) q,
        ∫ x : Point3,
          f r x
          ∂volume :=
      hSwapExpanded.symm
    _ =
      ∫ r in (0 : ℝ)..q,
        ∫ x : Point3,
          f r x
          ∂volume :=
      hRight.symm

/-- On every shortened physical elapsed interval, the temporal zero extension
has exactly the same primitive as the actual old temporal derivative. -/
theorem h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension_intervalIntegral_eq_velocityDifference
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hq : q ∈ Set.Icc (0 : ℝ) tau)
    (i : Fin 3)
    (x : Point3) :
    (∫ r in (0 : ℝ)..q,
      h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension
        hNS i (t + r) x)
      =
    loggedVelocityComponent
        u (t + q) (h3AxisOfFin3 i) x
      -
    loggedVelocityComponent
        u t (h3AxisOfFin3 i) x := by
  let q0 : Set.Icc (0 : ℝ) tau :=
    ⟨0, le_rfl, hq.1.trans hq.2⟩

  let q1 : Set.Icc (0 : ℝ) tau :=
    ⟨q, hq⟩

  have hActual :
      (∫ r in (0 : ℝ)..q,
        temporal.d
          (fun a : ℝ =>
            loggedVelocityComponent
              u a (h3AxisOfFin3 i) x)
          (t + r))
        =
      loggedVelocityComponent
          u (t + q) (h3AxisOfFin3 i) x
        -
      loggedVelocityComponent
          u t (h3AxisOfFin3 i) x := by
    have hFTC :=
      h3PreterminalLoggedVelocityComponent_intervalIntegral_temporalDerivative_between
        hNS ht hEnd hTail
        q0 q1
        (by
          dsimp only [q0, q1]
          exact hq.1)
        i x

    simpa only [q0, q1, add_zero] using hFTC

  have hExtension :
      (∫ r in (0 : ℝ)..q,
        h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension
          hNS i (t + r) x)
        =
      ∫ r in (0 : ℝ)..q,
        temporal.d
          (fun a : ℝ =>
            loggedVelocityComponent
              u a (h3AxisOfFin3 i) x)
          (t + r) := by
    rw [intervalIntegral.integral_of_le hq.1]
    rw [intervalIntegral.integral_of_le hq.1]
    rw [← restrict_Ioo_eq_restrict_Ioc]
    apply integral_congr_ae

    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr

    have hAbs :
        t + r ∈ Set.Ioo (0 : ℝ) T := by
      constructor
      · linarith [ht.1, hr.1]
      · linarith [hEnd, hr.2, hq.2]

    rw [
      h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension_apply_of_mem
        hNS i hAbs x
    ]

  exact hExtension.trans hActual

/-- Product integrability gives the exact compact-test old velocity increment
identity for one coordinate. -/
theorem h3PreterminalLoggedVelocityCoordinate_pairingDifference_eq_intervalIntegral_of_productIntegrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector)
    (hq : q ∈ Set.Icc (0 : ℝ) tau)
    (hProd :
      H3PreterminalLoggedVelocityTemporalProductIntegrableTo
        hNS t q φ)
    (i : Fin 3) :
    (∫ x : Point3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ i x)
        (loggedVelocityComponent
            u (t + q) (h3AxisOfFin3 i) x
          -
        loggedVelocityComponent
            u t (h3AxisOfFin3 i) x)
      ∂volume)
      =
    ∫ r in (0 : ℝ)..q,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension
            hNS i (t + r) x)
        ∂volume := by
  have hPrimitive
      (x : Point3) :
      (∫ r in (0 : ℝ)..q,
        h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension
          hNS i (t + r) x)
        =
      loggedVelocityComponent
          u (t + q) (h3AxisOfFin3 i) x
        -
      loggedVelocityComponent
          u t (h3AxisOfFin3 i) x :=
    h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension_intervalIntegral_eq_velocityDifference
      hNS ht hEnd hTail hq i x

  calc
    (∫ x : Point3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ i x)
        (loggedVelocityComponent
            u (t + q) (h3AxisOfFin3 i) x
          -
        loggedVelocityComponent
            u t (h3AxisOfFin3 i) x)
      ∂volume)
        =
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (∫ r in (0 : ℝ)..q,
            h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension
              hNS i (t + r) x)
        ∂volume := by
          apply integral_congr_ae
          filter_upwards with x
          rw [hPrimitive x]
    _ =
      ∫ r in (0 : ℝ)..q,
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension
              hNS i (t + r) x)
          ∂volume :=
      h3PreterminalLoggedVelocityTemporalCoordinate_fubini_to_of_productIntegrable
        hNS φ hq hProd i

/-- The pressure-defect mass frontier from `TemporalPressureFrontier` therefore
immediately supplies the coordinatewise weak FTC identity. -/
theorem h3PreterminalLoggedVelocityCoordinate_pairingDifference_eq_intervalIntegral_of_pressureDefect
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector)
    (hq : q ∈ Set.Icc (0 : ℝ) tau)
    (hPressure :
      H3PreterminalTailCanonicalZeroPressureGradientDefectSpatialNormMassUniformlyBoundedOnElapsed
        hNS ht hEnd hTail φ)
    (i : Fin 3) :
    (∫ x : Point3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ i x)
        (loggedVelocityComponent
            u (t + q) (h3AxisOfFin3 i) x
          -
        loggedVelocityComponent
            u t (h3AxisOfFin3 i) x)
      ∂volume)
      =
    ∫ r in (0 : ℝ)..q,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension
            hNS i (t + r) x)
        ∂volume := by
  apply
    h3PreterminalLoggedVelocityCoordinate_pairingDifference_eq_intervalIntegral_of_productIntegrable
      hNS ht hEnd hTail φ hq

  exact
    H3PreterminalLoggedVelocityTemporalProductIntegrableTo_of_pressureDefect
      hNS ht hEnd hE hTail φ
      hq.1 hq.2 hPressure

end

end Euclidean
end Bridge
end PrimeTensor
