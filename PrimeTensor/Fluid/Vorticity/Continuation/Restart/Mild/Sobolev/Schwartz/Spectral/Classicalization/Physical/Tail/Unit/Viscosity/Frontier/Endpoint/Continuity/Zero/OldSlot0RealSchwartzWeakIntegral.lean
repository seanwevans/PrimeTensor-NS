import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.OldSlot0RealSchwartzWeakDeriv
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Transport

/-!
# Pressure-free slot0 real-Schwartz integration inputs

`OldSlot0RealSchwartzWeakDeriv` packages continuity of the transported old
zeroth endpoint coordinate against arbitrary real Schwartz tests and their
coordinate derivatives.

The next spatial integration-by-parts step needs three genuine `L¹` products
on the Euclidean carrier.  For a fixed retained elapsed snapshot, write `f` for
one old velocity component and `∂ᵢ f` for one spatial coordinate derivative.
The H³ tail already places both fields in `L²`.  A Schwartz test `φ` and its
coordinate derivative `∂ᵢ φ` are also in `L²`.  Hölder therefore gives
integrability of

    (∂ᵢ f) φ,    f (∂ᵢ φ),    f φ.

This file records those three inputs after transporting the physical fields to
the Euclidean carrier.  No pressure, temporal derivative, endpoint continuity,
or additional PDE estimate is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  SchwartzMap LineDeriv Distributions

noncomputable section

noncomputable local instance axisFintypeH3ZeroOldSlot0RealSchwartzWeakIntegral
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3ZeroOldSlot0RealSchwartzWeakIntegral :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The old zeroth velocity coordinate at every retained elapsed time is `L²`
on the physical carrier. -/
theorem h3PreterminalOldSlot0_raw_memLp_two
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (j : Fin 3) :
    MemLp
      (loggedVelocityComponent
        u
        (t + (q : ℝ))
        (h3AxisOfFin3 j))
      2
      (volume : Measure Point3) := by
  simpa [velocityH3JetFieldAt, h3JetSlot0] using
    (velocityH3JetFieldAt_memLp2
      (h3PreterminalTailIntegrableOnElapsed
        hEnd hTail q)
      (h3PreterminalTailMeasurableOnElapsed
        hNS ht hEnd hTail q)
      (h3JetSlot0 j))

/-- The corresponding old first spatial coordinate derivative is `L²` at every
retained elapsed time. -/
theorem h3PreterminalOldSlot1_raw_memLp_two
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (j i : Fin 3) :
    MemLp
      (spatial3.d
        (h3AxisOfFin3 i)
        (loggedVelocityComponent
          u
          (t + (q : ℝ))
          (h3AxisOfFin3 j)))
      2
      (volume : Measure Point3) := by
  simpa [velocityH3JetFieldAt, h3JetSlot1] using
    (velocityH3JetFieldAt_memLp2
      (h3PreterminalTailIntegrableOnElapsed
        hEnd hTail q)
      (h3PreterminalTailMeasurableOnElapsed
        hNS ht hEnd hTail q)
      (h3JetSlot1 j i))

/-- The transported first spatial derivative times a fixed real Schwartz test
is integrable. -/
theorem h3PreterminalOldSlot1_transport_mul_realSchwartz_integrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (j i : Fin 3) :
    Integrable
      (fun x : H3FourierPoint3 =>
        (ContinuousLinearMap.lsmul ℝ ℝ)
          ((h3TransportScalarField
            (spatial3.d
              (h3AxisOfFin3 i)
              (loggedVelocityComponent
                u
                (t + (q : ℝ))
                (h3AxisOfFin3 j)))) x)
          (φ x))
      (volume : Measure H3FourierPoint3) := by
  exact
    h3_integrable_bilin_of_memLp_two
      (ContinuousLinearMap.lsmul ℝ ℝ)
      (h3TransportScalarField_memLp2
        (h3PreterminalOldSlot1_raw_memLp_two
          hNS ht hEnd hTail q j i))
      (φ.memLp 2 (volume : Measure H3FourierPoint3))

/-- The transported old zeroth coordinate times a coordinate derivative of a
real Schwartz test is integrable. -/
theorem h3PreterminalOldSlot0_transport_mul_realSchwartzLineDeriv_integrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (j i : Fin 3) :
    Integrable
      (fun x : H3FourierPoint3 =>
        (ContinuousLinearMap.lsmul ℝ ℝ)
          ((h3TransportScalarField
            (loggedVelocityComponent
              u
              (t + (q : ℝ))
              (h3AxisOfFin3 j))) x)
          ((∂_{h3FourierAxisDirection (h3AxisOfFin3 i)} φ :
              𝓢(H3FourierPoint3, ℝ)) x))
      (volume : Measure H3FourierPoint3) := by
  exact
    h3_integrable_bilin_of_memLp_two
      (ContinuousLinearMap.lsmul ℝ ℝ)
      (h3TransportScalarField_memLp2
        (h3PreterminalOldSlot0_raw_memLp_two
          hNS ht hEnd hTail q j))
      ((∂_{h3FourierAxisDirection (h3AxisOfFin3 i)} φ :
          𝓢(H3FourierPoint3, ℝ)).memLp
        2 (volume : Measure H3FourierPoint3))

/-- The transported old zeroth coordinate times the undifferentiated real
Schwartz test is integrable.  This is the third product required by the generic
line-derivative integration-by-parts theorem. -/
theorem h3PreterminalOldSlot0_transport_mul_realSchwartz_integrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (j : Fin 3) :
    Integrable
      (fun x : H3FourierPoint3 =>
        (ContinuousLinearMap.lsmul ℝ ℝ)
          ((h3TransportScalarField
            (loggedVelocityComponent
              u
              (t + (q : ℝ))
              (h3AxisOfFin3 j))) x)
          (φ x))
      (volume : Measure H3FourierPoint3) := by
  exact
    h3_integrable_bilin_of_memLp_two
      (ContinuousLinearMap.lsmul ℝ ℝ)
      (h3TransportScalarField_memLp2
        (h3PreterminalOldSlot0_raw_memLp_two
          hNS ht hEnd hTail q j))
      (φ.memLp 2 (volume : Measure H3FourierPoint3))

end

end Euclidean
end Bridge
end PrimeTensor
