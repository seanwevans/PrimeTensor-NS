import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.OldSlot1RealSchwartzWeak
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Transport

/-!
# Pressure-free slot1 real-Schwartz integration inputs

`OldSlot1RealSchwartzWeak` closes weak continuity of every first spatial H³ jet
coordinate against arbitrary real Schwartz tests.

To repeat the same spatial weak-derivative argument from slot `1` to slot `2`,
fix indices `j,i,k` and write

    f = ∂ₖ uⱼ,
    g = ∂ᵢ ∂ₖ uⱼ.

The retained H³ tail already gives `f,g ∈ L²`, while a Schwartz test `φ` and
its coordinate derivative `∂ᵢ φ` lie in `L²`.  Hölder therefore provides the
two new `L¹` products needed by Mathlib's line-derivative integration-by-parts
theorem:

    g φ,
    f (∂ᵢ φ).

The third required product `f φ` was already packaged as
`h3PreterminalOldSlot1_transport_mul_realSchwartz_integrable`.

No pressure, temporal derivative, endpoint continuity, or new PDE estimate is
introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  SchwartzMap LineDeriv Distributions

noncomputable section

noncomputable local instance axisFintypeH3ZeroOldSlot1RealSchwartzWeakIntegral
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3ZeroOldSlot1RealSchwartzWeakIntegral :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The old ordered-second spatial coordinate is `L²` at every retained
elapsed time. -/
theorem h3PreterminalOldSlot2_raw_memLp_two
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (j i k : Fin 3) :
    MemLp
      (spatial3.d
        (h3AxisOfFin3 i)
        (spatial3.d
          (h3AxisOfFin3 k)
          (loggedVelocityComponent
            u
            (t + (q : ℝ))
            (h3AxisOfFin3 j))))
      2
      (volume : Measure Point3) := by
  simpa [velocityH3JetFieldAt, h3JetSlot2] using
    (velocityH3JetFieldAt_memLp2
      (h3PreterminalTailIntegrableOnElapsed
        hEnd hTail q)
      (h3PreterminalTailMeasurableOnElapsed
        hNS ht hEnd hTail q)
      (h3JetSlot2 j i k))

/-- The transported ordered-second spatial derivative times a fixed real
Schwartz test is integrable. -/
theorem h3PreterminalOldSlot2_transport_mul_realSchwartz_integrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (j i k : Fin 3) :
    Integrable
      (fun x : H3FourierPoint3 =>
        (ContinuousLinearMap.lsmul ℝ ℝ)
          ((h3TransportScalarField
            (spatial3.d
              (h3AxisOfFin3 i)
              (spatial3.d
                (h3AxisOfFin3 k)
                (loggedVelocityComponent
                  u
                  (t + (q : ℝ))
                  (h3AxisOfFin3 j))))) x)
          (φ x))
      (volume : Measure H3FourierPoint3) := by
  exact
    h3_integrable_bilin_of_memLp_two
      (ContinuousLinearMap.lsmul ℝ ℝ)
      (h3TransportScalarField_memLp2
        (h3PreterminalOldSlot2_raw_memLp_two
          hNS ht hEnd hTail q j i k))
      (φ.memLp 2 (volume : Measure H3FourierPoint3))

/-- The transported old first spatial coordinate `∂ₖ uⱼ` times the coordinate
derivative `∂ᵢ φ` of a real Schwartz test is integrable. -/
theorem h3PreterminalOldSlot1_transport_mul_realSchwartzLineDeriv_integrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (j i k : Fin 3) :
    Integrable
      (fun x : H3FourierPoint3 =>
        (ContinuousLinearMap.lsmul ℝ ℝ)
          ((h3TransportScalarField
            (spatial3.d
              (h3AxisOfFin3 k)
              (loggedVelocityComponent
                u
                (t + (q : ℝ))
                (h3AxisOfFin3 j)))) x)
          ((∂_{h3FourierAxisDirection (h3AxisOfFin3 i)} φ :
              𝓢(H3FourierPoint3, ℝ)) x))
      (volume : Measure H3FourierPoint3) := by
  exact
    h3_integrable_bilin_of_memLp_two
      (ContinuousLinearMap.lsmul ℝ ℝ)
      (h3TransportScalarField_memLp2
        (h3PreterminalOldSlot1_raw_memLp_two
          hNS ht hEnd hTail q j k))
      ((∂_{h3FourierAxisDirection (h3AxisOfFin3 i)} φ :
          𝓢(H3FourierPoint3, ℝ)).memLp
        2 (volume : Measure H3FourierPoint3))

end

end Euclidean
end Bridge
end PrimeTensor
