import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.OldSlot2RealSchwartzWeak
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Transport

/-!
# Pressure-free slot2 real-Schwartz integration inputs

`OldSlot2RealSchwartzWeak` closes weak continuity of every ordered-second H³ jet
coordinate against arbitrary real Schwartz tests.

For the final spatial weak-derivative step, fix indices `j,i,k,l` and write

    f = ∂ₖ∂ₗ uⱼ,
    g = ∂ᵢ∂ₖ∂ₗ uⱼ.

The retained H³ tail places both `f` and `g` in `L²`.  Since a real Schwartz
test `φ` and its coordinate derivative `∂ᵢ φ` are also in `L²`, Hölder gives

    g φ,
    f (∂ᵢ φ)

in `L¹`.  The third product `f φ` is already provided by
`h3PreterminalOldSlot2_transport_mul_realSchwartz_integrable`.

This is the last integrability checkpoint before arbitrary real-Schwartz weak
continuity of the full ordered H³ jet.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  SchwartzMap LineDeriv Distributions

noncomputable section

noncomputable local instance axisFintypeH3ZeroOldSlot2RealSchwartzWeakIntegral
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3ZeroOldSlot2RealSchwartzWeakIntegral :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The old ordered-third spatial coordinate is `L²` at every retained elapsed
time. -/
theorem h3PreterminalOldSlot3_raw_memLp_two
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (j i k l : Fin 3) :
    MemLp
      (spatial3.d
        (h3AxisOfFin3 i)
        (spatial3.d
          (h3AxisOfFin3 k)
          (spatial3.d
            (h3AxisOfFin3 l)
            (loggedVelocityComponent
              u
              (t + (q : ℝ))
              (h3AxisOfFin3 j)))))
      2
      (volume : Measure Point3) := by
  simpa [velocityH3JetFieldAt, h3JetSlot3] using
    (velocityH3JetFieldAt_memLp2
      (h3PreterminalTailIntegrableOnElapsed
        hEnd hTail q)
      (h3PreterminalTailMeasurableOnElapsed
        hNS ht hEnd hTail q)
      (h3JetSlot3 j i k l))

/-- The transported ordered-third spatial derivative times a fixed real
Schwartz test is integrable. -/
theorem h3PreterminalOldSlot3_transport_mul_realSchwartz_integrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (j i k l : Fin 3) :
    Integrable
      (fun x : H3FourierPoint3 =>
        (ContinuousLinearMap.lsmul ℝ ℝ)
          ((h3TransportScalarField
            (spatial3.d
              (h3AxisOfFin3 i)
              (spatial3.d
                (h3AxisOfFin3 k)
                (spatial3.d
                  (h3AxisOfFin3 l)
                  (loggedVelocityComponent
                    u
                    (t + (q : ℝ))
                    (h3AxisOfFin3 j)))))) x)
          (φ x))
      (volume : Measure H3FourierPoint3) := by
  exact
    h3_integrable_bilin_of_memLp_two
      (ContinuousLinearMap.lsmul ℝ ℝ)
      (h3TransportScalarField_memLp2
        (h3PreterminalOldSlot3_raw_memLp_two
          hNS ht hEnd hTail q j i k l))
      (φ.memLp 2 (volume : Measure H3FourierPoint3))

/-- The transported old ordered-second coordinate `∂ₖ∂ₗ uⱼ` times the
coordinate derivative `∂ᵢ φ` of a real Schwartz test is integrable. -/
theorem h3PreterminalOldSlot2_transport_mul_realSchwartzLineDeriv_integrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (j i k l : Fin 3) :
    Integrable
      (fun x : H3FourierPoint3 =>
        (ContinuousLinearMap.lsmul ℝ ℝ)
          ((h3TransportScalarField
            (spatial3.d
              (h3AxisOfFin3 k)
              (spatial3.d
                (h3AxisOfFin3 l)
                (loggedVelocityComponent
                  u
                  (t + (q : ℝ))
                  (h3AxisOfFin3 j))))) x)
          ((∂_{h3FourierAxisDirection (h3AxisOfFin3 i)} φ :
              𝓢(H3FourierPoint3, ℝ)) x))
      (volume : Measure H3FourierPoint3) := by
  exact
    h3_integrable_bilin_of_memLp_two
      (ContinuousLinearMap.lsmul ℝ ℝ)
      (h3TransportScalarField_memLp2
        (h3PreterminalOldSlot2_raw_memLp_two
          hNS ht hEnd hTail q j k l))
      ((∂_{h3FourierAxisDirection (h3AxisOfFin3 i)} φ :
          𝓢(H3FourierPoint3, ℝ)).memLp
        2 (volume : Measure H3FourierPoint3))

end

end Euclidean
end Bridge
end PrimeTensor
