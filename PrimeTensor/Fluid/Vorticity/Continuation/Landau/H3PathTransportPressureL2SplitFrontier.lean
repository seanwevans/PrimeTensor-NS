import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathSelectedDuhamelTailRadialL2BKMClosure

/-!
# Split the remaining transport/pressure L² frontier

The selected Duhamel terminal-tail radial `L²` branch is now closed.  The
current H³ BKM continuation theorem therefore retains one spatial mass package
that is still unnecessarily bundled:

    H3PathEnergyClassProducesTransportPressureMemLp2.

Transport and pressure have different analytic origins.  Transport is a
product estimate for the velocity and its spatial derivatives, while pressure
is controlled through the canonical pressure/Leray structure.  Carrying them
as one hypothesis hides which side remains open.

This file separates the package into two exact path-level predicates and proves
that they recombine definitionally into the historical transport/pressure
frontier.  The public BKM theorem is then restated with independent transport
and pressure hypotheses.

No new estimate is introduced here; this is the final structural split before
closing the two remaining spatial mass mechanisms separately.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open Filter
open MeasureTheory

noncomputable section

noncomputable local instance axisFintypeH3PathTransportPressureL2SplitFrontier
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathTransportPressureL2SplitFrontier :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Independent transport and pressure path frontiers -/

/--
Every differentiated transport component through order three belongs to
physical `L²` at every strict H³ energy-class time.
-/
def H3PathEnergyClassProducesTransportMemLp2 : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalH3PathAdmissible u T →
      ∀ a : ℝ,
        ∀ hClass : PreterminalH3EnergyClass u a T,
          ∀ t : ℝ,
            ∀ _ht : t ∈ Set.Ioo a T,
              (
                ∀ j : PrimeTensor.Axis Depth.three,
                  MemLp
                    (momentumTransport0Component
                      (logSpaceTimeVectorField u)
                      t j)
                    2
                    (volume : Measure Point3)
              )
                ∧
              (
                ∀ i j : PrimeTensor.Axis Depth.three,
                  MemLp
                    (momentumTransport1Component
                      (logSpaceTimeVectorField u)
                      t i j)
                    2
                    (volume : Measure Point3)
              )
                ∧
              (
                ∀ i k j : PrimeTensor.Axis Depth.three,
                  MemLp
                    (momentumTransport2Component
                      (logSpaceTimeVectorField u)
                      t i k j)
                    2
                    (volume : Measure Point3)
              )
                ∧
              (
                ∀ i k l j : PrimeTensor.Axis Depth.three,
                  MemLp
                    (momentumTransport3Component
                      (logSpaceTimeVectorField u)
                      t i k l j)
                    2
                    (volume : Measure Point3)
              )

/--
Every differentiated component of the canonical energy-class pressure through
order three belongs to physical `L²` at every strict H³ energy-class time.
-/
def H3PathEnergyClassProducesPressureMemLp2 : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalH3PathAdmissible u T →
      ∀ a : ℝ,
        ∀ hClass : PreterminalH3EnergyClass u a T,
          ∀ t : ℝ,
            ∀ ht : t ∈ Set.Ioo a T,
              (
                ∀ j : PrimeTensor.Axis Depth.three,
                  MemLp
                    (momentumPressure0Component
                      (h3EnergyClassSplitPressureAt hClass ht)
                      t j)
                    2
                    (volume : Measure Point3)
              )
                ∧
              (
                ∀ i j : PrimeTensor.Axis Depth.three,
                  MemLp
                    (momentumPressure1Component
                      (h3EnergyClassSplitPressureAt hClass ht)
                      t i j)
                    2
                    (volume : Measure Point3)
              )
                ∧
              (
                ∀ i k j : PrimeTensor.Axis Depth.three,
                  MemLp
                    (momentumPressure2Component
                      (h3EnergyClassSplitPressureAt hClass ht)
                      t i k j)
                    2
                    (volume : Measure Point3)
              )
                ∧
              (
                ∀ i k l j : PrimeTensor.Axis Depth.three,
                  MemLp
                    (momentumPressure3Component
                      (h3EnergyClassSplitPressureAt hClass ht)
                      t i k l j)
                    2
                    (volume : Measure Point3)
              )

/-! ## Recombine the historical transport/pressure package -/

/-- Independent transport and pressure `L²` packages reconstruct the bundled
historical frontier exactly. -/
theorem h3PathEnergyClassProducesTransportPressureMemLp2_of_transport_of_pressure
    (hTransport :
      H3PathEnergyClassProducesTransportMemLp2)
    (hPressure :
      H3PathEnergyClassProducesPressureMemLp2) :
    H3PathEnergyClassProducesTransportPressureMemLp2 := by

  intro u T hH3 a hClass t ht

  have hT :=
    hTransport u T hH3 a hClass t ht

  have hP :=
    hPressure u T hH3 a hClass t ht

  refine ⟨?_, ?_, ?_, ?_⟩

  · intro j
    exact
      ⟨
        hT.1 j,
        hP.1 j
      ⟩

  · intro i j
    exact
      ⟨
        hT.2.1 i j,
        hP.2.1 i j
      ⟩

  · intro i k j
    exact
      ⟨
        hT.2.2.1 i k j,
        hP.2.2.1 i k j
      ⟩

  · intro i k l j
    exact
      ⟨
        hT.2.2.2 i k l j,
        hP.2.2.2 i k l j
      ⟩

/-! ## BKM closure with transport and pressure separated -/

/--
After closing the selected Duhamel radial tail, the remaining bundled spatial
mass hypothesis can be replaced by independent transport and pressure `L²`
frontiers.
-/
theorem h3PathVorticityL1LinfProducesExtension_of_lowTail_of_derivativeIdentities_of_transport_of_pressure_of_fullScalarEnergy
    (hLow :
      H3PathEnergyClassProducesBKMZerothVelocityL2LateTail)
    (hDerivative :
      H3PathEnergyClassProducesOrderEnergyDerivativeIdentities)
    (hTransport :
      H3PathEnergyClassProducesTransportMemLp2)
    (hPressure :
      H3PathEnergyClassProducesPressureMemLp2)
    (hFull :
      H3PathEnergyClassProducesFullScalarEnergyData) :
    H3PathVorticityL1LinfProducesExtension := by

  exact
    h3PathVorticityL1LinfProducesExtension_of_lowTail_of_derivativeIdentities_of_transportPressure_of_fullScalarEnergy
      hLow
      hDerivative
      (h3PathEnergyClassProducesTransportPressureMemLp2_of_transport_of_pressure
        hTransport hPressure)
      hFull

end

end Euclidean
end Bridge
end PrimeTensor
