import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Subinterval.Consistency
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Initial.Decoder

/-!
# Classicalization: preterminal spectral overlap witnesses

The selected restart is now known to be consistent on every shorter positive
subinterval.  Therefore overlap uniqueness can be reduced to a local
preterminal spectral statement at one elapsed time at a time.

For a positive elapsed time `τ`, a preterminal overlap witness consists of a
bounded continuous spectral H³ path on `[0,τ]` which

* stays in the same `2A` Picard ball;
* satisfies the restarted heat--Leray mild equation from the anchor state
  `U₀`;
* decodes at its right endpoint to the old logged velocity at absolute time
  `t + τ`.

No uniqueness is included in the witness.  The existing Banach uniqueness
theorem supplies that automatically.

The main theorem of this file proves that such witnesses at every positive
overlap time imply
`H3SelectedRestartDecoderAgreesWithPreterminalOnOverlap`.

The zero elapsed-time case is discharged separately from the exact initial
state and encoder/decoder round-trip already proved in
`SelectedInitialDecoder`.

Thus the remaining PDE-side problem is isolated cleanly: construct these local
preterminal spectral witnesses from the classical Navier--Stokes solution.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzClassicalizationPreterminalOverlapWitness
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

noncomputable local instance point3MeasureSpaceH3SchwartzClassicalizationPreterminalOverlapWitness :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- A local spectral realization of the old preterminal solution on one
positive elapsed interval `[0,τ]`.

The mild identity is stated in exactly the form consumed by
`h3SpectralFinHeatLerayPhysicalOverlap_normalized_unique`. -/
def H3PreterminalSpectralOverlapWitnessAt
    (ν A : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t τ : ℝ)
    (hτ : 0 ≤ τ) : Prop :=
  ∃ P : H3SpectralPhysicalVelocityPath τ,
    (∀ q : Set.Icc (0 : ℝ) τ,
      ‖P q‖ ≤ 2 * A)
      ∧
    (∀ s : H3UnitTime,
      h3SpectralVelocityHeatApplyNN
          ν hν.le
          (h3PhysicalTimeNN τ hτ s)
          U₀
        -
      h3SpectralFinHeatLerayDuhamel
          ν
          (h3PhysicalTime τ s)
          hν
          (h3PathPhysicalRealExtension
            τ
            (h3SpectralNormalizedPathOfPhysical hτ P))
          (h3PathPhysicalRealExtension
            τ
            (h3SpectralNormalizedPathOfPhysical hτ P))
        =
      P (h3PhysicalTimeMap τ hτ s))
      ∧
    ∀ j : Fin 3,
      ∀ᵐ x : Point3 ∂volume,
        h3FromFourierRealL2
            (h3SpectralVelocityDecodeRealL2
              (P (h3PhysicalTimeMap τ hτ h3UnitTimeOne))
              j)
            x
          =
        (logSpaceTimeVectorField
            u
            (t + τ)
            x).component
          (h3AxisOfFin3 j)

/-- A positive local preterminal spectral witness has the same endpoint state
as the canonical-radius selected restart.

The proof is purely uniqueness bookkeeping:

1. Banach uniqueness identifies the witness path with the directly selected
   `τ`-solution.
2. subinterval consistency identifies the canonical-radius restriction with
   that same `τ`-solution;
3. evaluate both normalized paths at time one. -/
theorem h3PreterminalSpectralOverlapWitnessAt_endpoint_eq_selected
    {ν A t τ : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (hτ : 0 < τ)
    (hτR : τ ≤ h3FinHeatLerayRestartRadius ν A)
    (hWitness :
      H3PreterminalSpectralOverlapWitnessAt
        ν A hν U₀ u t τ hτ.le) :
    ∃ P : H3SpectralPhysicalVelocityPath τ,
      (∀ j : Fin 3,
        ∀ᵐ x : Point3 ∂volume,
          h3FromFourierRealL2
              (h3SpectralVelocityDecodeRealL2
                (P (h3PhysicalTimeMap τ hτ.le h3UnitTimeOne))
                j)
              x
            =
          (logSpaceTimeVectorField
              u
              (t + τ)
              x).component
            (h3AxisOfFin3 j))
        ∧
      P (h3PhysicalTimeMap τ hτ.le h3UnitTimeOne)
        =
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀ τ := by
  rcases hWitness with
    ⟨P, hPbound, hPmild, hPdecode⟩

  have hsmall :
      8 * h3HeatLerayDuhamelPathCoefficient ν * A * Real.sqrt τ
        ≤
      1 :=
    h3FinHeatLerayRestartRadius_smallness_of_le
      hA hτ.le hτR

  have hUnique :
      h3SpectralNormalizedPathOfPhysical hτ.le P
        =
      h3SpectralFinHeatLerayMildSolution
        hν hτ.le U₀ hA hU₀ hsmall :=
    h3SpectralFinHeatLerayPhysicalOverlap_normalized_unique
      hν hτ.le U₀ hA hU₀ hsmall
      P hPbound hPmild

  have hRestrict :
      h3SpectralNormalizedPathOfPhysical
          hτ.le
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRestrictPhysical
            hν U₀ hA hU₀ hτ.le)
        =
      h3SpectralFinHeatLerayMildSolution
        hν hτ.le U₀ hA hU₀ hsmall := by
    simpa only using
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_normalized_restrict_eq
        hν U₀ hA hU₀ hτ hτR

  have hPaths :
      h3SpectralNormalizedPathOfPhysical hτ.le P
        =
      h3SpectralNormalizedPathOfPhysical
        hτ.le
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRestrictPhysical
          hν U₀ hA hU₀ hτ.le) :=
    hUnique.trans hRestrict.symm

  have hAtOne :=
    congrArg
      (fun V : H3SpectralVelocityPath => V h3UnitTimeOne)
      hPaths

  have hAtOne' :
      P (h3PhysicalTimeMap τ hτ.le h3UnitTimeOne)
        =
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
        ((h3PhysicalTimeMap τ hτ.le h3UnitTimeOne : Set.Icc (0 : ℝ) τ) : ℝ) := by
    simpa only [
      h3SpectralNormalizedPathOfPhysical_apply,
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRestrictPhysical_apply
    ] using hAtOne

  have hEndTime :
      ((h3PhysicalTimeMap τ hτ.le h3UnitTimeOne : Set.Icc (0 : ℝ) τ) : ℝ)
        =
      τ := by
    change h3PhysicalTime τ h3UnitTimeOne = τ
    exact h3PhysicalTime_one τ

  rw [hEndTime] at hAtOne'

  have hEndpoint :
      P (h3PhysicalTimeMap τ hτ.le h3UnitTimeOne)
        =
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀ τ :=
    hAtOne'

  exact
    ⟨P, hPdecode, hEndpoint⟩

/-- Local preterminal spectral witnesses at every positive overlap time imply
the exact decoder-overlap predicate needed by the gluing theorem.

The only exceptional elapsed time is zero, where the selected state is exactly
the encoded anchor state and the encoder/decoder round-trip identifies it with
the old logged slice. -/
theorem h3SelectedRestartDecoderAgreesWithPreterminalOnOverlap_of_witnesses
    {ν A t T : ℝ}
    (hν : 0 < ν)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (hA : 0 < A)
    (hU₀ :
      ‖velocityH3SpectralStateAt
          u t hInt hMeas hFourier‖ ≤ A)
    (hWitness :
      ∀ q : Set.Icc
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν A),
        0 < (q : ℝ) →
        t + (q : ℝ) < T →
        H3PreterminalSpectralOverlapWitnessAt
          ν A hν
          (velocityH3SpectralStateAt
            u t hInt hMeas hFourier)
          u t (q : ℝ) q.property.1) :
    H3SelectedRestartDecoderAgreesWithPreterminalOnOverlap
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν
        (velocityH3SpectralStateAt
          u t hInt hMeas hFourier)
        hA
        hU₀)
      u
      t
      T
      (h3FinHeatLerayRestartRadius ν A) := by
  intro q j hBefore

  by_cases hqZero : (q : ℝ) = 0

  · have hZero :
        h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν
            (velocityH3SpectralStateAt
              u t hInt hMeas hFourier)
            hA
            hU₀
            (q : ℝ)
          =
        velocityH3SpectralStateAt
          u t hInt hMeas hFourier := by
      rw [hqZero]
      exact
        h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_zero
          hν
          (velocityH3SpectralStateAt
            u t hInt hMeas hFourier)
          hA
          hU₀

    have hDecode :
        ((velocityH3L2JetAt
            u t hInt hMeas
            (h3JetSlot0 j) : H3ScalarL2) :
          Point3 → ℝ)
          =ᵐ[(volume : Measure Point3)]
        loggedVelocityComponent
          u t (h3AxisOfFin3 j) :=
      velocityH3L2JetAt_slot0_ae_eq_loggedVelocityComponent
        hInt hMeas j

    filter_upwards [hDecode] with x hx

    rw [hZero]

    rw [
      h3FromFourierRealL2_h3SpectralVelocityDecodeRealL2_velocityH3SpectralStateAt_eq
        hFourier j
    ]

    rw [hqZero, add_zero]

    change
      ((velocityH3L2JetAt
          u t hInt hMeas
          (h3JetSlot0 j) : H3ScalarL2) :
        Point3 → ℝ) x
        =
      loggedVelocityComponent
        u t (h3AxisOfFin3 j) x

    exact hx

  · have hqPos : 0 < (q : ℝ) :=
      lt_of_le_of_ne
        q.property.1
        (Ne.symm hqZero)

    rcases
      h3PreterminalSpectralOverlapWitnessAt_endpoint_eq_selected
        hν
        (velocityH3SpectralStateAt
          u t hInt hMeas hFourier)
        hA
        hU₀
        u
        hqPos
        q.property.2
        (hWitness q hqPos hBefore)
    with
      ⟨P, hPdecode, hEndpoint⟩

    have hAE := hPdecode j

    rw [hEndpoint] at hAE

    exact hAE

end
end Euclidean
end Bridge
end PrimeTensor
