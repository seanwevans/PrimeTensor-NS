import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathTemporalJetL2Frontier
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.EnergyDerivativeMajorantOnly

/-!
# Reduce temporal-jet L² membership to square-integrability

The preceding frontier asks for the complete temporal H³ jet to belong to
physical `L²`.

Inside `PreterminalH3EnergyClass`, measurability of that temporal jet is not a
genuine whole-space hypothesis.  The high-order spatial regularity of velocity
and pressure makes the momentum RHS continuous through order three, while the
preterminal momentum identities identify those fields with the corresponding
spatial derivatives of `∂ₜu`.

Thus the only remaining content of temporal-jet `L²` membership is

    ∫ |D^α ∂ₜu|² < ∞,    |α| ≤ 3.

This file packages that square-integrability frontier and proves that it
implies `H3TemporalJetMemLp2At`, hence the temporal pairing frontier and the
downstream BKM closure.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open Filter
open MeasureTheory

noncomputable section

noncomputable local instance axisFintypeH3PathTemporalJetSquareFrontier
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathTemporalJetSquareFrontier :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Small continuity helpers -/

private theorem spatialC1_spatial_d_continuous_temporalJetSquare
    {f : ScalarField3}
    (hf : SpatialC1 f)
    (i : PrimeTensor.Axis Depth.three) :
    Continuous (spatial3.d i f) := by

  have hfun :
      (fun x : Point3 => partialDeriv i f x)
        =
      (fun x : Point3 =>
        (fderiv ℝ f x) (axisDirection i)) := by
    funext x
    exact
      PrimeTensor.Bridge.Euclidean.SpatialC1.partialDeriv_eq_fderiv_axisDirection
        hf x i

  change Continuous (fun x : Point3 => partialDeriv i f x)
  rw [hfun]

  have hfd :
      ContDiff ℝ 0 (fderiv ℝ f) := by
    unfold SpatialC1 at hf
    exact hf.fderiv_right (by norm_num)

  exact
    (hfd.clm_apply contDiff_const).continuous

private theorem spatialC1_of_spatialC3_temporalJetSquare
    {f : ScalarField3}
    (hf : SpatialC3 f) :
    SpatialC1 f := by
  unfold SpatialC3 at hf
  unfold SpatialC1
  exact hf.of_le (by norm_num)

private theorem firstPartial_spatialC1_of_spatialC3_temporalJetSquare
    {f : ScalarField3}
    (hf : SpatialC3 f)
    (i : PrimeTensor.Axis Depth.three) :
    SpatialC1 (spatial3.d i f) := by

  have h2 :
      SpatialC2
        (fun x : Point3 => partialDeriv i f x) :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_contDiff_two
      hf i

  change SpatialC1 (fun x : Point3 => partialDeriv i f x)
  exact h2.of_le (by norm_num)

/-! ## Temporal-jet measurability is automatic in the energy class -/

/--
All four temporal H³ jet levels are strongly measurable at an interior
energy-class time.

This is local regularity only; no whole-space decay or integrability is used.
-/
theorem h3TemporalJet_aestronglyMeasurable_of_energyClass
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    (
      ∀ j : PrimeTensor.Axis Depth.three,
        AEStronglyMeasurable
          (loggedVelocityTemporalComponent u t j)
          (volume : Measure Point3)
    )
      ∧
    (
      ∀ i j : PrimeTensor.Axis Depth.three,
        AEStronglyMeasurable
          (spatial3.d i
            (loggedVelocityTemporalComponent u t j))
          (volume : Measure Point3)
    )
      ∧
    (
      ∀ i k j : PrimeTensor.Axis Depth.three,
        AEStronglyMeasurable
          (spatial3.d i
            (spatial3.d k
              (loggedVelocityTemporalComponent u t j)))
          (volume : Measure Point3)
    )
      ∧
    (
      ∀ i k l j : PrimeTensor.Axis Depth.three,
        AEStronglyMeasurable
          (spatial3.d i
            (spatial3.d k
              (spatial3.d l
                (loggedVelocityTemporalComponent u t j))))
          (volume : Measure Point3)
    ) := by

  rcases
    preterminalH3EnergyClass_produces_splitRegularity
      hClass ht
  with
    ⟨p, hPDE, hRegular⟩

  have htPre :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      lt_trans hClass.terminal_start.1 ht.1,
      ht.2
    ⟩

  have htTail :
      t ∈ Set.Ico a T :=
    ⟨ht.1.le, ht.2⟩

  refine ⟨?_, ?_, ?_, ?_⟩

  · intro j

    let f : ScalarField3 :=
      loggedVelocityComponent u t j

    have hxx :
        Continuous
          (spatial3.d xAxis
            (spatial3.d xAxis f)) :=
      (hClass.velocity_spatial_five
        t htTail j xAxis xAxis).continuous

    have hyy :
        Continuous
          (spatial3.d yAxis
            (spatial3.d yAxis f)) :=
      (hClass.velocity_spatial_five
        t htTail j yAxis yAxis).continuous

    have hzz :
        Continuous
          (spatial3.d zAxis
            (spatial3.d zAxis f)) :=
      (hClass.velocity_spatial_five
        t htTail j zAxis zAxis).continuous

    have hLap :
        Continuous
          (PrimeTensor.Bridge.RealFluid.laplacian
            spatial3 f) := by
      have hEq :
          PrimeTensor.Bridge.RealFluid.laplacian
              spatial3 f
            =
          fun x : Point3 =>
            spatial3.d xAxis
                (spatial3.d xAxis f) x
              +
            (spatial3.d yAxis
                (spatial3.d yAxis f) x
              +
             spatial3.d zAxis
                (spatial3.d zAxis f) x) := by
        funext x
        exact laplacian3_eq f x
      rw [hEq]
      exact hxx.add (hyy.add hzz)

    have hBaseC1
        (m : PrimeTensor.Axis Depth.three) :
        SpatialC1
          (fun x : Point3 =>
            (logSpaceTimeVectorField u t x).component m) :=
      spatialC1_of_spatialC3_temporalJetSquare
        (hPDE.regularity.velocity_spatial_three
          t htPre m)

    have hFirstC1
        (m r : PrimeTensor.Axis Depth.three) :
        SpatialC1
          (spatial3.d r
            (fun x : Point3 =>
              (logSpaceTimeVectorField u t x).component m)) :=
      firstPartial_spatialC1_of_spatialC3_temporalJetSquare
        (hPDE.regularity.velocity_spatial_three
          t htPre m)
        r

    have hTransport :
        Continuous
          (fun x : Point3 =>
            realAdvectionComponent
              (logSpaceTimeVectorField u)
              t x j) := by
      unfold realAdvectionComponent
      exact
        ((hBaseC1 xAxis).continuous.mul
          (hFirstC1 j xAxis).continuous).add
          (((hBaseC1 yAxis).continuous.mul
              (hFirstC1 j yAxis).continuous).add
            ((hBaseC1 zAxis).continuous.mul
              (hFirstC1 j zAxis).continuous))

    rcases hClass.pressure_witness with
    ⟨pClass, hPDEClass, hp4⟩

    have hPressure :
        Continuous (spatial3.d j (pClass t)) :=
      (hp4 t htTail j).continuous

    have hRHS :
        Continuous
          (momentumRHS0Component
            (logSpaceTimeVectorField u)
            pClass t j) := by
      unfold momentumRHS0Component
      dsimp only [f] at hLap
      exact
        (hLap.sub hTransport).sub hPressure

    have hEq :
        loggedVelocityTemporalComponent u t j
          =
        momentumRHS0Component
          (logSpaceTimeVectorField u)
          pClass t j :=
      loggedVelocityTemporalComponent_eq_momentumRHS0
        hPDEClass htPre j

    rw [hEq]
    exact hRHS.aestronglyMeasurable

  · intro i j

    have hRHS :
        SpatialC1
          (momentumRHS1Component
            (logSpaceTimeVectorField u)
            p t i j) := by
      rw [momentumRHS1Component_eq_split]
      exact
        (hRegular.1 i j).2.2.1.sub
          (hRegular.1 i j).2.2.2

    have hEq :
        spatial3.d i
            (loggedVelocityTemporalComponent u t j)
          =
        momentumRHS1Component
          (logSpaceTimeVectorField u)
          p t i j :=
      spatial_d_loggedVelocityTemporalComponent_eq_momentumRHS1
        hPDE htPre i j

    rw [hEq]
    exact hRHS.continuous.aestronglyMeasurable

  · intro i k j

    have hRHS :
        SpatialC1
          (momentumRHS2Component
            (logSpaceTimeVectorField u)
            p t i k j) := by
      rw [
        momentumRHS2Component_eq_split_of_spatialC1
          hRegular i k j
      ]
      exact
        (hRegular.2 i k j).2.2.1.sub
          (hRegular.2 i k j).2.2.2

    have hEq :
        spatial3.d i
            (spatial3.d k
              (loggedVelocityTemporalComponent u t j))
          =
        momentumRHS2Component
          (logSpaceTimeVectorField u)
          p t i k j :=
      spatial_d2_loggedVelocityTemporalComponent_eq_momentumRHS2
        hPDE htPre i k j

    rw [hEq]
    exact hRHS.continuous.aestronglyMeasurable

  · intro i k l j

    have hReg2 :=
      hRegular.2 k l j

    have hDiffusion :
        Continuous
          (momentumDiffusion3Component
            (logSpaceTimeVectorField u)
            t i k l j) := by
      unfold momentumDiffusion3Component
      exact
        spatialC1_spatial_d_continuous_temporalJetSquare
          hReg2.1 i

    have hTransport :
        Continuous
          (momentumTransport3Component
            (logSpaceTimeVectorField u)
            t i k l j) := by
      unfold momentumTransport3Component
      exact
        spatialC1_spatial_d_continuous_temporalJetSquare
          hReg2.2.1 i

    have hPressure :
        Continuous
          (momentumPressure3Component
            p t i k l j) := by
      unfold momentumPressure3Component
      exact
        spatialC1_spatial_d_continuous_temporalJetSquare
          hReg2.2.2.2 i

    have hRHS :
        Continuous
          (momentumRHS3Component
            (logSpaceTimeVectorField u)
            p t i k l j) := by
      rw [
        momentumRHS3Component_eq_split_of_spatialC1
          hRegular i k l j
      ]
      exact
        (hDiffusion.sub hTransport).sub hPressure

    have hEq :
        spatial3.d i
            (spatial3.d k
              (spatial3.d l
                (loggedVelocityTemporalComponent u t j)))
          =
        momentumRHS3Component
          (logSpaceTimeVectorField u)
          p t i k l j :=
      spatial_d3_loggedVelocityTemporalComponent_eq_momentumRHS3
        hPDE htPre i k l j

    rw [hEq]
    exact hRHS.aestronglyMeasurable

/-! ## Exact square-integrability frontier -/

/--
Square-integrability of the complete temporal H³ jet at one time.
-/
def H3TemporalJetSquareIntegrableAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) : Prop :=
  (
    ∀ j : PrimeTensor.Axis Depth.three,
      SpatialL2SquareIntegrable
        (loggedVelocityTemporalComponent u t j)
  )
    ∧
  (
    ∀ i j : PrimeTensor.Axis Depth.three,
      SpatialL2SquareIntegrable
        (spatial3.d i
          (loggedVelocityTemporalComponent u t j))
  )
    ∧
  (
    ∀ i k j : PrimeTensor.Axis Depth.three,
      SpatialL2SquareIntegrable
        (spatial3.d i
          (spatial3.d k
            (loggedVelocityTemporalComponent u t j)))
  )
    ∧
  (
    ∀ i k l j : PrimeTensor.Axis Depth.three,
      SpatialL2SquareIntegrable
        (spatial3.d i
          (spatial3.d k
            (spatial3.d l
              (loggedVelocityTemporalComponent u t j))))
  )

/--
Path-level square-integrability frontier for the temporal H³ jet.
-/
def H3PathEnergyClassProducesTemporalJetSquareIntegrability : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalH3PathAdmissible u T →
      ∀ a : ℝ,
        ∀ hClass : PreterminalH3EnergyClass u a T,
          ∀ t : ℝ,
            t ∈ Set.Ioo a T →
              H3TemporalJetSquareIntegrableAt u t

/-! ## Square-integrability gives the L² frontier -/

/--
At one energy-class time, temporal-jet square-integrability is exactly enough
to obtain temporal-jet `L²` membership, because measurability is automatic.
-/
theorem h3TemporalJetMemLp2At_of_squareIntegrable_of_energyClass
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hSquare : H3TemporalJetSquareIntegrableAt u t) :
    H3TemporalJetMemLp2At u t := by

  have hMeas :=
    h3TemporalJet_aestronglyMeasurable_of_energyClass
      hClass ht

  refine ⟨?_, ?_, ?_, ?_⟩

  · intro j
    simpa using
      (memLp_two_of_spatialL2SquareIntegrable
        (hMeas.1 j)
        (hSquare.1 j))

  · intro i j
    simpa using
      (memLp_two_of_spatialL2SquareIntegrable
        (hMeas.2.1 i j)
        (hSquare.2.1 i j))

  · intro i k j
    simpa using
      (memLp_two_of_spatialL2SquareIntegrable
        (hMeas.2.2.1 i k j)
        (hSquare.2.2.1 i k j))

  · intro i k l j
    simpa using
      (memLp_two_of_spatialL2SquareIntegrable
        (hMeas.2.2.2 i k l j)
        (hSquare.2.2.2 i k l j))

/--
Path-level temporal-jet square-integrability implies path-level temporal-jet
`L²` membership.
-/
theorem h3PathEnergyClassProducesTemporalJetMemLp2_of_squareIntegrability
    (hSquare :
      H3PathEnergyClassProducesTemporalJetSquareIntegrability) :
    H3PathEnergyClassProducesTemporalJetMemLp2 := by

  intro u T hH3 a hClass t ht

  exact
    h3TemporalJetMemLp2At_of_squareIntegrable_of_energyClass
      hClass
      ht
      (hSquare u T hH3 a hClass t ht)

/-! ## BKM closure at the square-integrability frontier -/

/--
BKM continuation with the temporal side reduced to square-integrability of the
complete temporal H³ jet.
-/
theorem h3PathVorticityL1LinfProducesExtension_of_lowTail_of_derivativeIdentities_of_temporalJetSquareIntegrability_of_fullScalarEnergy
    (hLow :
      H3PathEnergyClassProducesBKMZerothVelocityL2LateTail)
    (hDerivative :
      H3PathEnergyClassProducesOrderEnergyDerivativeIdentities)
    (hTemporal :
      H3PathEnergyClassProducesTemporalJetSquareIntegrability)
    (hFull :
      H3PathEnergyClassProducesFullScalarEnergyData) :
    H3PathVorticityL1LinfProducesExtension := by

  exact
    h3PathVorticityL1LinfProducesExtension_of_lowTail_of_derivativeIdentities_of_temporalJetMemLp2_of_fullScalarEnergy
      hLow
      hDerivative
      (h3PathEnergyClassProducesTemporalJetMemLp2_of_squareIntegrability
        hTemporal)
      hFull

end

end Euclidean
end Bridge
end PrimeTensor
