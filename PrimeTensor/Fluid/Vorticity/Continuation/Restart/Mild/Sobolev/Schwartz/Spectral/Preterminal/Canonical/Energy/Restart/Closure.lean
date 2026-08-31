import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Encoded.Canonical.Energy.Restart.Closure
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fourier.Compatibility

/-!
# Preterminal canonical-energy spectral restart closure

The canonical-energy encoded restart theorem still carried two snapshot-side
proof objects which are absent from the classical continuation interface:

* `VelocityH3MeasurableAt`;
* `VelocityH3FourierCompatibleAt`.

For an interior slice of `LoggedPreterminalNavierStokesAdmissible`, neither is
an additional analytic hypothesis.  The preterminal Navier--Stokes structure
already supplies spatial `C³` regularity of every logged velocity component.
That regularity makes the component and all coordinate derivatives through
order three continuous (hence strongly measurable), and the existing
`FourierCompatibility` bridge then supplies the exact Fourier derivative
identities.

Consequently the canonical-energy restart construction can now be invoked from
exactly the snapshot hypotheses appearing in `UniformCanonicalH3RealRestartLifespan`:
preterminal admissibility, an interior time, H³ integrability, and a normalized
energy ceiling.  The remaining gap to the real restart proposition is therefore
only the classical physical-field reconstruction / pressure / C³ gluing step.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology BigOperators

noncomputable section

noncomputable local instance axisFintypeH3PreterminalCanonicalRestart
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PreterminalCanonicalRestart :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- A coordinate derivative of a spatially `C¹` field is continuous. -/
private theorem spatialC1_spatial_d_continuous
    {f : ScalarField3}
    (hf : SpatialC1 f)
    (i : PrimeTensor.Axis Depth.three) :
    Continuous (spatial3.d i f) := by
  have hfun :
      (fun x : Point3 => partialDeriv i f x)
        =
      (fun x : Point3 => (fderiv ℝ f x) (axisDirection i)) := by
    funext x
    exact
      PrimeTensor.Bridge.Euclidean.SpatialC1.partialDeriv_eq_fderiv_axisDirection
        hf x i

  change Continuous (fun x : Point3 => partialDeriv i f x)
  rw [hfun]

  have hfd : ContDiff ℝ 0 (fderiv ℝ f) := by
    unfold SpatialC1 at hf
    exact hf.fderiv_right (by norm_num)

  exact
    (hfd.clm_apply contDiff_const).continuous

/-- Spatial `C³` regularity supplies all measurability required by the concrete
H³ `L²` jet bridge. -/
theorem velocityH3MeasurableAt_of_spatialC3
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hSpatial :
      ∀ j : PrimeTensor.Axis Depth.three,
        SpatialC3 (loggedVelocityComponent u t j)) :
    VelocityH3MeasurableAt u t := by
  intro j
  let f : ScalarField3 := loggedVelocityComponent u t j

  have hf3 : SpatialC3 f := by
    simpa only [f] using hSpatial j

  dsimp only [f]
  refine ⟨?_, ?_, ?_, ?_⟩

  · exact hf3.continuous.aestronglyMeasurable

  · intro i
    have hdi2 : SpatialC2 (spatial3.d i f) := by
      change SpatialC2 (fun x : Point3 => partialDeriv i f x)
      exact
        PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_contDiff_two
          hf3 i
    exact hdi2.continuous.aestronglyMeasurable

  · intro i k
    have hdk2 : SpatialC2 (spatial3.d k f) := by
      change SpatialC2 (fun x : Point3 => partialDeriv k f x)
      exact
        PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_contDiff_two
          hf3 k

    have hdik1 : SpatialC1 (spatial3.d i (spatial3.d k f)) := by
      change
        SpatialC1
          (fun x : Point3 =>
            partialDeriv i (spatial3.d k f) x)
      exact
        PrimeTensor.Bridge.Euclidean.SpatialC2.partialDeriv_contDiff_one
          hdk2 i

    exact hdik1.continuous.aestronglyMeasurable

  · intro i k l
    have hdl2 : SpatialC2 (spatial3.d l f) := by
      change SpatialC2 (fun x : Point3 => partialDeriv l f x)
      exact
        PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_contDiff_two
          hf3 l

    have hkdl1 : SpatialC1 (spatial3.d k (spatial3.d l f)) := by
      change
        SpatialC1
          (fun x : Point3 =>
            partialDeriv k (spatial3.d l f) x)
      exact
        PrimeTensor.Bridge.Euclidean.SpatialC2.partialDeriv_contDiff_one
          hdl2 k

    exact
      (spatialC1_spatial_d_continuous hkdl1 i).aestronglyMeasurable

/-- Every interior slice of a logged preterminal classical solution satisfies
the concrete H³ measurability predicate. -/
theorem velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    VelocityH3MeasurableAt u t := by
  rcases hNS with ⟨p, hp⟩

  apply velocityH3MeasurableAt_of_spatialC3
  intro j

  change
    SpatialC3
      (fun x : Point3 =>
        (logSpaceTimeVectorField u t x).component j)
  exact hp.regularity.velocity_spatial_three t ht j

/-- Every H³-integrable interior slice of a logged preterminal classical
solution satisfies the exact Fourier derivative compatibility predicate. -/
theorem velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hInt : VelocityH3IntegrableAt u t) :
    let hMeas : VelocityH3MeasurableAt u t :=
      velocityH3MeasurableAt_of_loggedPreterminalNavierStokes hNS ht
    VelocityH3FourierCompatibleAt u t hInt hMeas := by
  dsimp only

  apply
    velocityH3FourierCompatibleAt_of_spatialC3
      (hInt := hInt)
      (hMeas := velocityH3MeasurableAt_of_loggedPreterminalNavierStokes hNS ht)

  rcases hNS with ⟨p, hp⟩
  intro j
  change
    SpatialC3
      (fun x : Point3 =>
        (logSpaceTimeVectorField u t x).component j)
  exact hp.regularity.velocity_spatial_three t ht j

/-- Canonical-energy spectral restart closure from exactly the snapshot-side
hypotheses of the classical uniform restart-lifespan interface.

The theorem returns the automatically generated measurability and Fourier
compatibility witnesses together with the full canonical-radius physically
realized signed mild step. -/
theorem h3SpectralPreterminalCanonicalEnergyRestart_fullStep_realized
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hInt : VelocityH3IntegrableAt u t)
    (hEnergy : velocityH3EnergyAt u t ≤ E) :
    ∃
      (hMeas : VelocityH3MeasurableAt u t)
      (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas),
      let hEpos : 0 < E := lt_of_lt_of_le zero_lt_one hE
      let U₀ : H3SpectralVelocityState :=
        velocityH3SpectralStateAt u t hInt hMeas hFourier
      let R : NNReal := h3FinHeatLerayRestartRadiusNN ν E hEpos
      let W : ℝ → H3SpectralFinVectorState :=
        h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hEpos
            (norm_velocityH3SpectralStateAt_le_energyCeiling
              hFourier hE hEnergy)
      let D : H3SpectralFinVectorState :=
        h3SpectralFinHeatLerayDuhamelRestartRemainder
          ν 0 hν W W R
      (∀ j : Fin 3,
        h3SpectralVelocityDecodeRealL2 U₀ j
          = h3ToFourierRealL2
              (velocityH3L2JetAt u t hInt hMeas (h3JetSlot0 j)))
        ∧
      (
        h3SpectralFinVectorDecodeComplexL2 (W (R : ℝ))
            = h3ComplexPhysicalVelocityHeatApplyNN ν hν.le R (W 0)
              - h3SpectralFinVectorDecodeComplexL2 D
          ∧
        h3SpectralFinVectorDecodeComplexL2 D
            ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization
                ν (R : ℝ) hν
      ) := by
  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes hNS ht

  let hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hNS ht hInt

  refine ⟨hMeas, hFourier, ?_⟩

  exact
    h3SpectralEncodedCanonicalEnergyRestart_fullStep_realized
      hν hFourier hE hEnergy

/-- The canonical positive spectral restart radius is therefore available from
the exact hypotheses of the classical canonical-energy lifespan interface. -/
theorem h3SpectralPreterminalCanonicalEnergyRestartRadius_pos
    {ν E : ℝ}
    (hν : 0 < ν)
    (hE : 1 ≤ E) :
    0 < h3FinHeatLerayRestartRadius ν E := by
  exact h3SpectralEncodedCanonicalEnergyRestartRadius_pos hν hE

end

end Euclidean
end Bridge
end PrimeTensor
