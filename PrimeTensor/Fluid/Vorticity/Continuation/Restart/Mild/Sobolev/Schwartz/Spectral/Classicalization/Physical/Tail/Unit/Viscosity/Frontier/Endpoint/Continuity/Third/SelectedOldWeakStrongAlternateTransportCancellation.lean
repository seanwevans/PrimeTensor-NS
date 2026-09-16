import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongAlternateTransportSplit
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongAdvectionRepresentatives
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Physical.Incompressibility

/-!
# Alternate weak--strong pure transport cancellation

The alternate convection split is

    (S · ∇)S - (O · ∇)O
      =
    S · ∇D + D · ∇O,

with `D = S - O`.

The existing scalar-transport cancellation theorem was stated for a full
`PreterminalNavierStokes3` velocity because that structure supplied two facts:

* spatial `C¹`;
* pointwise incompressibility.

The selected restart already has both facts independently:

* its physical H³ representative is spatially `C¹`;
* Fourier raw-divergence-free propagation gives pointwise physical
  incompressibility.

This file therefore factors the scalar cancellation through exactly those two
properties, with no pressure and no Navier--Stokes structure on the transporting
field.

After specialization, the selected pure-transport contribution

    ∫ D_j (S · ∇D_j)

vanishes assuming only the corresponding whole-space scalar-flux integral
vanishes.  In particular the old-branch transport IBP datum is no longer
involved.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory
open scoped BigOperators

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongAlternateTransportCancellation
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- For any spatially `C¹`, pointwise incompressible three-dimensional
velocity, the scalar flux identity

    div(v f²) = 2 f (v · ∇f)

holds without requiring a full Navier--Stokes structure. -/
theorem transportScalarFluxDivergenceXYZ_eq_two_mul_transport_of_divergenceFree
    (v :
      PrimeTensor.SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (t : ℝ)
    {f : ScalarField3}
    (hv :
      ∀ k : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun q : Point3 =>
            (v t q).component k))
    (hDiv :
      ∀ x : Point3,
        PrimeTensor.Bridge.RealFluid.divergence
            spatial3 (v t) x
          =
        0)
    (hf : SpatialC1 f)
    (x : Point3) :
    transportScalarFluxDivergenceXYZ
        v t f x
      =
    2 * f x * h3ScalarTransport
        v t f x := by
  have hux :
      SpatialC1
        (fun q : Point3 =>
          (v t q).component xAxis) :=
    hv xAxis

  have huy :
      SpatialC1
        (fun q : Point3 =>
          (v t q).component yAxis) :=
    hv yAxis

  have huz :
      SpatialC1
        (fun q : Point3 =>
          (v t q).component zAxis) :=
    hv zAxis

  have hf2 :
      SpatialC1
        (fun q : Point3 =>
          f q * f q) :=
    hf.mul hf

  have hDivXYZ :
      spatial3.d
          xAxis
          (fun q : Point3 =>
            (v t q).component xAxis)
          x
        +
      (
        spatial3.d
            yAxis
            (fun q : Point3 =>
              (v t q).component yAxis)
            x
          +
        spatial3.d
            zAxis
            (fun q : Point3 =>
              (v t q).component zAxis)
            x
      )
        =
      0 := by
    have h := hDiv x

    unfold PrimeTensor.Bridge.RealFluid.divergence at h
    rw [axis_fold_three] at h

    exact h

  unfold
    transportScalarFluxDivergenceXYZ
    h3ScalarTransport

  rw [
    SpatialC1.spatial3_d_mul
      hux hf2 x xAxis,
    SpatialC1.spatial3_d_mul
      huy hf2 x yAxis,
    SpatialC1.spatial3_d_mul
      huz hf2 x zAxis,
    SpatialC1.spatial3_d_mul
      hf hf x xAxis,
    SpatialC1.spatial3_d_mul
      hf hf x yAxis,
    SpatialC1.spatial3_d_mul
      hf hf x zAxis
  ]

  nlinarith [hDivXYZ]

/-- Generic scalar pure-transport energy cancellation for a spatially `C¹`,
pointwise incompressible transporting velocity. -/
theorem spatialEnergyPairing_scalarTransport_eq_zero_of_divergenceFree
    (v :
      PrimeTensor.SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (t : ℝ)
    {f : ScalarField3}
    (hv :
      ∀ k : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun q : Point3 =>
            (v t q).component k))
    (hDiv :
      ∀ x : Point3,
        PrimeTensor.Bridge.RealFluid.divergence
            spatial3 (v t) x
          =
        0)
    (hf : SpatialC1 f)
    (hFlux :
      TransportScalarFluxVanishesAt
        v t f) :
    spatialEnergyPairing
        f
        (h3ScalarTransport v t f)
      =
    0 := by
  have hPointwise :
      (fun x : Point3 =>
        transportScalarFluxDivergenceXYZ
          v t f x)
        =
      (fun x : Point3 =>
        2 * (f x * h3ScalarTransport v t f x)) := by
    funext x

    simpa [mul_assoc] using
      transportScalarFluxDivergenceXYZ_eq_two_mul_transport_of_divergenceFree
        v t hv hDiv hf x

  have hIntegral :
      (∫ x : Point3,
        2 * (f x * h3ScalarTransport v t f x))
        =
      0 := by
    rw [← hPointwise]

    exact hFlux

  unfold spatialEnergyPairing

  rw [← MeasureTheory.integral_const_mul]

  exact hIntegral

/-- The actual selected weak--strong velocity is pointwise incompressible at
every elapsed time in the closed strict interval. -/
theorem h3PreterminalSelectedWeakStrongVelocity_divergence_eq_zero
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (_hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (q : Set.Icc (0 : ℝ) tau)
    (x : Point3) :
    PrimeTensor.Bridge.RealFluid.divergence
        spatial3
        ((h3PreterminalSelectedWeakStrongVelocity
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail)
          (q : ℝ))
        x
      =
    0 := by
  let qR :=
    h3PreterminalElapsedToSelectedUnitRadius htauR q

  let U :=
    h3PreterminalSelectedUnitSpectralStateOnRadius
      hNS ht hE hTail qR

  have hRaw :
      H3SpectralFinRawDivergenceFree U := by
    dsimp only [U]

    exact
      h3PreterminalSelectedUnitSpectralStateOnRadius_rawDivergenceFree
        hNS ht hE hTail qR

  have hPhysical :
      PrimeTensor.Bridge.RealFluid.divergence
          spatial3
          ((h3SpectralRealVelocityOfPath
            (fun _ : ℝ => U))
            0)
          x
        =
      0 :=
    h3SpectralRealVelocityOfPath_divergence_eq_zero_of_rawDivergenceFree
      (fun _ : ℝ => U)
      0
      hRaw
      x

  have hVelocity :
      h3SpectralRealVelocityOfPath
          (fun _ : ℝ => U)
          0
        =
      (h3PreterminalSelectedWeakStrongVelocity
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail)
        (q : ℝ) := by
    dsimp only [U, qR]

    simpa only [
      h3PreterminalElapsedToSelectedUnitRadius_coe
    ] using
      h3SpectralRealVelocityOfPath_const_selectedUnit_eq_selectedWeakStrong
        hNS ht hE hTail
        (h3PreterminalElapsedToSelectedUnitRadius htauR q)

  rw [hVelocity] at hPhysical

  exact hPhysical

/-- Remaining scalar-flux datum for the selected pure-transport piece in the
alternate weak--strong split.

Unlike the previous route this mentions neither the old preterminal pressure
nor old-branch transport IBP. -/
def H3PreterminalSelectedOldWeakStrongSelectedTransportFluxVanishesAt
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau) : Prop :=
  let selected :=
    h3PreterminalSelectedWeakStrongVelocity
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail

  let old :=
    h3PreterminalOldElapsedWeakStrongVelocity
      u t

  ∀ j : PrimeTensor.Axis Depth.three,
    TransportScalarFluxVanishesAt
      selected
      (q : ℝ)
      (selectedOldVelocityDifferenceComponent
        selected old (q : ℝ) j)

/-- The selected pure-transport component in the alternate split cancels under
only the selected scalar-flux condition. -/
theorem spatialEnergyPairing_selectedTransportDifference_eq_zero
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (q : Set.Icc (0 : ℝ) tau)
    (hFlux :
      H3PreterminalSelectedOldWeakStrongSelectedTransportFluxVanishesAt
        hNS ht hEnd hE hTail q)
    (j : PrimeTensor.Axis Depth.three) :
    let selected :=
      h3PreterminalSelectedWeakStrongVelocity
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail

    let old :=
      h3PreterminalOldElapsedWeakStrongVelocity
        u t

    spatialEnergyPairing
        (selectedOldVelocityDifferenceComponent
          selected old (q : ℝ) j)
        (fun x : Point3 =>
          realAdvectionSelectedTransportDifferenceComponent
            selected old (q : ℝ) x j)
      =
    0 := by
  dsimp only

  let selected :=
    h3PreterminalSelectedWeakStrongVelocity
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail

  let old :=
    h3PreterminalOldElapsedWeakStrongVelocity
      u t

  have hSelected :
      ∀ k : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun x : Point3 =>
            (selected (q : ℝ) x).component k) := by
    intro k
    dsimp only [selected]

    exact
      h3PreterminalSelectedWeakStrongVelocity_component_spatialC1
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail (q : ℝ) k

  have hOld :
      ∀ k : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun x : Point3 =>
            (old (q : ℝ) x).component k) := by
    intro k
    dsimp only [old]

    exact
      h3PreterminalOldElapsedWeakStrongVelocity_component_spatialC1
        hNS ht hEnd hTail q k

  have hf :
      SpatialC1
        (selectedOldVelocityDifferenceComponent
          selected old (q : ℝ) j) :=
    selectedOldVelocityDifferenceComponent_spatialC1
      selected old (q : ℝ) j
      hSelected hOld

  have hDiv :
      ∀ x : Point3,
        PrimeTensor.Bridge.RealFluid.divergence
            spatial3 (selected (q : ℝ)) x
          =
        0 := by
    intro x
    dsimp only [selected]

    exact
      h3PreterminalSelectedWeakStrongVelocity_divergence_eq_zero
        hNS ht hEnd hE hTail htauR q x

  have hCancel :
      spatialEnergyPairing
          (selectedOldVelocityDifferenceComponent
            selected old (q : ℝ) j)
          (h3ScalarTransport
            selected
            (q : ℝ)
            (selectedOldVelocityDifferenceComponent
              selected old (q : ℝ) j))
        =
      0 :=
    spatialEnergyPairing_scalarTransport_eq_zero_of_divergenceFree
      selected
      (q : ℝ)
      hSelected
      hDiv
      hf
      (hFlux j)

  rw [
    ← realAdvectionSelectedTransportDifferenceComponent_eq_scalarTransport
      selected old (q : ℝ) j
  ] at hCancel

  exact hCancel

end

end Euclidean
end Bridge
end PrimeTensor
