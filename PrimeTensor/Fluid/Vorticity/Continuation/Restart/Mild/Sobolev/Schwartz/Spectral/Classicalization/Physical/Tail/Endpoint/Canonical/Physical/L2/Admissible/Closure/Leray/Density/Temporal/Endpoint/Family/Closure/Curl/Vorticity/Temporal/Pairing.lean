import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.Curl.Vorticity.FTC
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Weak.Pairing.Integral

/-!
# Curl-test temporal pairings are vorticity temporal pairings

The product-space/Fubini and scalar FTC seams for the three vorticity
components are now closed.

The older weak-temporal layer already identifies the finite sum of compact-test
pointwise velocity temporal-derivative pairings with the projected RHS at every
strict elapsed time.  For the three elementary curl tests, that finite sum has
a much simpler spatial interpretation:

    curl01(ψ)  ->   <ψ, ∂ₜω_z>,
    curl02(ψ)  -> - <ψ, ∂ₜω_y>,
    curl12(ψ)  ->   <ψ, ∂ₜω_x>.

This file proves exactly those three strict-time identities.  The proof uses
only:

* the endpoint representative temporal derivative equals the old absolute-time
  derivative;
* the old temporal velocity derivative is spatially `C¹`, by the classical
  momentum equation;
* one spatial integration by parts;
* time differentiation commutes with classical vorticity.

The next increment can integrate these identities in elapsed time and close the
three `Curl.Integrated` hypotheses directly.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3EndpointCurlVorticityTemporalPairing
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3EndpointCurlVorticityTemporalPairing :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)


@[simp]
theorem h3WeakTestFunction_neg_apply_endpointCurlVorticityTemporalPairing
    (φ : H3WeakTestFunction)
    (x : Point3) :
    ((-φ : H3WeakTestFunction) x) = -(φ x) := by
  rfl

@[simp]
theorem h3WeakTestFunction_zero_apply_endpointCurlVorticityTemporalPairing
    (x : Point3) :
    ((0 : H3WeakTestFunction) x) = 0 := by
  rfl

/-- At one strict old preterminal time, a velocity temporal-derivative
coordinate is spatially `C¹`. -/
theorem loggedPreterminalTemporalDerivative_spatialC1_endpointCurlVorticity
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (j : PrimeTensor.Axis Depth.three) :
    SpatialC1
      (fun x : Point3 =>
        temporal.d
          (fun q : ℝ =>
            loggedVelocityComponent u q j x)
          s) := by
  let p :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        p
        T :=
    Classical.choose_spec hNS

  let uj : ScalarField3 :=
    loggedVelocityComponent u s j

  have huj3 : SpatialC3 uj := by
    dsimp only [uj, loggedVelocityComponent]
    exact
      hPDE.regularity.velocity_spatial_three
        s hs j

  have hLaplacian :
      SpatialC1
        (PrimeTensor.Bridge.RealFluid.laplacian
          spatial3 uj) :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.laplacian3_spatialC1
      huj3

  have hAdvection :
      SpatialC1
        (fun x : Point3 =>
          realAdvectionComponent
            (logSpaceTimeVectorField u)
            s x j) :=
    hPDE.realAdvectionComponent_spatialC1
      hs j

  have hp2 :
      SpatialC2 (p s) :=
    hPDE.regularity.pressure_spatial_two
      s hs

  have hPressure :
      SpatialC1
        (spatial3.d j (p s)) :=
    PrimeTensor.Bridge.Euclidean.SpatialC2.partialDeriv_contDiff_one
      hp2 j

  have hRHS :
      SpatialC1
        (fun x : Point3 =>
          PrimeTensor.Bridge.RealFluid.laplacian
              spatial3 uj x
            -
          realAdvectionComponent
              (logSpaceTimeVectorField u)
              s x j
            -
          spatial3.d j (p s) x) :=
    (hLaplacian.sub hAdvection).sub hPressure

  have hEq :
      (fun x : Point3 =>
        temporal.d
          (fun q : ℝ =>
            loggedVelocityComponent u q j x)
          s)
        =
      (fun x : Point3 =>
        PrimeTensor.Bridge.RealFluid.laplacian
              spatial3 uj x
            -
        realAdvectionComponent
              (logSpaceTimeVectorField u)
              s x j
            -
        spatial3.d j (p s) x) := by
    funext x

    have hMomentum :=
      hPDE.temporalComponent_eq_laplacian_sub_advection_sub_pressure
        hs x j

    change
      temporal.d
          (fun q : ℝ =>
            (logSpaceTimeVectorField u q x).component j)
          s
        =
      PrimeTensor.Bridge.RealFluid.laplacian
          spatial3
          (fun y : Point3 =>
            (logSpaceTimeVectorField u s y).component j)
          x
        -
      realAdvectionComponent
          (logSpaceTimeVectorField u)
          s x j
        -
      spatial3.d j (p s) x

    exact hMomentum

  rw [hEq]
  exact hRHS

/-- One normalized endpoint temporal-coordinate pairing can be rewritten with
the genuine old absolute-time temporal derivative. -/
theorem h3PreterminalTailCanonicalWeakTemporalCoordinatePairingReal_eq_old
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (hs : s ∈ Set.Ioo (0 : ℝ) tau)
    (φ : H3WeakTestFunction)
    (i : Fin 3) :
    h3PreterminalTailCanonicalWeakTemporalCoordinatePairingReal
        hNS ht htau hEnd hE hTail hEndpoint φ i s
      =
    ∫ x : Point3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ x)
        (temporal.d
          (fun q : ℝ =>
            loggedVelocityComponent
              u q (h3AxisOfFin3 i) x)
          (t + s))
      ∂volume := by
  unfold
    h3PreterminalTailCanonicalWeakTemporalCoordinatePairingReal
  dsimp only

  apply integral_congr_ae
  filter_upwards with x

  rw [
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_component_temporal_d_eq_old
      hNS ht htau hEnd hE hTail hEndpoint
      hs i x
  ]

/-- Compact testing of one spatial derivative of an old temporal-velocity
coordinate is integrable. -/
theorem integrable_weakTest_mul_spatial_d_loggedTemporalDerivative
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (ψ : H3WeakTestFunction)
    (a j : PrimeTensor.Axis Depth.three) :
    Integrable
      (fun x : Point3 =>
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ x)
          (spatial3.d
            a
            (fun y : Point3 =>
              temporal.d
                (fun q : ℝ =>
                  loggedVelocityComponent u q j y)
                s)
            x))
      (volume : Measure Point3) := by
  have hC1 :=
    loggedPreterminalTemporalDerivative_spatialC1_endpointCurlVorticity
      hNS hs j

  have hDContinuous :
      Continuous
        (spatial3.d
          a
          (fun y : Point3 =>
            temporal.d
              (fun q : ℝ =>
                loggedVelocityComponent u q j y)
              s)) :=
    h3SpatialC1_spatial3_d_continuous_weakPressure
      hC1 a

  exact
    ψ.integrable_bilin
      (ContinuousLinearMap.lsmul ℝ ℝ)
      (hDContinuous.locallyIntegrable.locallyIntegrableOn Set.univ)

/-- Spatial integration by parts with one old temporal-velocity coordinate. -/
theorem integral_testDerivative_mul_loggedTemporalDerivative_eq_neg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (ψ : H3WeakTestFunction)
    (a j : PrimeTensor.Axis Depth.three) :
    (∫ x : Point3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        ((h3WeakTestFunctionSpatialDerivative a ψ) x)
        (temporal.d
          (fun q : ℝ =>
            loggedVelocityComponent u q j x)
          s)
      ∂volume)
      =
    -
    ∫ x : Point3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (ψ x)
        (spatial3.d
          a
          (fun y : Point3 =>
            temporal.d
              (fun q : ℝ =>
                loggedVelocityComponent u q j y)
              s)
          x)
      ∂volume := by
  have hC1 :=
    loggedPreterminalTemporalDerivative_spatialC1_endpointCurlVorticity
      hNS hs j

  have hIBP :=
    h3SpatialC1_test_pairing_spatial3_d_eq_neg_testDerivative_pairing
      hC1 a ψ

  linarith

/-- The `01` curl test temporal pairing is the compact weak pairing with the
z-vorticity temporal derivative. -/
theorem h3PreterminalTailCanonicalWeakTemporalCurl01_eq_vorticityZTemporal
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (hs : s ∈ Set.Ioo (0 : ℝ) tau)
    (ψ : H3WeakTestFunction) :
    (∑ i : Fin 3,
      h3PreterminalTailCanonicalWeakTemporalCoordinatePairingReal
        hNS ht htau hEnd hE hTail hEndpoint
        ((h3WeakTestCurl01 ψ) i) i s)
      =
    ∫ x : Point3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (ψ x)
        (h3LoggedPreterminalVorticityZTemporalDerivativeContinuousMapExtension
          hNS (t + s) x)
      ∂volume := by
  have hAbs :
      t + s ∈ Set.Ioo (0 : ℝ) T :=
    h3PreterminalElapsedTime_mem_Ioo
      ht hEnd
      ⟨s, ⟨hs.1.le, hs.2.le⟩⟩

  let qx : ScalarField3 :=
    fun x : Point3 =>
      temporal.d
        (fun q : ℝ =>
          loggedVelocityComponent u q xAxis x)
        (t + s)

  let qy : ScalarField3 :=
    fun x : Point3 =>
      temporal.d
        (fun q : ℝ =>
          loggedVelocityComponent u q yAxis x)
        (t + s)

  have h0 :=
    h3PreterminalTailCanonicalWeakTemporalCoordinatePairingReal_eq_old
      hNS ht htau hEnd hE hTail hEndpoint hs
      ((h3WeakTestCurl01 ψ) 0) (0 : Fin 3)

  have h1 :=
    h3PreterminalTailCanonicalWeakTemporalCoordinatePairingReal_eq_old
      hNS ht htau hEnd hE hTail hEndpoint hs
      ((h3WeakTestCurl01 ψ) 1) (1 : Fin 3)

  have h2 :=
    h3PreterminalTailCanonicalWeakTemporalCoordinatePairingReal_eq_old
      hNS ht htau hEnd hE hTail hEndpoint hs
      ((h3WeakTestCurl01 ψ) 2) (2 : Fin 3)

  simp only [
    h3WeakTestCurl01_apply_zero,
    h3WeakTestCurl01_apply_one,
    h3WeakTestCurl01_apply_two,
    h3AxisOfFin3_zero,
    h3AxisOfFin3_one,
    h3AxisOfFin3_two
  ] at h0 h1 h2

  have hIBPy :=
    integral_testDerivative_mul_loggedTemporalDerivative_eq_neg
      hNS hAbs ψ yAxis xAxis

  have hIBPx :=
    integral_testDerivative_mul_loggedTemporalDerivative_eq_neg
      hNS hAbs ψ xAxis yAxis

  have hDxInt :=
    integrable_weakTest_mul_spatial_d_loggedTemporalDerivative
      hNS hAbs ψ xAxis yAxis

  have hDyInt :=
    integrable_weakTest_mul_spatial_d_loggedTemporalDerivative
      hNS hAbs ψ yAxis xAxis

  have hVortPointwise
      (x : Point3) :
      h3LoggedPreterminalVorticityZTemporalDerivativeContinuousMapExtension
          hNS (t + s) x
        =
      spatial3.d xAxis qy x
        -
      spatial3.d yAxis qx x := by
    rw [
      h3LoggedPreterminalVorticityZTemporalDerivativeContinuousMapExtension_apply_of_mem
        hNS hAbs x
    ]

    let pOld :
        SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
      Classical.choose hNS

    let hPDE :
        PreterminalNavierStokes3
          (logSpaceTimeVectorField u)
          pOld
          T :=
      Classical.choose_spec hNS

    have hTemporal :=
      hPDE.temporal_realVorticityZ hAbs x

    simpa only [
      qx,
      qy,
      loggedVelocityComponent
    ] using hTemporal

  have hTarget :
      (∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ x)
          (h3LoggedPreterminalVorticityZTemporalDerivativeContinuousMapExtension
            hNS (t + s) x)
        ∂volume)
        =
      (∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ x)
          (spatial3.d xAxis qy x)
        ∂volume)
        -
      (∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ x)
          (spatial3.d yAxis qx x)
        ∂volume) := by
    rw [← integral_sub hDxInt hDyInt]
    apply integral_congr_ae
    filter_upwards with x
    rw [hVortPointwise x]
    exact
      ((ContinuousLinearMap.lsmul ℝ ℝ) (ψ x)).map_sub
        (spatial3.d xAxis qy x)
        (spatial3.d yAxis qx x)

  rw [Fin.sum_univ_three]

  simp only [
    h3WeakTestCurl01_apply_zero,
    h3WeakTestCurl01_apply_one,
    h3WeakTestCurl01_apply_two,
    h3AxisOfFin3_zero,
    h3AxisOfFin3_one,
    h3AxisOfFin3_two
  ]

  rw [h0, h1, h2]

  simp only [
    h3WeakTestFunction_neg_apply_endpointCurlVorticityTemporalPairing,
    h3WeakTestFunction_zero_apply_endpointCurlVorticityTemporalPairing,
    ContinuousLinearMap.lsmul_apply,
    smul_eq_mul,
    neg_mul,
    zero_mul,
    integral_neg,
    integral_zero,
    add_zero
  ]

  dsimp only [qx, qy] at hIBPy hIBPx hTarget

  simp only [
    ContinuousLinearMap.lsmul_apply,
    smul_eq_mul
  ] at hIBPy hIBPx hTarget

  linarith

/-- The `02` curl test temporal pairing is minus the compact weak pairing with
the y-vorticity temporal derivative. -/
theorem h3PreterminalTailCanonicalWeakTemporalCurl02_eq_neg_vorticityYTemporal
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (hs : s ∈ Set.Ioo (0 : ℝ) tau)
    (ψ : H3WeakTestFunction) :
    (∑ i : Fin 3,
      h3PreterminalTailCanonicalWeakTemporalCoordinatePairingReal
        hNS ht htau hEnd hE hTail hEndpoint
        ((h3WeakTestCurl02 ψ) i) i s)
      =
    -
    ∫ x : Point3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (ψ x)
        (h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension
          hNS (t + s) x)
      ∂volume := by
  have hAbs :
      t + s ∈ Set.Ioo (0 : ℝ) T :=
    h3PreterminalElapsedTime_mem_Ioo
      ht hEnd
      ⟨s, ⟨hs.1.le, hs.2.le⟩⟩

  let qx : ScalarField3 :=
    fun x : Point3 =>
      temporal.d
        (fun q : ℝ =>
          loggedVelocityComponent u q xAxis x)
        (t + s)

  let qz : ScalarField3 :=
    fun x : Point3 =>
      temporal.d
        (fun q : ℝ =>
          loggedVelocityComponent u q zAxis x)
        (t + s)

  have h0 :=
    h3PreterminalTailCanonicalWeakTemporalCoordinatePairingReal_eq_old
      hNS ht htau hEnd hE hTail hEndpoint hs
      ((h3WeakTestCurl02 ψ) 0) (0 : Fin 3)

  have h1 :=
    h3PreterminalTailCanonicalWeakTemporalCoordinatePairingReal_eq_old
      hNS ht htau hEnd hE hTail hEndpoint hs
      ((h3WeakTestCurl02 ψ) 1) (1 : Fin 3)

  have h2 :=
    h3PreterminalTailCanonicalWeakTemporalCoordinatePairingReal_eq_old
      hNS ht htau hEnd hE hTail hEndpoint hs
      ((h3WeakTestCurl02 ψ) 2) (2 : Fin 3)

  simp only [
    h3WeakTestCurl02_apply_zero,
    h3WeakTestCurl02_apply_one,
    h3WeakTestCurl02_apply_two,
    h3AxisOfFin3_zero,
    h3AxisOfFin3_one,
    h3AxisOfFin3_two
  ] at h0 h1 h2

  have hIBPz :=
    integral_testDerivative_mul_loggedTemporalDerivative_eq_neg
      hNS hAbs ψ zAxis xAxis

  have hIBPx :=
    integral_testDerivative_mul_loggedTemporalDerivative_eq_neg
      hNS hAbs ψ xAxis zAxis

  have hDzInt :=
    integrable_weakTest_mul_spatial_d_loggedTemporalDerivative
      hNS hAbs ψ zAxis xAxis

  have hDxInt :=
    integrable_weakTest_mul_spatial_d_loggedTemporalDerivative
      hNS hAbs ψ xAxis zAxis

  have hVortPointwise
      (x : Point3) :
      h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension
          hNS (t + s) x
        =
      spatial3.d zAxis qx x
        -
      spatial3.d xAxis qz x := by
    rw [
      h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension_apply_of_mem
        hNS hAbs x
    ]

    let pOld :
        SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
      Classical.choose hNS

    let hPDE :
        PreterminalNavierStokes3
          (logSpaceTimeVectorField u)
          pOld
          T :=
      Classical.choose_spec hNS

    have hTemporal :=
      hPDE.temporal_realVorticityY hAbs x

    simpa only [
      qx,
      qz,
      loggedVelocityComponent
    ] using hTemporal

  have hTarget :
      (∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ x)
          (h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension
            hNS (t + s) x)
        ∂volume)
        =
      (∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ x)
          (spatial3.d zAxis qx x)
        ∂volume)
        -
      (∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ x)
          (spatial3.d xAxis qz x)
        ∂volume) := by
    rw [← integral_sub hDzInt hDxInt]
    apply integral_congr_ae
    filter_upwards with x
    rw [hVortPointwise x]
    exact
      ((ContinuousLinearMap.lsmul ℝ ℝ) (ψ x)).map_sub
        (spatial3.d zAxis qx x)
        (spatial3.d xAxis qz x)

  rw [Fin.sum_univ_three]

  simp only [
    h3WeakTestCurl02_apply_zero,
    h3WeakTestCurl02_apply_one,
    h3WeakTestCurl02_apply_two,
    h3AxisOfFin3_zero,
    h3AxisOfFin3_one,
    h3AxisOfFin3_two
  ]

  rw [h0, h1, h2]

  simp only [
    h3WeakTestFunction_neg_apply_endpointCurlVorticityTemporalPairing,
    h3WeakTestFunction_zero_apply_endpointCurlVorticityTemporalPairing,
    ContinuousLinearMap.lsmul_apply,
    smul_eq_mul,
    neg_mul,
    zero_mul,
    integral_neg,
    integral_zero,
    zero_add,
    add_zero
  ]

  dsimp only [qx, qz] at hIBPz hIBPx hTarget

  simp only [
    ContinuousLinearMap.lsmul_apply,
    smul_eq_mul
  ] at hIBPz hIBPx hTarget

  linarith

/-- The `12` curl test temporal pairing is the compact weak pairing with the
x-vorticity temporal derivative. -/
theorem h3PreterminalTailCanonicalWeakTemporalCurl12_eq_vorticityXTemporal
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (hs : s ∈ Set.Ioo (0 : ℝ) tau)
    (ψ : H3WeakTestFunction) :
    (∑ i : Fin 3,
      h3PreterminalTailCanonicalWeakTemporalCoordinatePairingReal
        hNS ht htau hEnd hE hTail hEndpoint
        ((h3WeakTestCurl12 ψ) i) i s)
      =
    ∫ x : Point3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (ψ x)
        (h3LoggedPreterminalVorticityXTemporalDerivativeContinuousMapExtension
          hNS (t + s) x)
      ∂volume := by
  have hAbs :
      t + s ∈ Set.Ioo (0 : ℝ) T :=
    h3PreterminalElapsedTime_mem_Ioo
      ht hEnd
      ⟨s, ⟨hs.1.le, hs.2.le⟩⟩

  let qy : ScalarField3 :=
    fun x : Point3 =>
      temporal.d
        (fun q : ℝ =>
          loggedVelocityComponent u q yAxis x)
        (t + s)

  let qz : ScalarField3 :=
    fun x : Point3 =>
      temporal.d
        (fun q : ℝ =>
          loggedVelocityComponent u q zAxis x)
        (t + s)

  have h0 :=
    h3PreterminalTailCanonicalWeakTemporalCoordinatePairingReal_eq_old
      hNS ht htau hEnd hE hTail hEndpoint hs
      ((h3WeakTestCurl12 ψ) 0) (0 : Fin 3)

  have h1 :=
    h3PreterminalTailCanonicalWeakTemporalCoordinatePairingReal_eq_old
      hNS ht htau hEnd hE hTail hEndpoint hs
      ((h3WeakTestCurl12 ψ) 1) (1 : Fin 3)

  have h2 :=
    h3PreterminalTailCanonicalWeakTemporalCoordinatePairingReal_eq_old
      hNS ht htau hEnd hE hTail hEndpoint hs
      ((h3WeakTestCurl12 ψ) 2) (2 : Fin 3)

  simp only [
    h3WeakTestCurl12_apply_zero,
    h3WeakTestCurl12_apply_one,
    h3WeakTestCurl12_apply_two,
    h3AxisOfFin3_zero,
    h3AxisOfFin3_one,
    h3AxisOfFin3_two
  ] at h0 h1 h2

  have hIBPz :=
    integral_testDerivative_mul_loggedTemporalDerivative_eq_neg
      hNS hAbs ψ zAxis yAxis

  have hIBPy :=
    integral_testDerivative_mul_loggedTemporalDerivative_eq_neg
      hNS hAbs ψ yAxis zAxis

  have hDzInt :=
    integrable_weakTest_mul_spatial_d_loggedTemporalDerivative
      hNS hAbs ψ zAxis yAxis

  have hDyInt :=
    integrable_weakTest_mul_spatial_d_loggedTemporalDerivative
      hNS hAbs ψ yAxis zAxis

  have hVortPointwise
      (x : Point3) :
      h3LoggedPreterminalVorticityXTemporalDerivativeContinuousMapExtension
          hNS (t + s) x
        =
      spatial3.d yAxis qz x
        -
      spatial3.d zAxis qy x := by
    rw [
      h3LoggedPreterminalVorticityXTemporalDerivativeContinuousMapExtension_apply_of_mem
        hNS hAbs x
    ]

    let pOld :
        SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
      Classical.choose hNS

    let hPDE :
        PreterminalNavierStokes3
          (logSpaceTimeVectorField u)
          pOld
          T :=
      Classical.choose_spec hNS

    have hTemporal :=
      hPDE.temporal_realVorticityX hAbs x

    simpa only [
      qy,
      qz,
      loggedVelocityComponent
    ] using hTemporal

  have hTarget :
      (∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ x)
          (h3LoggedPreterminalVorticityXTemporalDerivativeContinuousMapExtension
            hNS (t + s) x)
        ∂volume)
        =
      (∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ x)
          (spatial3.d yAxis qz x)
        ∂volume)
        -
      (∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ x)
          (spatial3.d zAxis qy x)
        ∂volume) := by
    rw [← integral_sub hDyInt hDzInt]
    apply integral_congr_ae
    filter_upwards with x
    rw [hVortPointwise x]
    exact
      ((ContinuousLinearMap.lsmul ℝ ℝ) (ψ x)).map_sub
        (spatial3.d yAxis qz x)
        (spatial3.d zAxis qy x)

  rw [Fin.sum_univ_three]

  simp only [
    h3WeakTestCurl12_apply_zero,
    h3WeakTestCurl12_apply_one,
    h3WeakTestCurl12_apply_two,
    h3AxisOfFin3_zero,
    h3AxisOfFin3_one,
    h3AxisOfFin3_two
  ]

  rw [h0, h1, h2]

  simp only [
    h3WeakTestFunction_neg_apply_endpointCurlVorticityTemporalPairing,
    h3WeakTestFunction_zero_apply_endpointCurlVorticityTemporalPairing,
    ContinuousLinearMap.lsmul_apply,
    smul_eq_mul,
    neg_mul,
    zero_mul,
    integral_neg,
    integral_zero,
    zero_add,
    add_zero
  ]

  dsimp only [qy, qz] at hIBPz hIBPy hTarget

  simp only [
    ContinuousLinearMap.lsmul_apply,
    smul_eq_mul
  ] at hIBPz hIBPy hTarget

  linarith

end

end Euclidean
end Bridge
end PrimeTensor
