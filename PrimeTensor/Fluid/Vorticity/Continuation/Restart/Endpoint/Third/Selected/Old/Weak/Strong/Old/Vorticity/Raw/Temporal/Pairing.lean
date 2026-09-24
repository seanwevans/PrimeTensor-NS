import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Old.Vorticity.FTC
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Projected.RHS.Weak.Evolution.Local.Domination
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.Curl.Vorticity.TemporalPairing

/-!
# Raw old curl temporal pairings

The endpoint-era curl/vorticity temporal identities were stated using the
endpoint-normalized weak temporal pairing.  That object carries
`H3PreterminalCanonicalL2EndpointContinuousOnElapsed` in its type.

The `Third` branch already contains the actual-old pairing

    h3PreterminalLoggedVelocityWeakTemporalCoordinatePairingReal,

which is simply the compact spatial pairing against the genuine old
absolute-time temporal derivative.

This file proves the three strict-time curl identities directly for that raw
pairing:

    curl01(ψ)  ->   <ψ, ∂ₜω_z>
    curl02(ψ)  -> - <ψ, ∂ₜω_y>
    curl12(ψ)  ->   <ψ, ∂ₜω_x>.

No endpoint-continuity hypothesis occurs.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongOldVorticityRawTemporalPairing
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3SelectedOldWeakStrongOldVorticityRawTemporalPairing :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The raw old temporal-coordinate pairing is definitionally the compact
pairing against the genuine old absolute-time temporal derivative. -/
theorem h3PreterminalLoggedVelocityWeakTemporalCoordinatePairingReal_eq_old
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (φ : H3WeakTestFunction)
    (i : Fin 3) :
    h3PreterminalLoggedVelocityWeakTemporalCoordinatePairingReal
        hNS t φ i s
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
  rfl

/-- The raw-old `01` curl temporal pairing is the compact weak pairing with
the z-vorticity temporal derivative. -/
theorem h3PreterminalLoggedVelocityWeakTemporalCurl01_eq_vorticityZTemporal
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hs : s ∈ Set.Ioo (0 : ℝ) tau)
    (ψ : H3WeakTestFunction) :
    (∑ i : Fin 3,
      h3PreterminalLoggedVelocityWeakTemporalCoordinatePairingReal
        hNS t ((h3WeakTestCurl01 ψ) i) i s)
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
    h3PreterminalLoggedVelocityWeakTemporalCoordinatePairingReal_eq_old
      (t := t)
      hNS ((h3WeakTestCurl01 ψ) 0) (0 : Fin 3) (s := s)

  have h1 :=
    h3PreterminalLoggedVelocityWeakTemporalCoordinatePairingReal_eq_old
      (t := t)
      hNS ((h3WeakTestCurl01 ψ) 1) (1 : Fin 3) (s := s)

  have h2 :=
    h3PreterminalLoggedVelocityWeakTemporalCoordinatePairingReal_eq_old
      (t := t)
      hNS ((h3WeakTestCurl01 ψ) 2) (2 : Fin 3) (s := s)

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

/-- The raw-old `02` curl temporal pairing is minus the compact weak pairing
with the y-vorticity temporal derivative. -/
theorem h3PreterminalLoggedVelocityWeakTemporalCurl02_eq_neg_vorticityYTemporal
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hs : s ∈ Set.Ioo (0 : ℝ) tau)
    (ψ : H3WeakTestFunction) :
    (∑ i : Fin 3,
      h3PreterminalLoggedVelocityWeakTemporalCoordinatePairingReal
        hNS t ((h3WeakTestCurl02 ψ) i) i s)
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
    h3PreterminalLoggedVelocityWeakTemporalCoordinatePairingReal_eq_old
      (t := t)
      hNS ((h3WeakTestCurl02 ψ) 0) (0 : Fin 3) (s := s)

  have h1 :=
    h3PreterminalLoggedVelocityWeakTemporalCoordinatePairingReal_eq_old
      (t := t)
      hNS ((h3WeakTestCurl02 ψ) 1) (1 : Fin 3) (s := s)

  have h2 :=
    h3PreterminalLoggedVelocityWeakTemporalCoordinatePairingReal_eq_old
      (t := t)
      hNS ((h3WeakTestCurl02 ψ) 2) (2 : Fin 3) (s := s)

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

/-- The raw-old `12` curl temporal pairing is the compact weak pairing with
the x-vorticity temporal derivative. -/
theorem h3PreterminalLoggedVelocityWeakTemporalCurl12_eq_vorticityXTemporal
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hs : s ∈ Set.Ioo (0 : ℝ) tau)
    (ψ : H3WeakTestFunction) :
    (∑ i : Fin 3,
      h3PreterminalLoggedVelocityWeakTemporalCoordinatePairingReal
        hNS t ((h3WeakTestCurl12 ψ) i) i s)
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
    h3PreterminalLoggedVelocityWeakTemporalCoordinatePairingReal_eq_old
      (t := t)
      hNS ((h3WeakTestCurl12 ψ) 0) (0 : Fin 3) (s := s)

  have h1 :=
    h3PreterminalLoggedVelocityWeakTemporalCoordinatePairingReal_eq_old
      (t := t)
      hNS ((h3WeakTestCurl12 ψ) 1) (1 : Fin 3) (s := s)

  have h2 :=
    h3PreterminalLoggedVelocityWeakTemporalCoordinatePairingReal_eq_old
      (t := t)
      hNS ((h3WeakTestCurl12 ψ) 2) (2 : Fin 3) (s := s)

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
