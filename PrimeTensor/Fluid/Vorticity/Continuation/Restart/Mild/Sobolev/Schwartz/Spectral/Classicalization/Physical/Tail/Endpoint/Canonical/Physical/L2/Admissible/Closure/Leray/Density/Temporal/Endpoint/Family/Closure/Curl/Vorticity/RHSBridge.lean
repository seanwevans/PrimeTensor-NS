import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.Curl.Vorticity.SquareBound

/-!
# Endpoint vorticity temporal-mass reduction to the pressure-free RHS

`Integrable` defined the scalar spatial norm masses using the continuous-map
zero extensions of the three actual vorticity temporal derivatives.

For the forthcoming H³ estimate we want those masses written in terms of the
explicit pressure-free vorticity right-hand sides.  On every genuine
preterminal slice the zero extension is the actual temporal derivative, while
`Derivative` identifies that derivative pointwise with the corresponding
pressure-free RHS.

This file records that identification first pointwise and then under the
spatial norm-mass integral.  No estimate is performed here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3EndpointCurlVorticityRHSBridge
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3EndpointCurlVorticityRHSBridge :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- On a genuine preterminal slice, the zero-extended x-vorticity temporal
derivative is exactly the pressure-free x-vorticity RHS. -/
theorem h3LoggedPreterminalVorticityXTemporalDerivativeContinuousMapExtension_apply_eq_rhs_of_mem
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3) :
    h3LoggedPreterminalVorticityXTemporalDerivativeContinuousMapExtension
        hNS s x
      =
    h3LoggedPreterminalVorticityRHSX u s x := by
  rw [
    h3LoggedPreterminalVorticityXTemporalDerivativeContinuousMapExtension_apply_of_mem
      hNS hs x
  ]
  have h :=
    (h3LoggedPreterminalVorticityX_hasDerivAt
      hNS hs x).deriv
  simpa only [temporal_d] using h

/-- On a genuine preterminal slice, the zero-extended y-vorticity temporal
derivative is exactly the pressure-free y-vorticity RHS. -/
theorem h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension_apply_eq_rhs_of_mem
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3) :
    h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension
        hNS s x
      =
    h3LoggedPreterminalVorticityRHSY u s x := by
  rw [
    h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension_apply_of_mem
      hNS hs x
  ]
  have h :=
    (h3LoggedPreterminalVorticityY_hasDerivAt
      hNS hs x).deriv
  simpa only [temporal_d] using h

/-- On a genuine preterminal slice, the zero-extended z-vorticity temporal
derivative is exactly the pressure-free z-vorticity RHS. -/
theorem h3LoggedPreterminalVorticityZTemporalDerivativeContinuousMapExtension_apply_eq_rhs_of_mem
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3) :
    h3LoggedPreterminalVorticityZTemporalDerivativeContinuousMapExtension
        hNS s x
      =
    h3LoggedPreterminalVorticityRHSZ u s x := by
  rw [
    h3LoggedPreterminalVorticityZTemporalDerivativeContinuousMapExtension_apply_of_mem
      hNS hs x
  ]
  have h :=
    (h3LoggedPreterminalVorticityZ_hasDerivAt
      hNS hs x).deriv
  simpa only [temporal_d] using h

/-- On a genuine preterminal elapsed slice, the x spatial norm mass is the
compact-test norm mass of the pressure-free x-vorticity RHS. -/
theorem h3PreterminalWeakVorticityXTemporalSpatialNormMassOnElapsed_eq_rhs_of_mem
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t r : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ψ : H3WeakTestFunction)
    (hr : t + r ∈ Set.Ioo (0 : ℝ) T) :
    h3PreterminalWeakVorticityXTemporalSpatialNormMassOnElapsed
        hNS t ψ r
      =
    ∫ x : Point3,
      ‖(ContinuousLinearMap.lsmul ℝ ℝ)
        (ψ x)
        (h3LoggedPreterminalVorticityRHSX
          u (t + r) x)‖
      ∂volume := by
  unfold
    h3PreterminalWeakVorticityXTemporalSpatialNormMassOnElapsed
  apply integral_congr_ae
  exact
    Filter.Eventually.of_forall
      (fun x : Point3 => by
        change
          ‖(ContinuousLinearMap.lsmul ℝ ℝ)
              (ψ x)
              (h3LoggedPreterminalVorticityXTemporalDerivativeContinuousMapExtension
                hNS (t + r) x)‖
            =
          ‖(ContinuousLinearMap.lsmul ℝ ℝ)
              (ψ x)
              (h3LoggedPreterminalVorticityRHSX
                u (t + r) x)‖
        rw [
          h3LoggedPreterminalVorticityXTemporalDerivativeContinuousMapExtension_apply_eq_rhs_of_mem
            hNS hr x
        ])

/-- On a genuine preterminal elapsed slice, the y spatial norm mass is the
compact-test norm mass of the pressure-free y-vorticity RHS. -/
theorem h3PreterminalWeakVorticityYTemporalSpatialNormMassOnElapsed_eq_rhs_of_mem
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t r : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ψ : H3WeakTestFunction)
    (hr : t + r ∈ Set.Ioo (0 : ℝ) T) :
    h3PreterminalWeakVorticityYTemporalSpatialNormMassOnElapsed
        hNS t ψ r
      =
    ∫ x : Point3,
      ‖(ContinuousLinearMap.lsmul ℝ ℝ)
        (ψ x)
        (h3LoggedPreterminalVorticityRHSY
          u (t + r) x)‖
      ∂volume := by
  unfold
    h3PreterminalWeakVorticityYTemporalSpatialNormMassOnElapsed
  apply integral_congr_ae
  exact
    Filter.Eventually.of_forall
      (fun x : Point3 => by
        change
          ‖(ContinuousLinearMap.lsmul ℝ ℝ)
              (ψ x)
              (h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension
                hNS (t + r) x)‖
            =
          ‖(ContinuousLinearMap.lsmul ℝ ℝ)
              (ψ x)
              (h3LoggedPreterminalVorticityRHSY
                u (t + r) x)‖
        rw [
          h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension_apply_eq_rhs_of_mem
            hNS hr x
        ])

/-- On a genuine preterminal elapsed slice, the z spatial norm mass is the
compact-test norm mass of the pressure-free z-vorticity RHS. -/
theorem h3PreterminalWeakVorticityZTemporalSpatialNormMassOnElapsed_eq_rhs_of_mem
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t r : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ψ : H3WeakTestFunction)
    (hr : t + r ∈ Set.Ioo (0 : ℝ) T) :
    h3PreterminalWeakVorticityZTemporalSpatialNormMassOnElapsed
        hNS t ψ r
      =
    ∫ x : Point3,
      ‖(ContinuousLinearMap.lsmul ℝ ℝ)
        (ψ x)
        (h3LoggedPreterminalVorticityRHSZ
          u (t + r) x)‖
      ∂volume := by
  unfold
    h3PreterminalWeakVorticityZTemporalSpatialNormMassOnElapsed
  apply integral_congr_ae
  exact
    Filter.Eventually.of_forall
      (fun x : Point3 => by
        change
          ‖(ContinuousLinearMap.lsmul ℝ ℝ)
              (ψ x)
              (h3LoggedPreterminalVorticityZTemporalDerivativeContinuousMapExtension
                hNS (t + r) x)‖
            =
          ‖(ContinuousLinearMap.lsmul ℝ ℝ)
              (ψ x)
              (h3LoggedPreterminalVorticityRHSZ
                u (t + r) x)‖
        rw [
          h3LoggedPreterminalVorticityZTemporalDerivativeContinuousMapExtension_apply_eq_rhs_of_mem
            hNS hr x
        ])

end

end Euclidean
end Bridge
end PrimeTensor
