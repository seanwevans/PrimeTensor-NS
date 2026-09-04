import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.PhysicalTailEndpointCanonicalPointwiseVelocity

/-!
# Classicalization: endpoint canonical advection is the old preterminal advection

The endpoint canonical normalized real path has now been identified pointwise
with the old logged preterminal velocity on every physical slice.

Advection at a fixed time depends only on

* the three velocity coordinate values, and
* the three first spatial derivatives of the target velocity coordinate.

The pointwise path identity supplies the three value identities directly.
Because it is equality of complete spatial scalar fields, applying
`spatial3.d` to the target-coordinate identity supplies the derivative
identities exactly.

After expanding the three-axis fold, the reconstructed endpoint-path advection
is therefore literally the old preterminal advection.  Composing with the
previous raw-outer-divergence theorem identifies the inverse Fourier
reconstruction of the unprojected nonlinear term directly with the old
physical advection.

No PDE equation, pressure identity, time derivative, or mild equation is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3PhysicalTailEndpointCanonicalOldAdvection
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Stable scalar form of one `RealFluid.advection` component in dimension
three.  Keeping this projection lemma separate avoids exposing the dependent
tensor structure inside later rewrite tactics. -/
theorem realFluid_advection_component_eq_axisFold_three
    (v : SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (s : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) :
    (PrimeTensor.Bridge.RealFluid.advection
      spatial3 v s x).component j
      =
    PrimeTensor.Axis.fold
      (· + ·)
      Depth.three
      (fun a =>
        (v s x).component a *
          spatial3.d
            a
            (fun y : Point3 => (v s y).component j)
            x) := by
  rfl

/-- On every genuine physical endpoint slice, advection of the canonical
reconstructed velocity is exactly advection of the old logged preterminal
velocity at the corresponding absolute time. -/
theorem h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_advection_eq_old
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (s : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) tau)
    (i : Fin 3)
    (x : Point3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint
    (PrimeTensor.Bridge.RealFluid.advection
      spatial3
      (h3SpectralRealVelocityOfPath W)
      s x).component
        (h3AxisOfFin3 i)
      =
    (PrimeTensor.Bridge.RealFluid.advection
      spatial3
      (logSpaceTimeVectorField u)
      (t + s) x).component
        (h3AxisOfFin3 i) := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  change
    (PrimeTensor.Bridge.RealFluid.advection
      spatial3
      (h3SpectralRealVelocityOfPath W)
      s x).component
        (h3AxisOfFin3 i)
      =
    (PrimeTensor.Bridge.RealFluid.advection
      spatial3
      (logSpaceTimeVectorField u)
      (t + s) x).component
        (h3AxisOfFin3 i)

  have h0 :
      (fun y : Point3 =>
        (h3SpectralRealVelocityOfPath W s y).component xAxis)
        =
      loggedVelocityComponent u (t + s) xAxis := by
    have h :=
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_component_eq_old
        hNS ht htau hEnd hE hTail hEndpoint s hs (0 : Fin 3)
    simpa only [
      W,
      h3AxisOfFin3_zero
    ] using h

  have h1 :
      (fun y : Point3 =>
        (h3SpectralRealVelocityOfPath W s y).component yAxis)
        =
      loggedVelocityComponent u (t + s) yAxis := by
    have h :=
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_component_eq_old
        hNS ht htau hEnd hE hTail hEndpoint s hs (1 : Fin 3)
    simpa only [
      W,
      h3AxisOfFin3_one
    ] using h

  have h2 :
      (fun y : Point3 =>
        (h3SpectralRealVelocityOfPath W s y).component zAxis)
        =
      loggedVelocityComponent u (t + s) zAxis := by
    have h :=
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_component_eq_old
        hNS ht htau hEnd hE hTail hEndpoint s hs (2 : Fin 3)
    simpa only [
      W,
      h3AxisOfFin3_two
    ] using h

  have hi :
      (fun y : Point3 =>
        (h3SpectralRealVelocityOfPath W s y).component
          (h3AxisOfFin3 i))
        =
      loggedVelocityComponent
        u (t + s) (h3AxisOfFin3 i) := by
    have h :=
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_component_eq_old
        hNS ht htau hEnd hE hTail hEndpoint s hs i
    simpa only [W] using h

  have h0x := congrFun h0 x
  have h1x := congrFun h1 x
  have h2x := congrFun h2 x

  have hdx :
      spatial3.d
          xAxis
          (fun y : Point3 =>
            (h3SpectralRealVelocityOfPath W s y).component
              (h3AxisOfFin3 i))
          x
        =
      spatial3.d
          xAxis
          (loggedVelocityComponent
            u (t + s) (h3AxisOfFin3 i))
          x :=
    congrArg
      (fun f : ScalarField3 => spatial3.d xAxis f x)
      hi

  have hdy :
      spatial3.d
          yAxis
          (fun y : Point3 =>
            (h3SpectralRealVelocityOfPath W s y).component
              (h3AxisOfFin3 i))
          x
        =
      spatial3.d
          yAxis
          (loggedVelocityComponent
            u (t + s) (h3AxisOfFin3 i))
          x :=
    congrArg
      (fun f : ScalarField3 => spatial3.d yAxis f x)
      hi

  have hdz :
      spatial3.d
          zAxis
          (fun y : Point3 =>
            (h3SpectralRealVelocityOfPath W s y).component
              (h3AxisOfFin3 i))
          x
        =
      spatial3.d
          zAxis
          (loggedVelocityComponent
            u (t + s) (h3AxisOfFin3 i))
          x :=
    congrArg
      (fun f : ScalarField3 => spatial3.d zAxis f x)
      hi

  unfold loggedVelocityComponent at h0x h1x h2x hdx hdy hdz

  rw [
    realFluid_advection_component_eq_axisFold_three,
    realFluid_advection_component_eq_axisFold_three,
    PrimeTensor.Bridge.Euclidean.axis_fold_three,
    PrimeTensor.Bridge.Euclidean.axis_fold_three
  ]

  rw [
    h0x,
    h1x,
    h2x,
    hdx,
    hdy,
    hdz
  ]

/-- Consequently the inverse Fourier reconstruction of the endpoint path's
unprojected raw outer-product divergence is directly the old preterminal
advection component. -/
theorem h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_rawOuterDivergence_fourierInv_re_eq_old_advection
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (s : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) tau)
    (i : Fin 3)
    (x : Point3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint
    (FourierTransformInv.fourierInv
      (h3RawFinOuterProductDivergence
        (W s) (W s) i)
      ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re
      =
    (PrimeTensor.Bridge.RealFluid.advection
      spatial3
      (logSpaceTimeVectorField u)
      (t + s) x).component
        (h3AxisOfFin3 i) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  calc
    (FourierTransformInv.fourierInv
      (h3RawFinOuterProductDivergence
        (W s) (W s) i)
      ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re
        =
      (PrimeTensor.Bridge.RealFluid.advection
        spatial3
        (h3SpectralRealVelocityOfPath W)
        s x).component
          (h3AxisOfFin3 i) := by
      simpa only [W] using
        h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_rawOuterDivergence_fourierInv_re_eq_advection
          hNS ht htau hEnd hE hTail hEndpoint s hs i x
    _ =
      (PrimeTensor.Bridge.RealFluid.advection
        spatial3
        (logSpaceTimeVectorField u)
        (t + s) x).component
          (h3AxisOfFin3 i) := by
      simpa only [W] using
        h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_advection_eq_old
          hNS ht htau hEnd hE hTail hEndpoint s hs i x

end

end Euclidean
end Bridge
end PrimeTensor
