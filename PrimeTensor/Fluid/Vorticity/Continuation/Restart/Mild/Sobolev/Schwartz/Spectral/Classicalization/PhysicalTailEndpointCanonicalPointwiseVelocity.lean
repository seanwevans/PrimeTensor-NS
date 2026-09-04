import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.PhysicalTailEndpointCanonicalRawOuterDivergenceAdvection
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedInitialDecoder

/-!
# Classicalization: pointwise velocity identification for the endpoint path

Every endpoint-canonical physical slice is literally the weighted H³ encoder of
the old preterminal velocity at the corresponding physical time.

`SelectedInitialDecoder` already proves, for any genuine encoded H³ snapshot,
that the canonical real `C¹` representative agrees almost everywhere with the
original logged velocity component.  On a preterminal slice both sides are
continuous:

* the spectral representative is spatially `C¹`;
* the old logged velocity component is spatially `C³`.

Equality almost everywhere therefore upgrades to equality everywhere.  This
file packages that upgrade first for the bounded endpoint path and then for the
globally indexed normalized real extension on the genuine physical interval.

The old physical component is kept behind the existing
`loggedVelocityComponent` wrapper throughout.  This avoids unfolding the
dependent tensor-component representation in downstream rewrites.

No mild equation, selected/preterminal uniqueness, pressure reconstruction, or
time derivative is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology BigOperators

noncomputable section

noncomputable local instance axisFintypeH3PhysicalTailEndpointCanonicalPointwiseVelocity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The canonical real `C¹` representative of one bounded endpoint-path slice
is pointwise the original logged preterminal velocity component. -/
theorem h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint_component_eq_old
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3) :
    h3SpectralVelocityRealC1RepresentativeOnPoint3
        (h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
          hNS ht hEnd hE hTail hEndpoint q)
        i
      =
    loggedVelocityComponent
      u
      (t + (q : ℝ))
      (h3AxisOfFin3 i) := by
  let hs :
      t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) T :=
    h3PreterminalElapsedTime_mem_Ioo ht hEnd q

  let hIq :
      VelocityH3IntegrableAt u (t + (q : ℝ)) :=
    canonicalH3TailDataFrom_integrableOnElapsed hEnd hTail q

  let hMeas :
      VelocityH3MeasurableAt u (t + (q : ℝ)) :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hNS hs

  let hFourier :
      VelocityH3FourierCompatibleAt
        u (t + (q : ℝ)) hIq hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hNS hs hIq

  have hState :
      h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
          hNS ht hEnd hE hTail hEndpoint q
        =
      velocityH3SpectralStateAt
        u
        (t + (q : ℝ))
        hIq
        hMeas
        hFourier := by
    rw [
      h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint_apply
    ]
    unfold h3PreterminalCanonicalSpectralStateOnElapsed
    rfl

  have hAE :
      h3SpectralVelocityRealC1RepresentativeOnPoint3
          (h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
            hNS ht hEnd hE hTail hEndpoint q)
          i
        =ᵐ[(volume : Measure Point3)]
      loggedVelocityComponent
        u
        (t + (q : ℝ))
        (h3AxisOfFin3 i) := by
    rw [hState]
    exact
      h3SpectralVelocityRealC1RepresentativeOnPoint3_velocityH3SpectralStateAt_ae_eq_loggedVelocityComponent
        hFourier i

  have hLeft :
      Continuous
        (h3SpectralVelocityRealC1RepresentativeOnPoint3
          (h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
            hNS ht hEnd hE hTail hEndpoint q)
          i) := by
    change
      Continuous
        (h3SpectralScalarRealC1RepresentativeOnPoint3
          ((h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
            hNS ht hEnd hE hTail hEndpoint q) i))
    exact
      (h3SpectralScalarRealC1RepresentativeOnPoint3_contDiff_one
        ((h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
          hNS ht hEnd hE hTail hEndpoint q) i)).continuous

  let p :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        p
        T :=
    Classical.choose_spec hNS

  have hOldContinuous :
      Continuous
        (loggedVelocityComponent
          u
          (t + (q : ℝ))
          (h3AxisOfFin3 i)) := by
    unfold loggedVelocityComponent
    exact
      (hPDE.regularity.velocity_spatial_three
        (t + (q : ℝ))
        hs
        (h3AxisOfFin3 i)).continuous

  exact
    MeasureTheory.Measure.eq_of_ae_eq
      hAE
      hLeft
      hOldContinuous

/-- On the genuine physical interval, the normalized real endpoint path
reconstructs the old logged velocity pointwise in every finite coordinate. -/
theorem h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_component_eq_old
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
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint
    (fun x : Point3 =>
      (h3SpectralRealVelocityOfPath W s x).component
        (h3AxisOfFin3 i))
      =
    loggedVelocityComponent
      u
      (t + s)
      (h3AxisOfFin3 i) := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  change
    (fun x : Point3 =>
      (h3SpectralRealVelocityOfPath W s x).component
        (h3AxisOfFin3 i))
      =
    loggedVelocityComponent
      u
      (t + s)
      (h3AxisOfFin3 i)

  let P : H3SpectralPhysicalVelocityPath tau :=
    h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
      hNS ht hEnd hE hTail hEndpoint

  let q : Set.Icc (0 : ℝ) tau :=
    ⟨s, hs⟩

  have hRecover :
      W s = P q := by
    dsimp only [W]
    unfold h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
    exact
      h3PathPhysicalRealExtension_normalizedPhysical_apply
        htau P q

  have hPhysical :=
    h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint_component_eq_old
      hNS ht hEnd hE hTail hEndpoint q i

  funext x

  rw [
    h3SpectralRealVelocityOfPath_component_h3AxisOfFin3,
    hRecover
  ]

  have hx := congrFun hPhysical x

  simpa only [P, q] using hx

/-- Pointwise form of the normalized endpoint-path/old-velocity identity. -/
theorem h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_component_apply_eq_old
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
    (h3SpectralRealVelocityOfPath W s x).component
        (h3AxisOfFin3 i)
      =
    loggedVelocityComponent
      u
      (t + s)
      (h3AxisOfFin3 i)
      x := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  change
    (h3SpectralRealVelocityOfPath W s x).component
        (h3AxisOfFin3 i)
      =
    loggedVelocityComponent
      u
      (t + s)
      (h3AxisOfFin3 i) x

  have hFunctions :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_component_eq_old
      hNS ht htau hEnd hE hTail hEndpoint s hs i

  exact congrFun hFunctions x

end

end Euclidean
end Bridge
end PrimeTensor
