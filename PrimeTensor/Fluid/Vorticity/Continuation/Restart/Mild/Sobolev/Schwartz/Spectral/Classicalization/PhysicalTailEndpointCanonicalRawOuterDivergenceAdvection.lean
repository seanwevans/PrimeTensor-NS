import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.PhysicalTailEndpointCanonicalRawFourierL2Forcing
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.RawOuterDivergenceAdvectionBridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.PreterminalIncompressibility
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedRawFourierIncompressibility
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Spectral.Realizability

/-!
# Classicalization: endpoint canonical raw outer divergence is advection

The endpoint canonical physical path is not an abstract selected solution: every
slice is literally the weighted H³ encoder of the old preterminal velocity at
the corresponding physical time.

Two existing invariants therefore apply slice-by-slice:

* every genuine encoded H³ snapshot is physically realizable;
* preterminal physical incompressibility makes the encoded spectral state
  divergence-free, hence also raw-Fourier divergence-free after exact
  deweighting.

The generic nonlinear bridge then identifies the inverse Fourier transform of
the unprojected raw outer-product divergence with ordinary physical advection
for the canonical reconstructed velocity.

This file transports those facts through both the bounded physical endpoint
path and its globally indexed normalized real extension.  No mild equation,
uniqueness theorem, pressure reconstruction, time derivative, or new estimate
is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3PhysicalTailEndpointCanonicalRawOuterDivergenceAdvection
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Every bounded endpoint-canonical physical slice is a genuine realizable
encoded H³ velocity state. -/
theorem h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint_realizable
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
    (q : Set.Icc (0 : ℝ) tau) :
    H3SpectralVelocityRealizable
      (h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
        hNS ht hEnd hE hTail hEndpoint q) := by
  rw [
    h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint_apply
  ]

  unfold h3PreterminalCanonicalSpectralStateOnElapsed

  exact
    velocityH3SpectralStateAt_realizable
      (velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
        hNS
        (h3PreterminalElapsedTime_mem_Ioo ht hEnd q)
        (canonicalH3TailDataFrom_integrableOnElapsed hEnd hTail q))

/-- Every bounded endpoint-canonical physical slice is raw-Fourier
divergence-free. -/
theorem h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint_rawDivergenceFree
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
    (q : Set.Icc (0 : ℝ) tau) :
    H3SpectralFinRawDivergenceFree
      (h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
        hNS ht hEnd hE hTail hEndpoint q) := by
  rw [
    h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint_apply
  ]

  unfold h3PreterminalCanonicalSpectralStateOnElapsed

  apply h3SpectralFinRawDivergenceFree_of_divergenceFree

  exact
    velocityH3SpectralStateAt_divergenceFree_of_loggedPreterminalNavierStokes
      hNS
      (h3PreterminalElapsedTime_mem_Ioo ht hEnd q)
      (canonicalH3TailDataFrom_integrableOnElapsed hEnd hTail q)

/-- Inside the physical interval, the normalized real endpoint path remains
realizable. -/
theorem h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_realizable
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
    (hs : s ∈ Set.Icc (0 : ℝ) tau) :
    H3SpectralVelocityRealizable
      (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint s) := by
  let P : H3SpectralPhysicalVelocityPath tau :=
    h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
      hNS ht hEnd hE hTail hEndpoint

  let q : Set.Icc (0 : ℝ) tau :=
    ⟨s, hs⟩

  have hRecover :
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
          hNS ht htau.le hEnd hE hTail hEndpoint s
        =
      P q := by
    unfold h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
    exact
      h3PathPhysicalRealExtension_normalizedPhysical_apply
        htau P q

  rw [hRecover]

  dsimp only [P, q]

  exact
    h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint_realizable
      hNS ht hEnd hE hTail hEndpoint ⟨s, hs⟩

/-- Inside the physical interval, the normalized real endpoint path remains
raw-Fourier divergence-free. -/
theorem h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_rawDivergenceFree
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
    (hs : s ∈ Set.Icc (0 : ℝ) tau) :
    H3SpectralFinRawDivergenceFree
      (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint s) := by
  let P : H3SpectralPhysicalVelocityPath tau :=
    h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
      hNS ht hEnd hE hTail hEndpoint

  let q : Set.Icc (0 : ℝ) tau :=
    ⟨s, hs⟩

  have hRecover :
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
          hNS ht htau.le hEnd hE hTail hEndpoint s
        =
      P q := by
    unfold h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
    exact
      h3PathPhysicalRealExtension_normalizedPhysical_apply
        htau P q

  rw [hRecover]

  dsimp only [P, q]

  exact
    h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint_rawDivergenceFree
      hNS ht hEnd hE hTail hEndpoint ⟨s, hs⟩

/-- On the genuine physical interval, the inverse Fourier reconstruction of
the endpoint path's unprojected raw outer-product divergence is exactly the
ordinary advection of its canonical reconstructed real velocity. -/
theorem h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_rawOuterDivergence_fourierInv_re_eq_advection
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
      (h3SpectralRealVelocityOfPath W)
      s x).component
        (h3AxisOfFin3 i) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  have hReal :
      H3SpectralVelocityRealizable (W s) := by
    dsimp only [W]
    exact
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_realizable
        hNS ht htau hEnd hE hTail hEndpoint s hs

  have hDiv :
      H3SpectralFinRawDivergenceFree (W s) := by
    dsimp only [W]
    exact
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_rawDivergenceFree
        hNS ht htau hEnd hE hTail hEndpoint s hs

  exact
    h3RawFinOuterProductDivergence_fourierInv_re_eq_advection_of_realizable_of_rawDivergenceFree
      W s hReal hDiv i x

end

end Euclidean
end Bridge
end PrimeTensor
