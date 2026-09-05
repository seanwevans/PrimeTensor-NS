import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.PhysicalTailEndpointCanonicalTemporalDivergence
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.PhysicalTailEndpointCanonicalPressureForce

/-!
# Classicalization: isolate the endpoint pressure-force defect

The endpoint canonical reconstructed path now has

* the old classical momentum equation;
* the old/canonical advection identification;
* the canonical Leray-complement pressure identity; and
* divergence-free temporal derivative.

At this point every non-pressure term needed by the quotient-safe spectral
evolution is already identified.  The only unresolved difference between the
classical PDE and the Leray-projected PDE is the mismatch between

* the old pressure force supplied existentially by
  `LoggedPreterminalNavierStokesAdmissible`, and
* the canonical pressure force reconstructed from the Leray complement of the
  nonlinear forcing.

This file names that mismatch and reduces the endpoint equation exactly to

    ∂ₛ Wᵢ + (P nonlinear)ᵢ
      = Δ Wᵢ + pressureDefectᵢ.

Thus the later weak/Leray argument has one explicit job: show that this
gradient defect disappears after divergence-free projection/testing.

No Fourier transform of the old pressure and no `L²`-valued time derivative
is asserted here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3PhysicalTailEndpointCanonicalPressureDefect
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Difference between the genuine old preterminal pressure force and the
canonical Leray-complement pressure force on one endpoint coordinate. -/
noncomputable def h3PreterminalTailCanonicalNormalizedRealPressureForceDefectOfL2Endpoint
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 ≤ tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (s : ℝ)
    (i : Fin 3)
    (x : Point3) : ℝ :=
  let pOld :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS
  PrimeTensor.Bridge.RealFluid.pressureForceComponent
      spatial3
      pOld
      (t + s)
      x
      (h3AxisOfFin3 i)
    -
  PrimeTensor.Bridge.RealFluid.pressureForceComponent
      spatial3
      (h3PreterminalTailCanonicalNormalizedRealPressureOfL2Endpoint
        hNS ht htau hEnd hE hTail hEndpoint)
      s x
      (h3AxisOfFin3 i)

/-- The pressure-force defect is exactly the residual between the endpoint
temporal derivative plus Leray forcing and the endpoint Laplacian. -/
theorem h3PreterminalTailCanonicalNormalizedRealPressureForceDefectOfL2Endpoint_eq_temporal_add_leray_sub_laplacian
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
    {s : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) tau)
    (i : Fin 3)
    (x : Point3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint
    h3PreterminalTailCanonicalNormalizedRealPressureForceDefectOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint s i x
      =
    temporal.d
        (fun r : ℝ =>
          (h3SpectralRealVelocityOfPath W r x).component
            (h3AxisOfFin3 i))
        s
      +
    (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
      (W s) (W s) i x).re
      -
    ∑ k : Fin 3,
      spatial3.d
        (h3AxisOfFin3 k)
        (spatial3.d
          (h3AxisOfFin3 k)
          (fun y : Point3 =>
            (h3SpectralRealVelocityOfPath W s y).component
              (h3AxisOfFin3 i)))
        x := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  let pOld :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  have hsClosed :
      s ∈ Set.Icc (0 : ℝ) tau :=
    ⟨hs.1.le, hs.2.le⟩

  have hMomentum :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_oldPressure_momentum_fin
      hNS ht htau hEnd hE hTail hEndpoint hs i x

  have hAdvection :
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
    simpa only [W] using
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_advection_eq_old
        hNS ht htau hEnd hE hTail hEndpoint
        s hsClosed i x

  have hPressure :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_old_advection_eq_pressureForce_add_leray
      hNS ht htau hEnd hE hTail hEndpoint
      s hsClosed i x

  change
    PrimeTensor.Bridge.RealFluid.pressureForceComponent
        spatial3
        pOld
        (t + s)
        x
        (h3AxisOfFin3 i)
      -
    PrimeTensor.Bridge.RealFluid.pressureForceComponent
        spatial3
        (h3PreterminalTailCanonicalNormalizedRealPressureOfL2Endpoint
          hNS ht htau.le hEnd hE hTail hEndpoint)
        s x
        (h3AxisOfFin3 i)
      =
    temporal.d
        (fun r : ℝ =>
          (h3SpectralRealVelocityOfPath W r x).component
            (h3AxisOfFin3 i))
        s
      +
    (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
      (W s) (W s) i x).re
      -
    ∑ k : Fin 3,
      spatial3.d
        (h3AxisOfFin3 k)
        (spatial3.d
          (h3AxisOfFin3 k)
          (fun y : Point3 =>
            (h3SpectralRealVelocityOfPath W s y).component
              (h3AxisOfFin3 i)))
        x

  dsimp only [W, pOld] at hMomentum hPressure ⊢

  have hAdvection' := hAdvection
  dsimp only [W] at hAdvection'

  linarith

/-- Momentum form with every non-pressure term already in canonical endpoint
coordinates.  The sole remainder is the named pressure-force defect. -/
theorem h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_projectedMomentum_with_pressureDefect
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
    {s : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) tau)
    (i : Fin 3)
    (x : Point3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint
    temporal.d
        (fun r : ℝ =>
          (h3SpectralRealVelocityOfPath W r x).component
            (h3AxisOfFin3 i))
        s
      +
    (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
      (W s) (W s) i x).re
      =
    ∑ k : Fin 3,
      spatial3.d
        (h3AxisOfFin3 k)
        (spatial3.d
          (h3AxisOfFin3 k)
          (fun y : Point3 =>
            (h3SpectralRealVelocityOfPath W s y).component
              (h3AxisOfFin3 i)))
        x
      +
    h3PreterminalTailCanonicalNormalizedRealPressureForceDefectOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint s i x := by
  dsimp only

  have h :=
    h3PreterminalTailCanonicalNormalizedRealPressureForceDefectOfL2Endpoint_eq_temporal_add_leray_sub_laplacian
      hNS ht htau hEnd hE hTail hEndpoint hs i x

  linarith

end

end Euclidean
end Bridge
end PrimeTensor
