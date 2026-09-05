import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Pressure.Defect
import PrimeTensor.Bridge.Euclidean.Advection.Product

/-!
# Classicalization: the endpoint pressure-force defect is a gradient

The previous checkpoint isolated the exact residual between the old classical
momentum equation and the canonical Leray-projected endpoint equation as a
coordinatewise pressure-force defect.

That defect is not an arbitrary remainder.  Both of its terms are negative
spatial derivatives of scalar pressures:

* the old pressure selected by `LoggedPreterminalNavierStokesAdmissible`;
* the canonical spectral pressure reconstructed from the Leray complement.

This file packages their scalar difference and proves that the force defect is
literally its negative gradient.

Thus the endpoint equation becomes

    ∂ₛ Wᵢ + (P nonlinear)ᵢ
      = ΔWᵢ - ∂ᵢ q,

where

    q = p_old(t+s) - p_canonical(s).

The remaining weak/Leray step therefore has the standard form: a gradient
field must vanish after pairing with divergence-free tests / applying the
Leray projection.

No Fourier transform of `p_old` is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3PhysicalTailEndpointCanonicalPressureGradientDefect
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Scalar pressure mismatch between the genuine old preterminal pressure and
the canonical Leray-complement pressure on the endpoint clock. -/
noncomputable def h3PreterminalTailCanonicalNormalizedRealPressureScalarDefectOfL2Endpoint
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
    (s : ℝ) :
    ScalarField3 :=
  let pOld :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS
  fun x : Point3 =>
    pOld (t + s) x
      -
    h3PreterminalTailCanonicalNormalizedRealPressureOfL2Endpoint
      hNS ht htau hEnd hE hTail hEndpoint
      s x

/-- On every strict physical elapsed slice, the scalar pressure defect is
spatially `C¹`. -/
theorem h3PreterminalTailCanonicalNormalizedRealPressureScalarDefectOfL2Endpoint_spatialC1
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
    (hs : s ∈ Set.Ioo (0 : ℝ) tau) :
    SpatialC1
      (h3PreterminalTailCanonicalNormalizedRealPressureScalarDefectOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint s) := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  let pOld :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        pOld
        T :=
    Classical.choose_spec hNS

  have hsClosed :
      s ∈ Set.Icc (0 : ℝ) tau :=
    ⟨hs.1.le, hs.2.le⟩

  have hAbs :
      t + s ∈ Set.Ioo (0 : ℝ) T :=
    h3PreterminalElapsedTime_mem_Ioo
      ht hEnd ⟨s, hsClosed⟩

  have hOldC2 :
      SpatialC2 (pOld (t + s)) :=
    hPDE.regularity.pressure_spatial_two
      (t + s) hAbs

  have hOldC1 :
      SpatialC1 (pOld (t + s)) := by
    exact hOldC2.of_le (by norm_num)

  have hCanonicalC1 :
      SpatialC1
        (h3PreterminalTailCanonicalNormalizedRealPressureOfL2Endpoint
          hNS ht htau.le hEnd hE hTail hEndpoint s) := by
    dsimp only [
      h3PreterminalTailCanonicalNormalizedRealPressureOfL2Endpoint,
      h3RawFinPressureRealC1OfPath,
      W
    ]
    exact
      h3RawFinPressureRealC1RepresentativeOnPoint3_contDiff_one
        (W s) (W s)

  change
    SpatialC1
      (fun x : Point3 =>
        pOld (t + s) x
          -
        h3PreterminalTailCanonicalNormalizedRealPressureOfL2Endpoint
          hNS ht htau.le hEnd hE hTail hEndpoint
          s x)

  exact hOldC1.sub hCanonicalC1

/-- The previously isolated pressure-force defect is exactly the negative
spatial derivative of the scalar pressure mismatch. -/
theorem h3PreterminalTailCanonicalNormalizedRealPressureForceDefectOfL2Endpoint_eq_neg_spatialDerivative_scalarDefect
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
    h3PreterminalTailCanonicalNormalizedRealPressureForceDefectOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint s i x
      =
    -
    spatial3.d
      (h3AxisOfFin3 i)
      (h3PreterminalTailCanonicalNormalizedRealPressureScalarDefectOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint s)
      x := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  let pOld :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        pOld
        T :=
    Classical.choose_spec hNS

  have hsClosed :
      s ∈ Set.Icc (0 : ℝ) tau :=
    ⟨hs.1.le, hs.2.le⟩

  have hAbs :
      t + s ∈ Set.Ioo (0 : ℝ) T :=
    h3PreterminalElapsedTime_mem_Ioo
      ht hEnd ⟨s, hsClosed⟩

  have hOldC2 :
      SpatialC2 (pOld (t + s)) :=
    hPDE.regularity.pressure_spatial_two
      (t + s) hAbs

  have hOldC1 :
      SpatialC1 (pOld (t + s)) := by
    exact hOldC2.of_le (by norm_num)

  have hCanonicalC1 :
      SpatialC1
        (h3PreterminalTailCanonicalNormalizedRealPressureOfL2Endpoint
          hNS ht htau.le hEnd hE hTail hEndpoint s) := by
    dsimp only [
      h3PreterminalTailCanonicalNormalizedRealPressureOfL2Endpoint,
      h3RawFinPressureRealC1OfPath,
      W
    ]
    exact
      h3RawFinPressureRealC1RepresentativeOnPoint3_contDiff_one
        (W s) (W s)

  have hSub :=
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_sub
      hOldC1 hCanonicalC1
      x
      (h3AxisOfFin3 i)

  unfold
    h3PreterminalTailCanonicalNormalizedRealPressureForceDefectOfL2Endpoint
    h3PreterminalTailCanonicalNormalizedRealPressureScalarDefectOfL2Endpoint
    PrimeTensor.Bridge.RealFluid.pressureForceComponent

  dsimp only [pOld]

  rw [hSub]

  ring

/-- The endpoint projected momentum equation with the sole remainder written
as an explicit scalar gradient. -/
theorem h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_projectedMomentum_with_gradientDefect
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
      -
    spatial3.d
      (h3AxisOfFin3 i)
      (h3PreterminalTailCanonicalNormalizedRealPressureScalarDefectOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint s)
      x := by
  dsimp only

  have hMomentum :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_projectedMomentum_with_pressureDefect
      hNS ht htau hEnd hE hTail hEndpoint hs i x

  have hDefect :=
    h3PreterminalTailCanonicalNormalizedRealPressureForceDefectOfL2Endpoint_eq_neg_spatialDerivative_scalarDefect
      hNS ht htau hEnd hE hTail hEndpoint hs i x

  rw [hDefect] at hMomentum

  linarith

end

end Euclidean
end Bridge
end PrimeTensor
