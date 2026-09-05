import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Old.Advection
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Pressure.Force

/-!
# Classicalization: canonical pressure force of the physical endpoint path

The old endpoint path now has an exact nonlinear reconstruction:

    Re 𝓕⁻ Fᵢ = (u_old · ∇) u_old,ᵢ.

It is tempting to Fourier-transform the old preterminal pressure directly.
That would require spatial integrability hypotheses which are not supplied by
the preterminal `C²` pressure regularity alone.

The existing spectral pressure construction avoids that issue entirely.  For
any spectral velocity path it reconstructs pressure from the Leray complement
of the nonlinear forcing and proves

    -∂ᵢ p_spec = Re 𝓕⁻ Fᵢ - Re 𝓕⁻ (P F)ᵢ.

Specializing that identity to the endpoint canonical path, and using the
already-proved raw-forcing/advection bridge, gives

    -∂ᵢ p_spec
      = (u_old · ∇) u_old,ᵢ - Re 𝓕⁻ (P F)ᵢ.

This packages the pressure/Leray seam without asserting any Fourier
integrability of the old physical pressure and without using a time derivative
or the mild equation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3PhysicalTailEndpointCanonicalPressureForce
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Canonical spectral pressure associated pointwise in time to the normalized
real endpoint path.  This is reconstructed from the Leray complement of the
nonlinear forcing; it is not defined by Fourier-transforming the old pressure.
-/
noncomputable def h3PreterminalTailCanonicalNormalizedRealPressureOfL2Endpoint
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
        hNS ht hEnd hTail) :
    SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
  h3RawFinPressureRealC1OfPath
    (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau hEnd hE hTail hEndpoint)

/-- On the genuine physical interval, the canonical endpoint pressure force is
exactly old physical advection minus the Leray-projected nonlinear forcing. -/
theorem h3PreterminalTailCanonicalNormalizedRealPressureOfL2Endpoint_pressureForce_eq_old_advection_sub_leray
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
    PrimeTensor.Bridge.RealFluid.pressureForceComponent
        spatial3
        (h3PreterminalTailCanonicalNormalizedRealPressureOfL2Endpoint
          hNS ht htau.le hEnd hE hTail hEndpoint)
        s x
        (h3AxisOfFin3 i)
      =
    (PrimeTensor.Bridge.RealFluid.advection
      spatial3
      (logSpaceTimeVectorField u)
      (t + s) x).component
        (h3AxisOfFin3 i)
      -
    (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
      (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint s)
      (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint s)
      i x).re := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  have hPressure :
      PrimeTensor.Bridge.RealFluid.pressureForceComponent
          spatial3
          (h3RawFinPressureRealC1OfPath W)
          s x
          (h3AxisOfFin3 i)
        =
      (FourierTransformInv.fourierInv
        (h3RawFinOuterProductDivergence
          (W s) (W s) i)
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re
        -
      (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
        (W s) (W s) i x).re :=
    h3RawFinPressureRealC1OfPath_pressureForceComponent_eq_raw_sub_leray
      W s i x

  have hAdv :
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
    simpa only [W] using
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_rawOuterDivergence_fourierInv_re_eq_old_advection
        hNS ht htau hEnd hE hTail hEndpoint s hs i x

  calc
    PrimeTensor.Bridge.RealFluid.pressureForceComponent
        spatial3
        (h3PreterminalTailCanonicalNormalizedRealPressureOfL2Endpoint
          hNS ht htau.le hEnd hE hTail hEndpoint)
        s x
        (h3AxisOfFin3 i)
        =
      (FourierTransformInv.fourierInv
        (h3RawFinOuterProductDivergence
          (W s) (W s) i)
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re
        -
      (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
        (W s) (W s) i x).re := by
      simpa only [
        h3PreterminalTailCanonicalNormalizedRealPressureOfL2Endpoint,
        W
      ] using hPressure
    _ =
      (PrimeTensor.Bridge.RealFluid.advection
        spatial3
        (logSpaceTimeVectorField u)
        (t + s) x).component
          (h3AxisOfFin3 i)
        -
      (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
        (W s) (W s) i x).re := by
      rw [hAdv]
    _ =
      (PrimeTensor.Bridge.RealFluid.advection
        spatial3
        (logSpaceTimeVectorField u)
        (t + s) x).component
          (h3AxisOfFin3 i)
        -
      (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
        (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
          hNS ht htau.le hEnd hE hTail hEndpoint s)
        (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
          hNS ht htau.le hEnd hE hTail hEndpoint s)
        i x).re := by
      rfl

/-- Rearranged pressure/Leray identity in the form used by the physical
momentum balance: old advection is pressure force plus projected forcing. -/
theorem h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_old_advection_eq_pressureForce_add_leray
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
    (PrimeTensor.Bridge.RealFluid.advection
      spatial3
      (logSpaceTimeVectorField u)
      (t + s) x).component
        (h3AxisOfFin3 i)
      =
    PrimeTensor.Bridge.RealFluid.pressureForceComponent
        spatial3
        (h3PreterminalTailCanonicalNormalizedRealPressureOfL2Endpoint
          hNS ht htau.le hEnd hE hTail hEndpoint)
        s x
        (h3AxisOfFin3 i)
      +
    (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
      (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint s)
      (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint s)
      i x).re := by
  have h :=
    h3PreterminalTailCanonicalNormalizedRealPressureOfL2Endpoint_pressureForce_eq_old_advection_sub_leray
      hNS ht htau hEnd hE hTail hEndpoint s hs i x
  linarith

end

end Euclidean
end Bridge
end PrimeTensor
