import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.Diffusion
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.RHS.Leray.Fixed

/-!
# Zeroth-order endpoint continuity: reality of the old projected RHS

`Zero.RHSBound` defines the endpoint-independent unit-viscosity projected RHS

    Δu - P div (u ⊗ u)

directly in Fourier `L²` from one old canonical weighted H³ snapshot.

The preceding snapshot checkpoints identify the diffusion term with the old
physical Laplacian and identify the unprojected nonlinear term with old
physical advection.  Before turning the old weak momentum identity into a
genuine physical `L²` evolution statement, one representation issue remains:
the Fourier RHS must reconstruct to a real physical field exactly.

This file closes that issue.

* The old physical Laplacian is real-valued, so its scalar Plancherel transform
  is Hermitian.  The snapshot diffusion identification transports that
  symmetry to `h3SpectralScalarLaplacianRawFourierL2`.
* A genuine old H³ encoder is raw-Hermitian, and the existing convolution,
  derivative, and finite Leray reality chain therefore makes the nonlinear
  forcing Hermitian.
* Hermitian symmetry is closed under subtraction.

Thus every endpoint-independent projected RHS coordinate is Hermitian.  The
existing realizability bridge then proves that inverse Fourier transform,
real-part projection, carrier transport, and forward Plancherel recover the
same Fourier `L²` state exactly.

No endpoint-continuity or time-evolution hypothesis is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  ComplexConjugate

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityZeroOldRHSReality
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3UnitViscosityZeroOldRHSReality :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Every endpoint-independent canonical old-tail spectral snapshot is
raw-Hermitian because it is a genuine encoding of a real H³ velocity slice. -/
theorem h3PreterminalTailCanonicalSpectralStateOnElapsed_rawHermitian
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau) :
    H3SpectralVelocityRawHermitian
      (h3PreterminalTailCanonicalSpectralStateOnElapsed
        hNS ht hEnd hTail q) := by
  unfold h3PreterminalTailCanonicalSpectralStateOnElapsed

  exact
    velocityH3SpectralStateAt_rawHermitian
      (h3PreterminalTailFourierCompatibleOnElapsed
        hNS ht hEnd hTail q)

/-- The snapshot spectral Laplacian is Hermitian.  This is transported from the
already-existing real physical old-solution Laplacian through scalar
Plancherel. -/
theorem h3PreterminalTailCanonicalSnapshotLaplacianFourierL2_hermitian
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3) :
    H3FourierL2Hermitian
      (h3SpectralScalarLaplacianRawFourierL2
        ((h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail q) i)) := by
  let L : H3ScalarL2 :=
    h3PreterminalTailCanonicalVelocityLaplacianPhysicalL2OnElapsed
      hNS ht hEnd hTail q i

  have hReal :
      H3FourierL2Hermitian
        (h3ScalarFourierL2 L) := by
    unfold h3ScalarFourierL2

    exact
      h3FourierL2_complexify_real_hermitian
        (h3ToFourierRealL2 L)

  have hTransform :
      h3ScalarFourierL2 L
        =
      h3PreterminalTailCanonicalVelocityLaplacianFourierL2OnElapsed
        hNS ht hEnd hTail q i := by
    dsimp only [L]

    exact
      h3ScalarFourierL2_h3PreterminalTailCanonicalVelocityLaplacianPhysicalL2OnElapsed
        hNS ht hEnd hTail q i

  rw [hTransform] at hReal

  rw [
    h3PreterminalTailCanonicalVelocityLaplacianFourierL2OnElapsed_eq_snapshotLaplacian
      hNS ht hEnd hTail q i
  ] at hReal

  exact hReal

/-- The endpoint-independent old-snapshot nonlinear Leray forcing is Hermitian. -/
theorem h3PreterminalTailCanonicalSnapshotLerayForcingFourierL2_hermitian
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3) :
    H3FourierL2Hermitian
      (h3RawFinLerayOuterProductDivergenceFourierL2
        (h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail q)
        (h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail q)
        i) := by
  let U : H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSpectralStateOnElapsed
      hNS ht hEnd hTail q

  have hU :
      H3SpectralVelocityRawHermitian U := by
    dsimp only [U]

    exact
      h3PreterminalTailCanonicalSpectralStateOnElapsed_rawHermitian
        hNS ht hEnd hTail q

  exact
    h3RawFinLerayOuterProductDivergenceFourierL2_preserves_hermitian
      hU hU i

/-- Every endpoint-independent unit-viscosity projected RHS coordinate is
Hermitian in Fourier `L²`. -/
theorem h3PreterminalTailCanonicalZeroProjectedRHSFourierL2OnElapsed_hermitian
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3) :
    H3FourierL2Hermitian
      (h3PreterminalTailCanonicalZeroProjectedRHSFourierL2OnElapsed
        hNS ht hEnd hTail q i) := by
  let U : H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSpectralStateOnElapsed
      hNS ht hEnd hTail q

  have hLap :
      H3FourierL2Hermitian
        (h3SpectralScalarLaplacianRawFourierL2 (U i)) := by
    dsimp only [U]

    exact
      h3PreterminalTailCanonicalSnapshotLaplacianFourierL2_hermitian
        hNS ht hEnd hTail q i

  have hForce :
      H3FourierL2Hermitian
        (h3RawFinLerayOuterProductDivergenceFourierL2 U U i) := by
    dsimp only [U]

    exact
      h3PreterminalTailCanonicalSnapshotLerayForcingFourierL2_hermitian
        hNS ht hEnd hTail q i

  unfold
    h3PreterminalTailCanonicalZeroProjectedRHSFourierL2OnElapsed

  dsimp only [U]

  exact hLap.sub hForce

/-- Endpoint-independent physical real `L²` reconstruction of the bounded
unit-viscosity projected RHS. -/
noncomputable def h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2OnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3) :
    H3ScalarL2 :=
  h3FromFourierRealL2
    (h3RealPartFourierL2
      ((MeasureTheory.Lp.fourierTransformₗᵢ
        H3FourierPoint3 ℂ).symm
        (h3PreterminalTailCanonicalZeroProjectedRHSFourierL2OnElapsed
          hNS ht hEnd hTail q i)))

/-- Forward scalar Plancherel of the physical real reconstruction recovers the
endpoint-independent projected Fourier RHS exactly. -/
theorem h3ScalarFourierL2_h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2OnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3) :
    h3ScalarFourierL2
        (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2OnElapsed
          hNS ht hEnd hTail q i)
      =
    h3PreterminalTailCanonicalZeroProjectedRHSFourierL2OnElapsed
      hNS ht hEnd hTail q i := by
  unfold
    h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2OnElapsed

  exact
    h3ScalarFourierL2_realPhysicalReconstruction_eq_of_hermitian
      (h3PreterminalTailCanonicalZeroProjectedRHSFourierL2OnElapsed
        hNS ht hEnd hTail q i)
      (h3PreterminalTailCanonicalZeroProjectedRHSFourierL2OnElapsed_hermitian
        hNS ht hEnd hTail q i)

end

end Euclidean
end Bridge
end PrimeTensor
