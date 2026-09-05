import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Fourier.L2.RHS.Leray.Fixed
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.RHS.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Initial.Decoder
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Spectral.Realizability.Bridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Spectral.Leray.Reality

/-!
# Classicalization: the actual physical endpoint RHS is Leray-fixed

`PhysicalTailEndpointCanonicalFourierL2RHSLerayFixed` proves that the exact
quotient-safe Fourier `L²` endpoint RHS is fixed by the finite Leray projector.
The physical RHS used by the weak/Bochner branch is real-valued, however, and
its nonlinear forcing coordinate was constructed by

    raw Fourier `L²`
      -> unitary inverse Fourier transform
      -> real-part projection
      -> carrier transport back to `Point3`.

To identify these two packages exactly we must know that the raw forcing is
already the Fourier transform of a real field.  This file closes that seam.

The proof follows the existing reality infrastructure:

* a genuine encoded old H³ slice is raw-Hermitian;
* weighted product convolution preserves raw-Hermitian reality;
* the unheated raw derivative preserves ordinary Fourier Hermitian symmetry;
* finite summation and the Leray multiplier preserve Hermitian symmetry.

Thus the raw nonlinear forcing is Hermitian.  The realizability bridge then
says that its unitary inverse Fourier transform is already the complexification
of its real part.  Forward Plancherel therefore recovers the original raw
forcing exactly after the physical real projection.

Combining this with the already-existing exact Plancherel identity for the
physical Laplacian gives

    Fourier(actual physical RHS(q)) = exact Fourier RHS(q).

Hence the genuine real physical `L²` RHS is Leray-fixed at every
`q ∈ [0,τ]`.

No fixed-frequency evaluation and no new density theorem are used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace ComplexConjugate

noncomputable section

noncomputable local instance axisFintypeH3PhysicalTailEndpointCanonicalPhysicalL2RHSLerayFixed
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PhysicalTailEndpointCanonicalPhysicalL2RHSLerayFixed :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Exact carrier round trip in the reverse direction -/

/-- Transporting a real Fourier-carrier `L²` class to `Point3` and immediately
transporting it back recovers the original class exactly. -/
@[simp]
theorem h3ToFourierRealL2_h3FromFourierRealL2
    (f : H3FourierRealL2) :
    h3ToFourierRealL2 (h3FromFourierRealL2 f) = f := by
  apply MeasureTheory.Lp.ext

  have hTo :
      ((h3ToFourierRealL2
          (h3FromFourierRealL2 f) : H3FourierRealL2) :
        H3FourierPoint3 → ℝ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        (h3FromFourierRealL2 f : H3ScalarL2)
          (WithLp.ofLp ξ)) := by
    unfold h3ToFourierRealL2
    exact
      MeasureTheory.Lp.coeFn_compMeasurePreserving
        (h3FromFourierRealL2 f)
        (PiLp.volume_preserving_ofLp
          (PrimeTensor.Axis Depth.three))

  have hFrom :
      ((h3FromFourierRealL2 f : H3ScalarL2) :
        Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        f ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)) := by
    unfold h3FromFourierRealL2
    exact
      MeasureTheory.Lp.coeFn_compMeasurePreserving
        f
        (PiLp.volume_preserving_toLp
          (PrimeTensor.Axis Depth.three))

  have hFromComp :
      (fun ξ : H3FourierPoint3 =>
        (h3FromFourierRealL2 f : H3ScalarL2)
          (WithLp.ofLp ξ))
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        f
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3)
            (WithLp.ofLp ξ))) := by
    exact
      (PiLp.volume_preserving_ofLp
        (PrimeTensor.Axis Depth.three)).quasiMeasurePreserving.ae_eq_comp
          hFrom

  filter_upwards [hTo, hFromComp] with ξ hToξ hFromξ

  rw [hToξ, hFromξ]

/-! ## Hermitian physical reconstruction is an exact Fourier round trip -/

/-- If a complex Fourier `L²` state is Hermitian, then inverse Fourier,
real-part projection, physical carrier transport, and forward scalar Plancherel
recover that Fourier state exactly. -/
theorem h3ScalarFourierL2_realPhysicalReconstruction_eq_of_hermitian
    (F : H3FourierComplexL2)
    (hF : H3FourierL2Hermitian F) :
    h3ScalarFourierL2
        (h3FromFourierRealL2
          (h3RealPartFourierL2
            ((MeasureTheory.Lp.fourierTransformₗᵢ
              H3FourierPoint3 ℂ).symm F)))
      =
    F := by
  unfold h3ScalarFourierL2

  rw [h3ToFourierRealL2_h3FromFourierRealL2]

  have hReal :=
    h3FourierL2Hermitian_fourierInv_eq_complexify_real F hF

  rw [← hReal]

  exact
    (MeasureTheory.Lp.fourierTransformₗᵢ
      H3FourierPoint3 ℂ).apply_symm_apply F

/-! ## Hermitian reality of the unheated nonlinear forcing -/

/-- Spending one raw derivative on a raw-Hermitian weighted H³ scalar state
produces an ordinary Hermitian Fourier `L²` state. -/
theorem h3SpectralScalarRawDerivativeFourierL2_preserves_hermitian
    (j : Fin 3)
    {P : H3SpectralScalarState}
    (hP : H3SpectralScalarRawHermitian P) :
    H3FourierL2Hermitian
      (h3SpectralScalarRawDerivativeFourierL2 j P) := by
  unfold H3FourierL2Hermitian

  have hOut :=
    h3SpectralScalarRawDerivativeFourierL2_ae j P

  have hOutNeg :=
    h3Fourier_ae_neg hOut

  have hRaw :=
    h3SpectralScalarRawFourier_hermitian_ae hP

  filter_upwards [hOut, hOutNeg, hRaw] with
      ξ hOutξ hOutNegξ hRawξ

  rw [hOutNegξ, hOutξ, hRawξ]
  rw [h3FourierDerivativeSymbol_neg_eq_conj]
  simp only [map_mul]

/-- One pre-Leray finite divergence coordinate is Hermitian whenever both input
velocity states are raw-Hermitian. -/
theorem h3SpectralFinUnheatedDivergenceApply_preserves_hermitian
    {U V : H3SpectralFinVectorState}
    (hU : H3SpectralVelocityRawHermitian U)
    (hV : H3SpectralVelocityRawHermitian V)
    (i : Fin 3) :
    H3FourierL2Hermitian
      (h3SpectralFinUnheatedDivergenceApply U V i) := by
  have hTerm :
      ∀ j : Fin 3,
        H3FourierL2Hermitian
          (h3SpectralScalarRawDerivativeFourierL2
            j
            (h3WeightedRawProductConvolutionL2
              (U i) (V j))) := by
    intro j

    exact
      h3SpectralScalarRawDerivativeFourierL2_preserves_hermitian
        j
        (h3WeightedRawProductConvolutionL2_preserves_rawHermitian
          (hU i) (hV j))

  unfold h3SpectralFinUnheatedDivergenceApply
  simp only [Fin.sum_univ_three]

  exact
    ((hTerm 0).add (hTerm 1)).add (hTerm 2)

/-- One coordinate of the bounded unheated Leray forcing is Hermitian whenever
both input velocity states are raw-Hermitian. -/
theorem h3SpectralFinUnheatedLerayForcingApply_preserves_hermitian
    {U V : H3SpectralFinVectorState}
    (hU : H3SpectralVelocityRawHermitian U)
    (hV : H3SpectralVelocityRawHermitian V)
    (i : Fin 3) :
    H3FourierL2Hermitian
      (h3SpectralFinUnheatedLerayForcingApply U V i) := by
  have hDiv :
      ∀ j : Fin 3,
        H3FourierL2Hermitian
          (h3SpectralFinUnheatedDivergenceApply U V j) := by
    intro j
    exact
      h3SpectralFinUnheatedDivergenceApply_preserves_hermitian
        hU hV j

  have hTerm :
      ∀ j : Fin 3,
        H3FourierL2Hermitian
          (h3SpectralScalarLerayCoefficientApply
            i j
            (h3SpectralFinUnheatedDivergenceApply U V j)) := by
    intro j

    exact
      h3SpectralScalarLerayCoefficientApply_preserves_hermitian
        i j (hDiv j)

  unfold h3SpectralFinUnheatedLerayForcingApply
  unfold h3SpectralFinLerayApply
  simp only [Fin.sum_univ_three]

  exact
    ((hTerm 0).add (hTerm 1)).add (hTerm 2)

/-- The repository's canonical raw Fourier `L²` nonlinear forcing package is
Hermitian whenever both weighted H³ input velocities are raw-Hermitian. -/
theorem h3RawFinLerayOuterProductDivergenceFourierL2_preserves_hermitian
    {U V : H3SpectralFinVectorState}
    (hU : H3SpectralVelocityRawHermitian U)
    (hV : H3SpectralVelocityRawHermitian V)
    (i : Fin 3) :
    H3FourierL2Hermitian
      (h3RawFinLerayOuterProductDivergenceFourierL2 U V i) := by
  rw [
    ← h3SpectralFinUnheatedLerayForcingApply_eq_rawFourierL2
      U V i
  ]

  exact
    h3SpectralFinUnheatedLerayForcingApply_preserves_hermitian
      hU hV i

/-! ## The actual endpoint forcing is already physically real -/

/-- Every bounded endpoint-canonical spectral slice is raw-Hermitian because
it is exactly a genuine encoded old real H³ velocity snapshot. -/
theorem h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint_rawHermitian
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
    H3SpectralVelocityRawHermitian
      (h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
        hNS ht hEnd hE hTail hEndpoint q) := by
  rw [
    h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint_apply
  ]

  unfold h3PreterminalCanonicalSpectralStateOnElapsed

  exact
    velocityH3SpectralStateAt_rawHermitian
      (h3PreterminalTailFourierCompatibleOnElapsed
        hNS ht hEnd hTail q)

/-- The endpoint raw Fourier `L²` nonlinear forcing is Hermitian at every
closed elapsed time. -/
theorem h3PreterminalTailCanonicalLerayForcingFourierL2OnElapsed_hermitian
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
    H3FourierL2Hermitian
      (h3PreterminalTailCanonicalLerayForcingFourierL2OnElapsed
        hNS ht hEnd hE hTail hEndpoint q i) := by
  let U : H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
      hNS ht hEnd hE hTail hEndpoint q

  have hU :
      H3SpectralVelocityRawHermitian U := by
    dsimp only [U]
    exact
      h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint_rawHermitian
        hNS ht hEnd hE hTail hEndpoint q

  unfold h3PreterminalTailCanonicalLerayForcingFourierL2OnElapsed

  exact
    h3RawFinLerayOuterProductDivergenceFourierL2_preserves_hermitian
      hU hU i

/-- Forward scalar Plancherel of the actual real physical forcing package is
exactly the already-packaged endpoint raw Fourier `L²` forcing. -/
theorem h3ScalarFourierL2_h3PreterminalTailCanonicalNormalizedRealLerayForcingPhysicalL2
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
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3) :
    h3ScalarFourierL2
        (h3PreterminalTailCanonicalNormalizedRealLerayForcingPhysicalL2
          hNS ht htau.le hEnd hE hTail hEndpoint
          (q : ℝ) i)
      =
    h3PreterminalTailCanonicalLerayForcingFourierL2OnElapsed
      hNS ht hEnd hE hTail hEndpoint q i := by
  let F : H3FourierComplexL2 :=
    h3PreterminalTailCanonicalNormalizedRealLerayForcingFourierL2
      hNS ht htau.le hEnd hE hTail hEndpoint
      (q : ℝ) i

  have hFEq :
      F
        =
      h3PreterminalTailCanonicalLerayForcingFourierL2OnElapsed
        hNS ht hEnd hE hTail hEndpoint q i := by
    dsimp only [F]
    exact
      h3PreterminalTailCanonicalNormalizedRealLerayForcingFourierL2_eq_on_physical
        hNS ht htau hEnd hE hTail hEndpoint
        (q : ℝ) q.property i

  have hFHermitian :
      H3FourierL2Hermitian F := by
    rw [hFEq]
    exact
      h3PreterminalTailCanonicalLerayForcingFourierL2OnElapsed_hermitian
        hNS ht hEnd hE hTail hEndpoint q i

  have hRoundTrip :
      h3ScalarFourierL2
          (h3FromFourierRealL2
            (h3RealPartFourierL2
              ((MeasureTheory.Lp.fourierTransformₗᵢ
                H3FourierPoint3 ℂ).symm F)))
        =
      F :=
    h3ScalarFourierL2_realPhysicalReconstruction_eq_of_hermitian
      F hFHermitian

  unfold
    h3PreterminalTailCanonicalNormalizedRealLerayForcingPhysicalL2

  change
    h3ScalarFourierL2
        (h3FromFourierRealL2
          (h3RealPartFourierL2
            ((MeasureTheory.Lp.fourierTransformₗᵢ
              H3FourierPoint3 ℂ).symm F)))
      =
    h3PreterminalTailCanonicalLerayForcingFourierL2OnElapsed
      hNS ht hEnd hE hTail hEndpoint q i

  exact hRoundTrip.trans hFEq

/-! ## Exact Fourier identification of the actual physical projected RHS -/

/-- Bundle the actual physical projected RHS at one elapsed time into the
three-component physical Hilbert product. -/
noncomputable def h3PreterminalTailCanonicalProjectedRHSPhysicalL2HilbertOnElapsed
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
    (q : Set.Icc (0 : ℝ) tau) :
    H3PhysicalRealFinVectorL2Hilbert :=
  WithLp.toLp 2
    (fun i : Fin 3 =>
      h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2OnElapsed
        hNS ht htau hEnd hE hTail hEndpoint i q)

/-- The canonical raw Fourier vector of the actual real physical RHS is
exactly the quotient-safe Fourier RHS already proved Leray-fixed. -/
theorem h3PhysicalRealFinVectorL2HilbertRawFourier_projectedRHSPhysicalL2OnElapsed_eq
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
    (q : Set.Icc (0 : ℝ) tau) :
    h3PhysicalRealFinVectorL2HilbertRawFourier
        (h3PreterminalTailCanonicalProjectedRHSPhysicalL2HilbertOnElapsed
          hNS ht htau hEnd hE hTail hEndpoint q)
      =
    h3PreterminalTailCanonicalProjectedRHSFourierL2OnElapsed
      hNS ht htau hEnd hE hTail hEndpoint q := by
  funext i

  unfold
    h3PhysicalRealFinVectorL2HilbertRawFourier
    h3PreterminalTailCanonicalProjectedRHSPhysicalL2HilbertOnElapsed

  simp only [PiLp.toLp_apply]

  rw [
    h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2OnElapsed_apply,
    h3ScalarFourierL2_sub,
    h3ScalarFourierL2_h3PreterminalTailCanonicalVelocityLaplacianPhysicalL2OnElapsed,
    h3ScalarFourierL2_h3PreterminalTailCanonicalNormalizedRealLerayForcingPhysicalL2
      hNS ht htau hEnd hE hTail hEndpoint q i
  ]

  rfl

/-- The genuine real physical `L²` projected RHS is Leray-fixed at every point
of the complete closed elapsed interval. -/
theorem h3PreterminalTailCanonicalProjectedRHSPhysicalL2HilbertOnElapsed_lerayFixed
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
    (q : Set.Icc (0 : ℝ) tau) :
    H3PhysicalRealFinVectorL2HilbertLerayFixed
      (h3PreterminalTailCanonicalProjectedRHSPhysicalL2HilbertOnElapsed
        hNS ht htau hEnd hE hTail hEndpoint q) := by
  unfold H3PhysicalRealFinVectorL2HilbertLerayFixed

  rw [
    h3PhysicalRealFinVectorL2HilbertRawFourier_projectedRHSPhysicalL2OnElapsed_eq
      hNS ht htau hEnd hE hTail hEndpoint q
  ]

  exact
    h3PreterminalTailCanonicalProjectedRHSFourierL2OnElapsed_lerayFixed
      hNS ht htau hEnd hE hTail hEndpoint q

end

end Euclidean
end Bridge
end PrimeTensor
