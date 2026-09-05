import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Fourier.L2.Forcing.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Spectral.Realizability.Closure

/-!
# Classicalization: strong physical `L²` continuity of the endpoint RHS

The preceding two continuity checkpoints prove, on the complete closed elapsed
interval:

* strong Fourier `L²` continuity of the endpoint Laplacian;
* strong Fourier `L²` continuity of the endpoint Leray forcing.

This file transports those statements to the exact physical real `L²` packages
already used by `PhysicalTailEndpointCanonicalPhysicalL2RHS`.

For diffusion we do not reconstruct a new physical object.  Instead we use the
exact scalar Plancherel isometry: the Fourier transform of the existing
physical Laplacian is the already-continuous Fourier Laplacian.  Equality of
`L²` distances under Plancherel then gives strong continuity of the original
physical Laplacian path.

For forcing we follow the package definition literally:

    raw Fourier `L²`
      -> unitary inverse Fourier transform
      -> real-part projection
      -> volume-preserving transport back to `Point3`.

Every arrow is continuous, so the existing physical forcing package is strongly
continuous.

Subtracting the two paths gives strong continuity of the actual quotient-safe
physical projected RHS on `[0,τ]`.

No pointwise temporal derivative, pressure transform, fixed-frequency
evaluation, or second-jet time-continuity hypothesis is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PhysicalTailEndpointCanonicalPhysicalL2RHSContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PhysicalTailEndpointCanonicalPhysicalL2RHSContinuity :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Plancherel preserves differences exactly -/

/-- Carrier transport from `Point3` to the Fourier Euclidean carrier respects
subtraction. -/
theorem h3ToFourierRealL2_sub
    (f g : H3ScalarL2) :
    h3ToFourierRealL2 (f - g)
      =
    h3ToFourierRealL2 f - h3ToFourierRealL2 g := by
  unfold h3ToFourierRealL2
  exact
    (MeasureTheory.Lp.compMeasurePreserving
      (WithLp.ofLp : H3FourierPoint3 → Point3)
      (PiLp.volume_preserving_ofLp
        (PrimeTensor.Axis Depth.three))).map_sub f g

/-- The canonical scalar Plancherel bridge respects subtraction. -/
theorem h3ScalarFourierL2_sub
    (f g : H3ScalarL2) :
    h3ScalarFourierL2 (f - g)
      =
    h3ScalarFourierL2 f - h3ScalarFourierL2 g := by
  unfold h3ScalarFourierL2
  rw [
    h3ToFourierRealL2_sub,
    h3ComplexifyFourierL2_sub
  ]
  exact
    (MeasureTheory.Lp.fourierTransformₗᵢ
      H3FourierPoint3 ℂ).map_sub _ _

/-- Scalar Plancherel preserves `L²` distances exactly. -/
theorem dist_h3ScalarFourierL2
    (f g : H3ScalarL2) :
    dist (h3ScalarFourierL2 f) (h3ScalarFourierL2 g)
      =
    dist f g := by
  rw [dist_eq_norm, dist_eq_norm]
  rw [← h3ScalarFourierL2_sub]
  exact norm_h3ScalarFourierL2 (f - g)

/-! ## Physical diffusion continuity -/

/-- Strong continuity of the existing physical `L²` endpoint Laplacian.

The proof pulls continuity back through the exact scalar Plancherel isometry,
so it requires no time continuity of the concrete second-order H³ jet slots.
-/
theorem continuous_h3PreterminalTailCanonicalVelocityLaplacianPhysicalL2OnElapsed
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
    (i : Fin 3) :
    Continuous
      (fun q : Set.Icc (0 : ℝ) tau =>
        h3PreterminalTailCanonicalVelocityLaplacianPhysicalL2OnElapsed
          hNS ht hEnd hTail q i) := by
  let L :
      Set.Icc (0 : ℝ) tau → H3ScalarL2 :=
    fun q =>
      h3PreterminalTailCanonicalVelocityLaplacianPhysicalL2OnElapsed
        hNS ht hEnd hTail q i

  let LF :
      Set.Icc (0 : ℝ) tau → H3FourierComplexL2 :=
    fun q =>
      h3PreterminalTailCanonicalVelocityLaplacianFourierL2OnElapsed
        hNS ht hEnd hTail q i

  have hFourier :
      Continuous LF := by
    dsimp only [LF]
    exact
      continuous_h3PreterminalTailCanonicalVelocityLaplacianFourierL2OnElapsed
        hNS ht htau hEnd hE hTail hEndpoint i

  have hTransform :
      (fun q : Set.Icc (0 : ℝ) tau =>
        h3ScalarFourierL2 (L q))
        =
      LF := by
    funext q
    dsimp only [L, LF]
    exact
      h3ScalarFourierL2_h3PreterminalTailCanonicalVelocityLaplacianPhysicalL2OnElapsed
        hNS ht hEnd hTail q i

  rw [continuous_iff_continuousAt]
  intro q₀

  apply tendsto_iff_norm_sub_tendsto_zero.2

  have hFourierAt :
      Tendsto
        (fun q : Set.Icc (0 : ℝ) tau =>
          ‖LF q - LF q₀‖)
        (𝓝 q₀)
        (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1
      hFourier.continuousAt

  have hNormEq :
      (fun q : Set.Icc (0 : ℝ) tau =>
        ‖L q - L q₀‖)
        =
      (fun q : Set.Icc (0 : ℝ) tau =>
        ‖LF q - LF q₀‖) := by
    funext q

    have hq :
        h3ScalarFourierL2 (L q) = LF q :=
      congrFun hTransform q

    have hq₀ :
        h3ScalarFourierL2 (L q₀) = LF q₀ :=
      congrFun hTransform q₀

    calc
      ‖L q - L q₀‖
          =
        ‖h3ScalarFourierL2 (L q - L q₀)‖ := by
          symm
          exact norm_h3ScalarFourierL2 (L q - L q₀)
      _ =
        ‖h3ScalarFourierL2 (L q) -
            h3ScalarFourierL2 (L q₀)‖ := by
          rw [h3ScalarFourierL2_sub]
      _ =
        ‖LF q - LF q₀‖ := by
          rw [hq, hq₀]

  rw [hNormEq]
  exact hFourierAt

/-! ## Physical forcing continuity -/

/-- The unitary inverse-Fourier reconstruction of the raw Leray forcing is
jointly strongly continuous in its two weighted H³ input states. -/
theorem continuous_h3RawFinLerayOuterProductDivergencePhysicalL2
    (i : Fin 3) :
    Continuous
      (fun p :
          H3SpectralFinVectorState × H3SpectralFinVectorState =>
        h3RawFinLerayOuterProductDivergencePhysicalL2
          p.1 p.2 i) := by
  unfold h3RawFinLerayOuterProductDivergencePhysicalL2

  exact
    (MeasureTheory.Lp.fourierTransformₗᵢ
      H3FourierPoint3 ℂ).symm.continuous.comp
      (continuous_h3RawFinLerayOuterProductDivergenceFourierL2 i)

/-- Strong continuity of the existing real physical `L²` forcing package on
the complete closed elapsed interval. -/
theorem continuous_h3PreterminalTailCanonicalNormalizedRealLerayForcingPhysicalL2OnElapsed
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
    (i : Fin 3) :
    Continuous
      (fun q : Set.Icc (0 : ℝ) tau =>
        h3PreterminalTailCanonicalNormalizedRealLerayForcingPhysicalL2
          hNS ht htau.le hEnd hE hTail hEndpoint
          (q : ℝ) i) := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  have hW :
      Continuous W :=
    continuous_h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  let D :
      Set.Icc (0 : ℝ) tau →
        H3SpectralFinVectorState × H3SpectralFinVectorState :=
    fun q => (W (q : ℝ), W (q : ℝ))

  have hD :
      Continuous D := by
    dsimp only [D]
    exact
      Continuous.prodMk
        (hW.comp continuous_subtype_val)
        (hW.comp continuous_subtype_val)

  have hPhysicalComplex :
      Continuous
        (fun q : Set.Icc (0 : ℝ) tau =>
          h3RawFinLerayOuterProductDivergencePhysicalL2
            (W (q : ℝ)) (W (q : ℝ)) i) := by
    change
      Continuous
        ((fun p :
            H3SpectralFinVectorState × H3SpectralFinVectorState =>
          h3RawFinLerayOuterProductDivergencePhysicalL2
            p.1 p.2 i) ∘ D)

    exact
      (continuous_h3RawFinLerayOuterProductDivergencePhysicalL2 i).comp hD

  unfold
    h3PreterminalTailCanonicalNormalizedRealLerayForcingPhysicalL2

  dsimp only [W]

  exact
    continuous_h3FromFourierRealL2.comp
      (continuous_h3RealPartFourierL2.comp
        hPhysicalComplex)

/-! ## Strong continuity of the actual physical RHS -/

/-- Closed-interval wrapper for the already-defined quotient-safe physical
projected RHS. -/
noncomputable def h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2OnElapsed
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
    (i : Fin 3)
    (q : Set.Icc (0 : ℝ) tau) :
    H3ScalarL2 :=
  h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2
    hNS ht htau hEnd hE hTail hEndpoint
    (q : ℝ) q.property i

@[simp]
theorem h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2OnElapsed_apply
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
    (i : Fin 3)
    (q : Set.Icc (0 : ℝ) tau) :
    h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2OnElapsed
        hNS ht htau hEnd hE hTail hEndpoint i q
      =
    h3PreterminalTailCanonicalVelocityLaplacianPhysicalL2OnElapsed
        hNS ht hEnd hTail q i
      -
    h3PreterminalTailCanonicalNormalizedRealLerayForcingPhysicalL2
        hNS ht htau.le hEnd hE hTail hEndpoint
        (q : ℝ) i := by
  rfl

/-- The actual quotient-safe physical projected RHS is strongly continuous in
`L²(Point3)` on the complete closed elapsed interval. -/
theorem continuous_h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2OnElapsed
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
    (i : Fin 3) :
    Continuous
      (h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2OnElapsed
        hNS ht htau hEnd hE hTail hEndpoint i) := by
  have hLap :
      Continuous
        (fun q : Set.Icc (0 : ℝ) tau =>
          h3PreterminalTailCanonicalVelocityLaplacianPhysicalL2OnElapsed
            hNS ht hEnd hTail q i) :=
    continuous_h3PreterminalTailCanonicalVelocityLaplacianPhysicalL2OnElapsed
      hNS ht htau hEnd hE hTail hEndpoint i

  have hForce :
      Continuous
        (fun q : Set.Icc (0 : ℝ) tau =>
          h3PreterminalTailCanonicalNormalizedRealLerayForcingPhysicalL2
            hNS ht htau.le hEnd hE hTail hEndpoint
            (q : ℝ) i) :=
    continuous_h3PreterminalTailCanonicalNormalizedRealLerayForcingPhysicalL2OnElapsed
      hNS ht htau hEnd hE hTail hEndpoint i

  unfold
    h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2OnElapsed
    h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2

  exact hLap.sub hForce

end

end Euclidean
end Bridge
end PrimeTensor
