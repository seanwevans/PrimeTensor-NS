import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Weak.Projected.Momentum
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Raw.Fourier.L2.Forcing

/-!
# Classicalization: package the pressure-free endpoint RHS in physical L²

`PhysicalTailEndpointCanonicalWeakProjectedMomentum` proves the pressure-free
weak residual identity

    ∂ₛ W + LerayForcing - ΔW = 0

against every compactly supported smooth divergence-free test vector.

The nonlinear forcing and diffusion terms already have quotient-safe `L²`
packages, but they live in slightly different presentations:

* the endpoint Laplacian is already packaged as a real `L²(Point3)` class;
* the Leray forcing is packaged as a complex unitary inverse-Fourier `L²`
  class on the Euclidean carrier, while the classical PDE uses the real part
  of its continuous physical representative.

This file closes that representation seam.

We take the real part of the complex forcing `L²` class and transport it back
to `L²(Point3)`.  The existing `L¹ ∩ L²` reconstruction theorem shows that this
real `L²` class is almost everywhere exactly the real part of the continuous
forcing representative already used by the pointwise PDE.

Subtracting it from the existing physical `L²` Laplacian gives a genuine
quotient-safe real `L²` right-hand side whose representative is almost
everywhere

    ΔWᵢ - (LerayForcingᵢ).

No time derivative, pressure Fourier transform, or fixed-frequency evaluation
is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3PhysicalTailEndpointCanonicalPhysicalL2RHS
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PhysicalTailEndpointCanonicalPhysicalL2RHS :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Real physical `L²(Point3)` package of one coordinate of the normalized
endpoint Leray forcing.

The complex unitary inverse-Fourier reconstruction is projected to its real
part on the Euclidean carrier and then transported through the canonical
volume-preserving `WithLp` equivalence back to `Point3`. -/
noncomputable def h3PreterminalTailCanonicalNormalizedRealLerayForcingPhysicalL2
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
    (i : Fin 3) :
    H3ScalarL2 :=
  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau hEnd hE hTail hEndpoint
  h3FromFourierRealL2
    (h3RealPartFourierL2
      (h3RawFinLerayOuterProductDivergencePhysicalL2
        (W s) (W s) i))

/-- The real physical forcing `L²` package represents exactly the real part of
the continuous pointwise forcing reconstruction almost everywhere. -/
theorem h3PreterminalTailCanonicalNormalizedRealLerayForcingPhysicalL2_ae
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
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau hEnd hE hTail hEndpoint
    ((h3PreterminalTailCanonicalNormalizedRealLerayForcingPhysicalL2
        hNS ht htau hEnd hE hTail hEndpoint s i : H3ScalarL2) :
        Point3 → ℝ)
      =ᵐ[(volume : Measure Point3)]
    (fun x : Point3 =>
      (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
        (W s) (W s) i x).re) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau hEnd hE hTail hEndpoint

  let FComplex : H3FourierComplexL2 :=
    h3RawFinLerayOuterProductDivergencePhysicalL2
      (W s) (W s) i

  let FReal : H3FourierRealL2 :=
    h3RealPartFourierL2 FComplex

  have hFrom :
      ((h3FromFourierRealL2 FReal : H3ScalarL2) :
          Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        FReal
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)) := by
    unfold h3FromFourierRealL2
    exact
      MeasureTheory.Lp.coeFn_compMeasurePreserving
        FReal
        (PiLp.volume_preserving_toLp
          (PrimeTensor.Axis Depth.three))

  have hRe :
      (FReal : H3FourierPoint3 → ℝ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun xi : H3FourierPoint3 =>
        (FComplex xi).re) := by
    dsimp only [FReal, h3RealPartFourierL2]
    exact
      Complex.reCLM.coeFn_compLp FComplex

  have hReComp :
      (fun x : Point3 =>
        FReal
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x))
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        (FComplex
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re) := by
    exact
      (PiLp.volume_preserving_toLp
        (PrimeTensor.Axis Depth.three)).quasiMeasurePreserving.ae_eq_comp
          hRe

  have hC0 :
      h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
          (W s) (W s) i
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        (FComplex
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x))) := by
    dsimp only [FComplex]
    exact
      h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_ae_eq_physicalL2
        (W s) (W s) i

  change
    ((h3FromFourierRealL2 FReal : H3ScalarL2) :
        Point3 → ℝ)
      =ᵐ[(volume : Measure Point3)]
    (fun x : Point3 =>
      (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
        (W s) (W s) i x).re)

  filter_upwards [hFrom, hReComp, hC0] with x hxFrom hxRe hxC0

  calc
    (h3FromFourierRealL2 FReal : H3ScalarL2) x
        =
      FReal
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x) :=
      hxFrom
    _ =
      (FComplex
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re :=
      hxRe
    _ =
      (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
        (W s) (W s) i x).re := by
      exact congrArg Complex.re hxC0.symm

/-- Quotient-safe physical real `L²` right-hand side of the pressure-free
endpoint projected momentum equation on a genuine physical elapsed time:

    RHS = ΔW - LerayForcing.
-/
noncomputable def h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2
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
    H3ScalarL2 :=
  h3PreterminalTailCanonicalVelocityLaplacianPhysicalL2OnElapsed
      hNS ht hEnd hTail ⟨s, hs⟩ i
    -
  h3PreterminalTailCanonicalNormalizedRealLerayForcingPhysicalL2
      hNS ht htau.le hEnd hE hTail hEndpoint s i

/-- The physical `L²` RHS has exactly the pointwise non-pressure endpoint PDE
right-hand side as an almost-everywhere representative. -/
theorem h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2_ae
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
    ((h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2
        hNS ht htau hEnd hE hTail hEndpoint s hs i : H3ScalarL2) :
        Point3 → ℝ)
      =ᵐ[(volume : Measure Point3)]
    (fun x : Point3 =>
      (∑ k : Fin 3,
        spatial3.d
          (h3AxisOfFin3 k)
          (spatial3.d
            (h3AxisOfFin3 k)
            (fun y : Point3 =>
              (h3SpectralRealVelocityOfPath W s y).component
                (h3AxisOfFin3 i)))
          x)
        -
      (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
        (W s) (W s) i x).re) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  let L : H3ScalarL2 :=
    h3PreterminalTailCanonicalVelocityLaplacianPhysicalL2OnElapsed
      hNS ht hEnd hTail ⟨s, hs⟩ i

  let F : H3ScalarL2 :=
    h3PreterminalTailCanonicalNormalizedRealLerayForcingPhysicalL2
      hNS ht htau.le hEnd hE hTail hEndpoint s i

  have hSub :=
    MeasureTheory.Lp.coeFn_sub L F

  have hLap :
      (L : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        ∑ k : Fin 3,
          spatial3.d
            (h3AxisOfFin3 k)
            (spatial3.d
              (h3AxisOfFin3 k)
              (fun y : Point3 =>
                (h3SpectralRealVelocityOfPath W s y).component
                  (h3AxisOfFin3 i)))
            x) := by
    dsimp only [L, W]
    exact
      h3PreterminalTailCanonicalVelocityLaplacianPhysicalL2OnElapsed_ae_eq_normalizedRealPath
        hNS ht htau hEnd hE hTail hEndpoint s hs i

  have hForce :
      (F : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
          (W s) (W s) i x).re) := by
    dsimp only [F, W]
    exact
      h3PreterminalTailCanonicalNormalizedRealLerayForcingPhysicalL2_ae
        hNS ht htau.le hEnd hE hTail hEndpoint s i

  change
    ((L - F : H3ScalarL2) : Point3 → ℝ)
      =ᵐ[(volume : Measure Point3)]
    (fun x : Point3 =>
      (∑ k : Fin 3,
        spatial3.d
          (h3AxisOfFin3 k)
          (spatial3.d
            (h3AxisOfFin3 k)
            (fun y : Point3 =>
              (h3SpectralRealVelocityOfPath W s y).component
                (h3AxisOfFin3 i)))
          x)
        -
      (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
        (W s) (W s) i x).re)

  filter_upwards [hSub, hLap, hForce] with x hxSub hxLap hxForce

  rw [hxSub]
  simp only [Pi.sub_apply]
  rw [hxLap, hxForce]

end

end Euclidean
end Bridge
end PrimeTensor
