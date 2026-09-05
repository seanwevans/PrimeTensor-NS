import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.PhysicalTailEndpointCanonicalPhysicalL2RHS

/-!
# Classicalization: weak temporal residual against the quotient-safe L² RHS

`PhysicalTailEndpointCanonicalWeakProjectedMomentum` proves that, against every
compactly supported smooth divergence-free test vector,

    ∂ₛ W + LerayForcing - ΔW

has zero weak pairing.

`PhysicalTailEndpointCanonicalPhysicalL2RHS` then packages

    ΔW - LerayForcing

as a genuine real `L²(Point3)` class, coordinatewise, with the expected
pointwise representative almost everywhere.

This file composes those two results without strengthening the conclusion
beyond what the Leray projection justifies.

For every strict physical elapsed time and every divergence-free test vector,

    Σᵢ ∫ φᵢ (∂ₛ Wᵢ - RHSᵢ) = 0.

The entire residual remains inside each integral.  In particular, this theorem
does **not** yet assert that the pointwise temporal derivative itself belongs to
`L²`, nor does it identify the temporal derivative against arbitrary
(non-solenoidal) test vectors.  It is exactly the quotient-safe weak evolution
statement needed before the Banach-valued time/FTC step.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3PhysicalTailEndpointCanonicalWeakTemporalL2RHS
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PhysicalTailEndpointCanonicalWeakTemporalL2RHS :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Coordinatewise quotient-safe physical `L²` right-hand side, bundled as a
three-component vector at one strict physical elapsed time. -/
noncomputable def h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Vector
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
    Fin 3 → H3ScalarL2 :=
  fun i =>
    h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2
      hNS ht htau hEnd hE hTail hEndpoint s hs i

/-- The endpoint pointwise temporal derivative and the quotient-safe physical
`L²` projected RHS have the same weak residual on every divergence-free
compactly supported smooth test vector.

The residual is intentionally kept inside the integral; no standalone
integrability or `L²` membership of the pointwise temporal derivative is used.
-/
theorem h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_weakTemporalResidual_projectedRHSPhysicalL2_eq_zero
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
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint
    let hsClosed : s ∈ Set.Icc (0 : ℝ) tau :=
      ⟨hs.1.le, hs.2.le⟩
    let R : Fin 3 → H3ScalarL2 :=
      h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Vector
        hNS ht htau hEnd hE hTail hEndpoint s hsClosed
    ∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (temporal.d
              (fun r : ℝ =>
                (h3SpectralRealVelocityOfPath W r x).component
                  (h3AxisOfFin3 i))
              s
            -
           R i x)
        ∂volume
      =
    0 := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  have hsClosed :
      s ∈ Set.Icc (0 : ℝ) tau :=
    ⟨hs.1.le, hs.2.le⟩

  let R : Fin 3 → H3ScalarL2 :=
    h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Vector
      hNS ht htau hEnd hE hTail hEndpoint s hsClosed

  have hWeak :
      ∑ i : Fin 3,
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (temporal.d
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
                 x)
          ∂volume
        =
      0 := by
    simpa only [W] using
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_weakProjectedMomentum
        hNS ht htau hEnd hE hTail hEndpoint hs φ hφ

  have hRhsAE
      (i : Fin 3) :
      (R i : Point3 → ℝ)
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
    dsimp only [
      R,
      h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Vector,
      W
    ]
    exact
      h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2_ae
        hNS ht htau hEnd hE hTail hEndpoint s hsClosed i

  calc
    (∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (temporal.d
              (fun r : ℝ =>
                (h3SpectralRealVelocityOfPath W r x).component
                  (h3AxisOfFin3 i))
              s
            -
           R i x)
        ∂volume)
        =
      ∑ i : Fin 3,
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (temporal.d
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
                 x)
          ∂volume := by
      apply Finset.sum_congr rfl
      intro i hi
      apply integral_congr_ae
      filter_upwards [hRhsAE i] with x hx

      change
        (φ i x) *
            (temporal.d
                (fun r : ℝ =>
                  (h3SpectralRealVelocityOfPath W r x).component
                    (h3AxisOfFin3 i))
                s
              -
             R i x)
          =
        (φ i x) *
            (temporal.d
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
                 x)

      rw [hx]
      ring
    _ = 0 :=
      hWeak

end

end Euclidean
end Bridge
end PrimeTensor
