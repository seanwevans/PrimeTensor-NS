import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.PhysicalTailEndpointCanonicalWeakTemporalL2RHS

/-!
# Classicalization: split the weak temporal pairing from the L² RHS

The previous checkpoint kept `φᵢ (∂ₛWᵢ - Rᵢ)` inside one integral.  Now the
two pieces can be separated: `Rᵢ` is a genuine physical `L²` class, while
pointwise projected momentum identifies the remaining difference with the
spatial derivative of the `C¹` scalar pressure defect.

Compact support of the test function therefore makes both contributions
integrable.  We obtain the explicit weak derivative pairing

    Σᵢ ∫ φᵢ ∂ₛWᵢ = Σᵢ ∫ φᵢ Rᵢ

for every compactly supported smooth divergence-free test vector.

No global `L¹` or `L²` membership of the pointwise temporal derivative is
claimed.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3PhysicalTailEndpointCanonicalWeakTemporalPairing
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PhysicalTailEndpointCanonicalWeakTemporalPairing :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- After multiplication by a compactly supported smooth scalar test function,
one coordinate of the endpoint pointwise temporal derivative is integrable. -/
theorem h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_test_mul_temporalDerivative_integrable
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
    (φ : H3WeakTestFunction) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint
    Integrable
      (fun x : Point3 =>
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ x)
          (temporal.d
            (fun r : ℝ =>
              (h3SpectralRealVelocityOfPath W r x).component
                (h3AxisOfFin3 i))
            s))
      (volume : Measure Point3) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  have hsClosed :
      s ∈ Set.Icc (0 : ℝ) tau :=
    ⟨hs.1.le, hs.2.le⟩

  let R : H3ScalarL2 :=
    h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2
      hNS ht htau hEnd hE hTail hEndpoint s hsClosed i

  let q : ScalarField3 :=
    h3PreterminalTailCanonicalNormalizedRealPressureScalarDefectOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint s

  have hqC1 :
      SpatialC1 q := by
    simpa only [q] using
      h3PreterminalTailCanonicalNormalizedRealPressureScalarDefectOfL2Endpoint_spatialC1
        hNS ht htau hEnd hE hTail hEndpoint hs

  have hRLocal :
      LocallyIntegrable
        (R : Point3 → ℝ)
        (volume : Measure Point3) := by
    exact
      (MeasureTheory.Lp.memLp R).locallyIntegrable
        (by norm_num)

  have hRInt :
      Integrable
        (fun x : Point3 =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ x)
            (R x))
        (volume : Measure Point3) := by
    exact
      φ.integrable_bilin
        (ContinuousLinearMap.lsmul ℝ ℝ)
        (hRLocal.locallyIntegrableOn Set.univ)

  have hdqContinuous :
      Continuous
        (spatial3.d
          (h3AxisOfFin3 i)
          q) :=
    h3SpatialC1_spatial3_d_continuous_weakPressure
      hqC1
      (h3AxisOfFin3 i)

  have hdqInt :
      Integrable
        (fun x : Point3 =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ x)
            (spatial3.d
              (h3AxisOfFin3 i)
              q
              x))
        (volume : Measure Point3) := by
    exact
      φ.integrable_bilin
        (ContinuousLinearMap.lsmul ℝ ℝ)
        (hdqContinuous.locallyIntegrable.locallyIntegrableOn Set.univ)

  have hRhsAE :
      (R : Point3 → ℝ)
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
    dsimp only [R, W]
    exact
      h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2_ae
        hNS ht htau hEnd hE hTail hEndpoint s hsClosed i

  have hTemporalAE :
      (fun x : Point3 =>
        temporal.d
          (fun r : ℝ =>
            (h3SpectralRealVelocityOfPath W r x).component
              (h3AxisOfFin3 i))
          s)
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        R x
          -
        spatial3.d
          (h3AxisOfFin3 i)
          q
          x) := by
    filter_upwards [hRhsAE] with x hxR

    have hMomentum :
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
          q
          x := by
      simpa only [W, q] using
        h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_projectedMomentum_with_gradientDefect
          hNS ht htau hEnd hE hTail hEndpoint hs i x

    linarith

  have hTestAE :
      (fun x : Point3 =>
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ x)
          (temporal.d
            (fun r : ℝ =>
              (h3SpectralRealVelocityOfPath W r x).component
                (h3AxisOfFin3 i))
            s))
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ x)
          (R x)
          -
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ x)
          (spatial3.d
            (h3AxisOfFin3 i)
            q
            x)) := by
    filter_upwards [hTemporalAE] with x hx
    change
      (φ x) *
          temporal.d
            (fun r : ℝ =>
              (h3SpectralRealVelocityOfPath W r x).component
                (h3AxisOfFin3 i))
            s
        =
      (φ x) * (R x)
        -
      (φ x) *
        spatial3.d
          (h3AxisOfFin3 i)
          q
          x
    rw [hx]
    ring

  exact
    (hRInt.sub hdqInt).congr hTestAE.symm

/-- Explicit weak derivative pairing with the quotient-safe projected `L²`
right-hand side.  Both sides are separately legitimate Bochner integrals. -/
theorem h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_weakTemporalPairing_eq_projectedRHSPhysicalL2
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
    (∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (temporal.d
            (fun r : ℝ =>
              (h3SpectralRealVelocityOfPath W r x).component
                (h3AxisOfFin3 i))
            s)
        ∂volume)
      =
    ∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (R i x)
        ∂volume := by
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

  let q : ScalarField3 :=
    h3PreterminalTailCanonicalNormalizedRealPressureScalarDefectOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint s

  have hqC1 :
      SpatialC1 q := by
    simpa only [q] using
      h3PreterminalTailCanonicalNormalizedRealPressureScalarDefectOfL2Endpoint_spatialC1
        hNS ht htau hEnd hE hTail hEndpoint hs

  have hPressure :
      ∑ i : Fin 3,
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (spatial3.d
              (h3AxisOfFin3 i)
              q
              x)
          ∂volume
        =
      0 := by
    simpa only [q] using
      h3PreterminalTailCanonicalNormalizedRealPressureScalarDefectOfL2Endpoint_classicalGradient_pairing_eq_zero
        hNS ht htau hEnd hE hTail hEndpoint hs φ hφ

  have hEach
      (i : Fin 3) :
      (∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (temporal.d
            (fun r : ℝ =>
              (h3SpectralRealVelocityOfPath W r x).component
                (h3AxisOfFin3 i))
            s)
        ∂volume)
        =
      (∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (R i x)
        ∂volume)
        -
      (∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (spatial3.d
            (h3AxisOfFin3 i)
            q
            x)
        ∂volume) := by
    have hRLocal :
        LocallyIntegrable
          (R i : Point3 → ℝ)
          (volume : Measure Point3) := by
      exact
        (MeasureTheory.Lp.memLp (R i)).locallyIntegrable
          (by norm_num)

    have hRInt :
        Integrable
          (fun x : Point3 =>
            (ContinuousLinearMap.lsmul ℝ ℝ)
              (φ i x)
              (R i x))
          (volume : Measure Point3) := by
      exact
        (φ i).integrable_bilin
          (ContinuousLinearMap.lsmul ℝ ℝ)
          (hRLocal.locallyIntegrableOn Set.univ)

    have hdqContinuous :
        Continuous
          (spatial3.d
            (h3AxisOfFin3 i)
            q) :=
      h3SpatialC1_spatial3_d_continuous_weakPressure
        hqC1
        (h3AxisOfFin3 i)

    have hdqInt :
        Integrable
          (fun x : Point3 =>
            (ContinuousLinearMap.lsmul ℝ ℝ)
              (φ i x)
              (spatial3.d
                (h3AxisOfFin3 i)
                q
                x))
          (volume : Measure Point3) := by
      exact
        (φ i).integrable_bilin
          (ContinuousLinearMap.lsmul ℝ ℝ)
          (hdqContinuous.locallyIntegrable.locallyIntegrableOn Set.univ)

    have hRhsAE :
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

    have hTemporalAE :
        (fun x : Point3 =>
          temporal.d
            (fun r : ℝ =>
              (h3SpectralRealVelocityOfPath W r x).component
                (h3AxisOfFin3 i))
            s)
          =ᵐ[(volume : Measure Point3)]
        (fun x : Point3 =>
          R i x
            -
          spatial3.d
            (h3AxisOfFin3 i)
            q
            x) := by
      filter_upwards [hRhsAE] with x hxR

      have hMomentum :
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
            q
            x := by
        simpa only [W, q] using
          h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_projectedMomentum_with_gradientDefect
            hNS ht htau hEnd hE hTail hEndpoint hs i x

      linarith

    calc
      (∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (temporal.d
            (fun r : ℝ =>
              (h3SpectralRealVelocityOfPath W r x).component
                (h3AxisOfFin3 i))
            s)
        ∂volume)
          =
        ∫ x : Point3,
          ((ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (R i x)
            -
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (spatial3.d
              (h3AxisOfFin3 i)
              q
              x))
          ∂volume := by
        apply integral_congr_ae
        filter_upwards [hTemporalAE] with x hx
        change
          (φ i x) *
              temporal.d
                (fun r : ℝ =>
                  (h3SpectralRealVelocityOfPath W r x).component
                    (h3AxisOfFin3 i))
                s
            =
          (φ i x) * (R i x)
            -
          (φ i x) *
            spatial3.d
              (h3AxisOfFin3 i)
              q
              x
        rw [hx]
        ring
      _ =
        (∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (R i x)
          ∂volume)
          -
        (∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (spatial3.d
              (h3AxisOfFin3 i)
              q
              x)
          ∂volume) := by
        exact integral_sub hRInt hdqInt

  calc
    (∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (temporal.d
            (fun r : ℝ =>
              (h3SpectralRealVelocityOfPath W r x).component
                (h3AxisOfFin3 i))
            s)
        ∂volume)
        =
      ∑ i : Fin 3,
        ((∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (R i x)
          ∂volume)
          -
        (∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (spatial3.d
              (h3AxisOfFin3 i)
              q
              x)
          ∂volume)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hEach i
    _ =
      (∑ i : Fin 3,
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (R i x)
          ∂volume)
        -
      (∑ i : Fin 3,
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (spatial3.d
              (h3AxisOfFin3 i)
              q
              x)
          ∂volume) := by
      rw [Finset.sum_sub_distrib]
    _ =
      ∑ i : Fin 3,
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (R i x)
          ∂volume := by
      rw [hPressure]
      simp

end

end Euclidean
end Bridge
end PrimeTensor
