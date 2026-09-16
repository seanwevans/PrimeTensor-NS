import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongSelectedWeakForcingTransfer

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

attribute [local instance]
  point3MeasureSpaceH3SelectedOldWeakStrongGenericWeakForcingAdvection

noncomputable local instance axisFintypeH3SelectedOldWeakStrongSelectedWeakLocalEvolution
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

theorem h3PreterminalSelectedUnitRealVelocity_weakTemporalPairing_eq_weakDiffusion_sub_leray
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q :
      Set.Icc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (hq0 : 0 < (q : ℝ))
    (hqR :
      (q : ℝ) <
        h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (φ : H3WeakTestVector) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalSelectedRestart
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail
    (∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (temporal.d
            (fun r : ℝ =>
              h3SpectralScalarRealC1RepresentativeOnPoint3
                (W r i) x)
            (q : ℝ))
        ∂volume)
      =
    h3PreterminalSelectedUnitWeakDiffusionPairingAt
        hNS ht hE hTail (q : ℝ) φ
      -
    inner ℝ
      (h3WeakTestVectorPhysicalL2Hilbert φ)
      (h3PreterminalSelectedUnitLerayForcingPhysicalL2HilbertOnRadius
        hNS ht hE hTail q) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSelectedRestart
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail

  have hPDE :=
    h3PreterminalSelectedUnitRealVelocity_weakTemporalPairing_eq_spatialRHS
      hNS ht hE hTail q hq0 hqR φ

  have hLap :=
    h3PreterminalSelectedUnitLiteralLaplacianPairing_eq_weakDiffusionPairing
      hNS ht hE hTail q hq0 φ

  have hForce :=
    inner_h3WeakTestVectorPhysicalL2Hilbert_selectedUnitLerayForcing_eq_literalC0
      hNS ht hE hTail q φ

  have hSpatialSplit :
      (∑ i : Fin 3,
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            ((∑ j : Fin 3,
              spatial3.d
                (h3AxisOfFin3 j)
                (spatial3.d
                  (h3AxisOfFin3 j)
                  (h3SpectralScalarRealC1RepresentativeOnPoint3
                    (W (q : ℝ) i)))
                x)
              -
            (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              (W (q : ℝ))
              (W (q : ℝ))
              i x).re)
          ∂volume)
        =
      (∑ i : Fin 3,
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (∑ j : Fin 3,
              spatial3.d
                (h3AxisOfFin3 j)
                (spatial3.d
                  (h3AxisOfFin3 j)
                  (h3SpectralScalarRealC1RepresentativeOnPoint3
                    (W (q : ℝ) i)))
                x)
          ∂volume)
        -
      (∑ i : Fin 3,
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            ((h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              (W (q : ℝ))
              (W (q : ℝ))
              i x).re)
          ∂volume) := by
    rw [← Finset.sum_sub_distrib]

    apply Finset.sum_congr rfl
    intro i hi

    let f : ScalarField3 :=
      h3SpectralScalarRealC1RepresentativeOnPoint3
        (W (q : ℝ) i)

    have hC3 : SpatialC3 f := by
      unfold SpatialC3
      dsimp only [f, W]
      unfold h3PreterminalTailCanonicalSelectedRestart

      exact
        h3SpectralFinHeatLerayMildSolutionAtRestartRadius_velocityRealC1RepresentativeOnPoint3_contDiff_three
          (one_pos : (0 : ℝ) < 1)
          (h3PreterminalTailCanonicalAnchorSpectralState
            hNS ht hTail)
          (lt_of_lt_of_le zero_lt_one hE)
          (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
            hNS ht hE hTail)
          hq0
          q.property.2
          i

    have hC2 : SpatialC2 f :=
      hC3.toSpatialC2

    have hLapEach
        (j : Fin 3) :
        Integrable
          (fun x : Point3 =>
            (ContinuousLinearMap.lsmul ℝ ℝ)
              (φ i x)
              (spatial3.d
                (h3AxisOfFin3 j)
                (spatial3.d
                  (h3AxisOfFin3 j)
                  f)
                x))
          (volume : Measure Point3) :=
      h3SpatialC2_test_mul_secondSpatialDerivative_integrable
        hC2
        (h3AxisOfFin3 j)
        (φ i)

    have hLapSum :
        Integrable
          (fun x : Point3 =>
            ∑ j : Fin 3,
              (ContinuousLinearMap.lsmul ℝ ℝ)
                (φ i x)
                (spatial3.d
                  (h3AxisOfFin3 j)
                  (spatial3.d
                    (h3AxisOfFin3 j)
                    f)
                  x))
          (volume : Measure Point3) := by
      exact
        integrable_finsetSum
          (Finset.univ : Finset (Fin 3))
          (fun j _ => hLapEach j)

    have hLapInt :
        Integrable
          (fun x : Point3 =>
            (ContinuousLinearMap.lsmul ℝ ℝ)
              (φ i x)
              (∑ j : Fin 3,
                spatial3.d
                  (h3AxisOfFin3 j)
                  (spatial3.d
                    (h3AxisOfFin3 j)
                    f)
                  x))
          (volume : Measure Point3) := by
      refine hLapSum.congr ?_
      filter_upwards with x
      rw [map_sum]

    let U : H3SpectralFinVectorState :=
      W (q : ℝ)

    have hForceInt :
        Integrable
          (fun x : Point3 =>
            (ContinuousLinearMap.lsmul ℝ ℝ)
              (φ i x)
              ((h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
                U U i x).re))
          (volume : Measure Point3) := by
      exact
        h3RawFinLerayOuterProductDivergenceWeakPairing_integrable
          (φ i) i U

    simpa only [f, U, map_sub] using
      (MeasureTheory.integral_sub hLapInt hForceInt)

  have hFinal := hPDE.trans hSpatialSplit
  rw [hLap, ← hForce] at hFinal
  simpa only [W] using hFinal

end

end Euclidean
end Bridge
end PrimeTensor
