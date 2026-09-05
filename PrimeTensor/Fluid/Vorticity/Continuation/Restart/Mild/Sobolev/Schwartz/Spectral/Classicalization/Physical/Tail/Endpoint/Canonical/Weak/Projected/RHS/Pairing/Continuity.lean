import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Weak.Forcing.Pairing.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Weak.Temporal.Pairing

/-!
# Classicalization: continuous weak projected RHS pairing

The weak diffusion pairing is continuous after moving two spatial derivatives
onto the compact test function.  The weak nonlinear forcing pairing is
continuous by the existing spectral-state difference estimate.

Their difference is therefore a continuous scalar function of elapsed time:

    weakRHSφ = weakDiffusionφ - weakForcingφ.

At every strict interior elapsed time, the already-proved weak projected
momentum identity can now be split term-by-term because:

* the compactly tested pointwise temporal derivative is integrable;
* the compactly tested forcing representative is integrable;
* every compactly tested pure second spatial derivative is integrable.

After splitting the residual, the diffusion transfer theorem and the forcing
pairing definition identify the result with the continuous `weakRHSφ`.

Hence, for every divergence-free compact test vector,

    Σᵢ ∫ φᵢ ∂ₛWᵢ = weakRHSφ(s).

Combining this with the earlier quotient-safe physical `L²` temporal pairing
theorem gives

    weakRHSφ(s) = Σᵢ ∫ φᵢ Rᵢ(s),

where `R` is the packaged physical `L²` projected RHS.

This is the final topology checkpoint before differentiating the continuous
velocity pairing and applying scalar FTC.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3PhysicalTailEndpointCanonicalWeakProjectedRHSPairingContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PhysicalTailEndpointCanonicalWeakProjectedRHSPairingContinuity :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Continuous candidate weak projected RHS pairing:
diffusion minus nonlinear Leray forcing. -/
noncomputable def h3PreterminalTailCanonicalWeakProjectedRHSPairingOnElapsed
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
    (φ : H3WeakTestVector)
    (q : Set.Icc (0 : ℝ) tau) :
    ℝ :=
  h3PreterminalTailCanonicalWeakDiffusionPairingOnElapsed
      hNS ht hEnd hTail φ q
    -
  h3PreterminalTailCanonicalWeakForcingPairingOnElapsed
      hNS ht htau hEnd hE hTail hEndpoint φ q

/-- The complete weak projected RHS pairing is continuous on the closed elapsed
interval. -/
theorem continuous_h3PreterminalTailCanonicalWeakProjectedRHSPairingOnElapsed
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
    (φ : H3WeakTestVector) :
    Continuous
      (h3PreterminalTailCanonicalWeakProjectedRHSPairingOnElapsed
        hNS ht htau hEnd hE hTail hEndpoint φ) := by
  unfold h3PreterminalTailCanonicalWeakProjectedRHSPairingOnElapsed

  exact
    (continuous_h3PreterminalTailCanonicalWeakDiffusionPairingOnElapsed
      hNS ht hEnd hTail hEndpoint φ).sub
      (continuous_h3PreterminalTailCanonicalWeakForcingPairingOnElapsed
        hNS ht htau hEnd hE hTail hEndpoint φ)

/-- A compact test times one pure second derivative of a spatially `C²` field
is integrable. -/
theorem h3SpatialC2_test_mul_secondSpatialDerivative_integrable
    {q : ScalarField3}
    (hq : SpatialC2 q)
    (a : PrimeTensor.Axis Depth.three)
    (φ : H3WeakTestFunction) :
    Integrable
      (fun x : Point3 =>
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ x)
          (spatial3.d a (spatial3.d a q) x))
      (volume : Measure Point3) := by
  have hdqC1 :
      SpatialC1 (spatial3.d a q) := by
    exact
      PrimeTensor.Bridge.Euclidean.SpatialC2.partialDeriv_contDiff_one
        hq a

  have hSecondContinuous :
      Continuous
        (spatial3.d a (spatial3.d a q)) :=
    h3SpatialC1_spatial3_d_continuous_weakPressure
      hdqC1 a

  exact
    φ.integrable_bilin
      (ContinuousLinearMap.lsmul ℝ ℝ)
      (hSecondContinuous.locallyIntegrable.locallyIntegrableOn Set.univ)

/-- On a genuine endpoint slice, a compact test times one reconstructed pure
second velocity derivative is integrable. -/
theorem h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_test_mul_secondSpatialDerivative_integrable
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
    (i k : Fin 3)
    (φ : H3WeakTestFunction) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint
    Integrable
      (fun x : Point3 =>
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ x)
          (spatial3.d
            (h3AxisOfFin3 k)
            (spatial3.d
              (h3AxisOfFin3 k)
              (fun y : Point3 =>
                (h3SpectralRealVelocityOfPath W s y).component
                  (h3AxisOfFin3 i)))
            x))
      (volume : Measure Point3) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  let f : ScalarField3 :=
    fun y : Point3 =>
      (h3SpectralRealVelocityOfPath W s y).component
        (h3AxisOfFin3 i)

  have hsClosed :
      s ∈ Set.Icc (0 : ℝ) tau :=
    ⟨hs.1.le, hs.2.le⟩

  have hAbs :
      t + s ∈ Set.Ioo (0 : ℝ) T :=
    h3PreterminalElapsedTime_mem_Ioo
      ht hEnd ⟨s, hsClosed⟩

  let pOld :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        pOld
        T :=
    Classical.choose_spec hNS

  have hOldC3 :
      SpatialC3
        (loggedVelocityComponent
          u
          (t + s)
          (h3AxisOfFin3 i)) := by
    unfold loggedVelocityComponent
    exact
      hPDE.regularity.velocity_spatial_three
        (t + s)
        hAbs
        (h3AxisOfFin3 i)

  have hOldEq :
      f
        =
      loggedVelocityComponent
        u
        (t + s)
        (h3AxisOfFin3 i) := by
    dsimp only [f, W]
    exact
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_component_eq_old
        hNS ht htau hEnd hE hTail hEndpoint
        s hsClosed i

  have hfC2 :
      SpatialC2 f := by
    rw [hOldEq]
    exact hOldC3.of_le (by norm_num)

  simpa only [f] using
    h3SpatialC2_test_mul_secondSpatialDerivative_integrable
      hfC2
      (h3AxisOfFin3 k)
      φ

/-- At every strict interior elapsed time, the pointwise weak temporal pairing
equals the continuous weak projected RHS pairing. -/
theorem h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_weakTemporalPairing_eq_weakProjectedRHSPairingOnElapsed
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
    h3PreterminalTailCanonicalWeakProjectedRHSPairingOnElapsed
      hNS ht htau hEnd hE hTail hEndpoint φ
      ⟨s, hsClosed⟩ := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  have hsClosed :
      s ∈ Set.Icc (0 : ℝ) tau :=
    ⟨hs.1.le, hs.2.le⟩

  let q : Set.Icc (0 : ℝ) tau :=
    ⟨s, hsClosed⟩

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

  have hSplit
      (i : Fin 3) :
      (∫ x : Point3,
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
        ∂volume)
        =
      (∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (temporal.d
            (fun r : ℝ =>
              (h3SpectralRealVelocityOfPath W r x).component
                (h3AxisOfFin3 i))
            s)
        ∂volume)
        +
      (∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          ((h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
            (W s) (W s) i x).re)
        ∂volume)
        -
      ∑ k : Fin 3,
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (spatial3.d
              (h3AxisOfFin3 k)
              (spatial3.d
                (h3AxisOfFin3 k)
                (fun y : Point3 =>
                  (h3SpectralRealVelocityOfPath W s y).component
                    (h3AxisOfFin3 i)))
              x)
          ∂volume := by
    have hT :
        Integrable
          (fun x : Point3 =>
            (ContinuousLinearMap.lsmul ℝ ℝ)
              (φ i x)
              (temporal.d
                (fun r : ℝ =>
                  (h3SpectralRealVelocityOfPath W r x).component
                    (h3AxisOfFin3 i))
                s))
          (volume : Measure Point3) := by
      simpa only [W] using
        h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_test_mul_temporalDerivative_integrable
          hNS ht htau hEnd hE hTail hEndpoint hs i (φ i)

    have hF :
        Integrable
          (fun x : Point3 =>
            (ContinuousLinearMap.lsmul ℝ ℝ)
              (φ i x)
              ((h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
                (W s) (W s) i x).re))
          (volume : Measure Point3) := by
      exact
        h3RawFinLerayOuterProductDivergenceWeakPairing_integrable
          (φ i) i (W s)

    have hD
        (k : Fin 3) :
        Integrable
          (fun x : Point3 =>
            (ContinuousLinearMap.lsmul ℝ ℝ)
              (φ i x)
              (spatial3.d
                (h3AxisOfFin3 k)
                (spatial3.d
                  (h3AxisOfFin3 k)
                  (fun y : Point3 =>
                    (h3SpectralRealVelocityOfPath W s y).component
                      (h3AxisOfFin3 i)))
                x))
          (volume : Measure Point3) := by
      simpa only [W] using
        h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_test_mul_secondSpatialDerivative_integrable
          hNS ht htau hEnd hE hTail hEndpoint hs i k (φ i)

    have hDSum :
        Integrable
          (fun x : Point3 =>
            ∑ k : Fin 3,
              (ContinuousLinearMap.lsmul ℝ ℝ)
                (φ i x)
                (spatial3.d
                  (h3AxisOfFin3 k)
                  (spatial3.d
                    (h3AxisOfFin3 k)
                    (fun y : Point3 =>
                      (h3SpectralRealVelocityOfPath W s y).component
                        (h3AxisOfFin3 i)))
                  x))
          (volume : Measure Point3) := by
      exact
        integrable_finset_sum
          (Finset.univ : Finset (Fin 3))
          (fun k _ => hD k)

    calc
      (∫ x : Point3,
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
        ∂volume)
          =
        ∫ x : Point3,
          ((ContinuousLinearMap.lsmul ℝ ℝ)
              (φ i x)
              (temporal.d
                (fun r : ℝ =>
                  (h3SpectralRealVelocityOfPath W r x).component
                    (h3AxisOfFin3 i))
                s)
            +
           (ContinuousLinearMap.lsmul ℝ ℝ)
              (φ i x)
              ((h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
                (W s) (W s) i x).re)
            -
           ∑ k : Fin 3,
             (ContinuousLinearMap.lsmul ℝ ℝ)
               (φ i x)
               (spatial3.d
                 (h3AxisOfFin3 k)
                 (spatial3.d
                   (h3AxisOfFin3 k)
                   (fun y : Point3 =>
                     (h3SpectralRealVelocityOfPath W s y).component
                       (h3AxisOfFin3 i)))
                 x))
          ∂volume := by
            apply integral_congr_ae
            filter_upwards with x
            change
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
                =
              (φ i x) *
                  temporal.d
                    (fun r : ℝ =>
                      (h3SpectralRealVelocityOfPath W r x).component
                        (h3AxisOfFin3 i))
                    s
                +
              (φ i x) *
                  (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
                    (W s) (W s) i x).re
                -
              ∑ k : Fin 3,
                (φ i x) *
                  spatial3.d
                    (h3AxisOfFin3 k)
                    (spatial3.d
                      (h3AxisOfFin3 k)
                      (fun y : Point3 =>
                        (h3SpectralRealVelocityOfPath W s y).component
                          (h3AxisOfFin3 i)))
                    x
            rw [mul_sub, mul_add, Finset.mul_sum]
      _ =
        ((∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (temporal.d
              (fun r : ℝ =>
                (h3SpectralRealVelocityOfPath W r x).component
                  (h3AxisOfFin3 i))
              s)
          ∂volume)
          +
        (∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            ((h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              (W s) (W s) i x).re)
          ∂volume))
          -
        ∫ x : Point3,
          ∑ k : Fin 3,
            (ContinuousLinearMap.lsmul ℝ ℝ)
              (φ i x)
              (spatial3.d
                (h3AxisOfFin3 k)
                (spatial3.d
                  (h3AxisOfFin3 k)
                  (fun y : Point3 =>
                    (h3SpectralRealVelocityOfPath W s y).component
                      (h3AxisOfFin3 i)))
                x)
          ∂volume := by
            let TF : Point3 → ℝ :=
              fun x =>
                (ContinuousLinearMap.lsmul ℝ ℝ)
                  (φ i x)
                  (temporal.d
                    (fun r : ℝ =>
                      (h3SpectralRealVelocityOfPath W r x).component
                        (h3AxisOfFin3 i))
                    s)

            let FF : Point3 → ℝ :=
              fun x =>
                (ContinuousLinearMap.lsmul ℝ ℝ)
                  (φ i x)
                  ((h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
                    (W s) (W s) i x).re)

            let DF : Point3 → ℝ :=
              fun x =>
                ∑ k : Fin 3,
                  (ContinuousLinearMap.lsmul ℝ ℝ)
                    (φ i x)
                    (spatial3.d
                      (h3AxisOfFin3 k)
                      (spatial3.d
                        (h3AxisOfFin3 k)
                        (fun y : Point3 =>
                          (h3SpectralRealVelocityOfPath W s y).component
                            (h3AxisOfFin3 i)))
                      x)

            have hTF : Integrable TF (volume : Measure Point3) := by
              simpa only [TF] using hT

            have hFF : Integrable FF (volume : Measure Point3) := by
              simpa only [FF] using hF

            have hDF : Integrable DF (volume : Measure Point3) := by
              simpa only [DF] using hDSum

            change
              (∫ x : Point3, (TF x + FF x) - DF x ∂volume)
                =
              ((∫ x : Point3, TF x ∂volume) +
               (∫ x : Point3, FF x ∂volume))
                -
              ∫ x : Point3, DF x ∂volume

            have hSub :
                (∫ x : Point3, (TF x + FF x) - DF x ∂volume)
                  =
                (∫ x : Point3, TF x + FF x ∂volume)
                  -
                ∫ x : Point3, DF x ∂volume := by
              simpa only [Pi.add_apply, Pi.sub_apply] using
                (integral_sub (hTF.add hFF) hDF)

            have hAdd :
                (∫ x : Point3, TF x + FF x ∂volume)
                  =
                (∫ x : Point3, TF x ∂volume)
                  +
                ∫ x : Point3, FF x ∂volume := by
              simpa only [Pi.add_apply] using
                (integral_add hTF hFF)

            calc
              (∫ x : Point3, (TF x + FF x) - DF x ∂volume)
                  =
                (∫ x : Point3, TF x + FF x ∂volume)
                  -
                ∫ x : Point3, DF x ∂volume :=
                hSub
              _ =
                ((∫ x : Point3, TF x ∂volume) +
                 (∫ x : Point3, FF x ∂volume))
                  -
                ∫ x : Point3, DF x ∂volume := by
                  rw [hAdd]
      _ =
        (∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (temporal.d
              (fun r : ℝ =>
                (h3SpectralRealVelocityOfPath W r x).component
                  (h3AxisOfFin3 i))
              s)
          ∂volume)
          +
        (∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            ((h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              (W s) (W s) i x).re)
          ∂volume)
          -
        ∑ k : Fin 3,
          ∫ x : Point3,
            (ContinuousLinearMap.lsmul ℝ ℝ)
              (φ i x)
              (spatial3.d
                (h3AxisOfFin3 k)
                (spatial3.d
                  (h3AxisOfFin3 k)
                  (fun y : Point3 =>
                    (h3SpectralRealVelocityOfPath W s y).component
                      (h3AxisOfFin3 i)))
                x)
            ∂volume := by
              rw [
                integral_finset_sum
                  (Finset.univ : Finset (Fin 3))
                  (fun k _ => hD k)
              ]

  have hWeakSplit :
      ∑ i : Fin 3,
        ((∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (temporal.d
              (fun r : ℝ =>
                (h3SpectralRealVelocityOfPath W r x).component
                  (h3AxisOfFin3 i))
              s)
          ∂volume)
          +
        (∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            ((h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              (W s) (W s) i x).re)
          ∂volume)
          -
        ∑ k : Fin 3,
          ∫ x : Point3,
            (ContinuousLinearMap.lsmul ℝ ℝ)
              (φ i x)
              (spatial3.d
                (h3AxisOfFin3 k)
                (spatial3.d
                  (h3AxisOfFin3 k)
                  (fun y : Point3 =>
                    (h3SpectralRealVelocityOfPath W s y).component
                      (h3AxisOfFin3 i)))
                x)
            ∂volume)
        =
      0 := by
    calc
      (∑ i : Fin 3,
        ((∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (temporal.d
              (fun r : ℝ =>
                (h3SpectralRealVelocityOfPath W r x).component
                  (h3AxisOfFin3 i))
              s)
          ∂volume)
          +
        (∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            ((h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              (W s) (W s) i x).re)
          ∂volume)
          -
        ∑ k : Fin 3,
          ∫ x : Point3,
            (ContinuousLinearMap.lsmul ℝ ℝ)
              (φ i x)
              (spatial3.d
                (h3AxisOfFin3 k)
                (spatial3.d
                  (h3AxisOfFin3 k)
                  (fun y : Point3 =>
                    (h3SpectralRealVelocityOfPath W s y).component
                      (h3AxisOfFin3 i)))
                x)
            ∂volume))
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
              exact (hSplit i).symm
      _ = 0 := hWeak

  have hAlgebra :
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
      (∑ i : Fin 3,
        ∑ k : Fin 3,
          ∫ x : Point3,
            (ContinuousLinearMap.lsmul ℝ ℝ)
              (φ i x)
              (spatial3.d
                (h3AxisOfFin3 k)
                (spatial3.d
                  (h3AxisOfFin3 k)
                  (fun y : Point3 =>
                    (h3SpectralRealVelocityOfPath W s y).component
                      (h3AxisOfFin3 i)))
                x)
            ∂volume)
        -
      (∑ i : Fin 3,
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            ((h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              (W s) (W s) i x).re)
          ∂volume) := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hWeakSplit
    linarith

  have hDiff :
      h3PreterminalTailCanonicalWeakDiffusionPairingOnElapsed
          hNS ht hEnd hTail φ q
        =
      ∑ i : Fin 3,
        ∑ k : Fin 3,
          ∫ x : Point3,
            (ContinuousLinearMap.lsmul ℝ ℝ)
              (φ i x)
              (spatial3.d
                (h3AxisOfFin3 k)
                (spatial3.d
                  (h3AxisOfFin3 k)
                  (fun y : Point3 =>
                    (h3SpectralRealVelocityOfPath W s y).component
                      (h3AxisOfFin3 i)))
                x)
            ∂volume := by
    simpa only [q, W] using
      h3PreterminalTailCanonicalWeakDiffusionPairingOnElapsed_eq_endpointSecondDerivativeIntegrals
        hNS ht htau hEnd hE hTail hEndpoint φ q

  have hForce :
      h3PreterminalTailCanonicalWeakForcingPairingOnElapsed
          hNS ht htau hEnd hE hTail hEndpoint φ q
        =
      ∑ i : Fin 3,
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            ((h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              (W s) (W s) i x).re)
          ∂volume := by
    unfold h3PreterminalTailCanonicalWeakForcingPairingOnElapsed
    dsimp only [q, W]
    rfl

  unfold h3PreterminalTailCanonicalWeakProjectedRHSPairingOnElapsed

  rw [hDiff, hForce]

  exact hAlgebra

/-- The continuous weak projected RHS pairing is exactly the compact-test
pairing with the quotient-safe physical `L²` RHS at every strict interior
elapsed time. -/
theorem h3PreterminalTailCanonicalWeakProjectedRHSPairingOnElapsed_eq_projectedRHSPhysicalL2
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
    let hsClosed : s ∈ Set.Icc (0 : ℝ) tau :=
      ⟨hs.1.le, hs.2.le⟩
    let R : Fin 3 → H3ScalarL2 :=
      h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Vector
        hNS ht htau hEnd hE hTail hEndpoint s hsClosed
    h3PreterminalTailCanonicalWeakProjectedRHSPairingOnElapsed
        hNS ht htau hEnd hE hTail hEndpoint φ
        ⟨s, hsClosed⟩
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

  have hTemporal :
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
      h3PreterminalTailCanonicalWeakProjectedRHSPairingOnElapsed
        hNS ht htau hEnd hE hTail hEndpoint φ
        ⟨s, hsClosed⟩ := by
    simpa only [W, hsClosed] using
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_weakTemporalPairing_eq_weakProjectedRHSPairingOnElapsed
        hNS ht htau hEnd hE hTail hEndpoint hs φ hφ

  have hL2 :
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
    simpa only [W, R, hsClosed] using
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_weakTemporalPairing_eq_projectedRHSPhysicalL2
        hNS ht htau hEnd hE hTail hEndpoint hs φ hφ

  exact hTemporal.symm.trans hL2

end

end Euclidean
end Bridge
end PrimeTensor
