import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Weak.Velocity.Pairing.FTC.Reduction

/-!
# Classicalization: continuous quotient-safe weak `L²` RHS pairing

The preceding stack constructs a continuous scalar weak projected RHS pairing

    weakDiffusionφ - weakForcingφ

on the complete closed elapsed interval.  At strict interior times it was
already identified with the quotient-safe physical `L²` RHS by passing through
the pointwise temporal derivative.

For the next density step, that interior restriction is unnecessary.  This
file proves the representation identity directly on every closed elapsed slice.

For a compact test vector `φ`, package the physical `L²` RHS pairing as

    Σᵢ ⟪φᵢ, Rᵢ(s)⟫_{L²}.

Using:

* the canonical `L²` representative of each compact test;
* the almost-everywhere representative of the physical projected RHS;
* the already-proved twofold spatial integration by parts for diffusion; and
* the continuous forcing representative,

we identify this Hilbert-space pairing directly with the continuous weak
projected RHS pairing for every `s ∈ [0,τ]`.

Consequently the quotient-safe physical `L²` RHS pairing itself is continuous
on the whole closed elapsed interval, without asserting continuity of the
`L²`-valued RHS path.

This is the exact scalar topology needed before upgrading weak integral
evolution by density in the solenoidal `L²` subspace.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PhysicalTailEndpointCanonicalWeakL2RHSPairing
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PhysicalTailEndpointCanonicalWeakL2RHSPairing :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Hilbert pairing of a compactly supported smooth scalar test with an
arbitrary physical real `L²(Point3)` class, written as the literal spatial
integral of representatives. -/
theorem h3WeakTestFunctionPhysicalL2_inner_eq_integral
    (φ : H3WeakTestFunction)
    (F : H3ScalarL2) :
    inner ℝ
        (h3WeakTestFunctionPhysicalL2 φ)
        F
      =
    ∫ x : Point3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ x)
        (F x)
      ∂volume := by
  let Φ : H3ScalarL2 :=
    h3WeakTestFunctionPhysicalL2 φ

  have hΦ :
      (Φ : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      (φ : Point3 → ℝ) := by
    dsimp only [Φ]
    exact h3WeakTestFunctionPhysicalL2_ae φ

  change
    inner ℝ Φ F
      =
    ∫ x : Point3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ x)
        (F x)
      ∂volume

  rw [MeasureTheory.L2.inner_def]

  apply integral_congr_ae

  filter_upwards [hΦ] with x hx

  rw [hx]

  simpa [mul_comm]

/-- Closed-interval version of the compact-test second-derivative
integrability lemma.

Unlike the strict-interior theorem used for the pointwise temporal residual,
this result needs only `s ∈ [0,τ]`: the absolute old time `t+s` remains strictly
preterminal because `t+τ<T`. -/
theorem h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_test_mul_secondSpatialDerivative_integrable_closed
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
    (hs : s ∈ Set.Icc (0 : ℝ) tau)
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

  have hAbs :
      t + s ∈ Set.Ioo (0 : ℝ) T :=
    h3PreterminalElapsedTime_mem_Ioo
      ht hEnd ⟨s, hs⟩

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
        s hs i

  have hfC2 :
      SpatialC2 f := by
    rw [hOldEq]
    exact hOldC3.of_le (by norm_num)

  simpa only [f] using
    h3SpatialC2_test_mul_secondSpatialDerivative_integrable
      hfC2
      (h3AxisOfFin3 k)
      φ

/-- Quotient-safe physical `L²` pairing of the compact test vector with the
projected endpoint RHS on the closed elapsed interval. -/
noncomputable def h3PreterminalTailCanonicalProjectedRHSPhysicalL2WeakPairingOnElapsed
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
  ∑ i : Fin 3,
    inner ℝ
      (h3WeakTestFunctionPhysicalL2 (φ i))
      (h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2
        hNS ht htau hEnd hE hTail hEndpoint
        (q : ℝ) q.property i)

/-- One coordinate of the quotient-safe physical `L²` RHS pairing equals the
literal diffusion-minus-forcing compact-test pairing on every closed elapsed
slice. -/
theorem h3PreterminalTailCanonicalProjectedRHSPhysicalL2WeakPairingOnElapsed_coordinate_eq
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
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint
    inner ℝ
        (h3WeakTestFunctionPhysicalL2 (φ i))
        (h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2
          hNS ht htau hEnd hE hTail hEndpoint
          (q : ℝ) q.property i)
      =
    (∑ k : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (spatial3.d
            (h3AxisOfFin3 k)
            (spatial3.d
              (h3AxisOfFin3 k)
              (fun y : Point3 =>
                (h3SpectralRealVelocityOfPath W (q : ℝ) y).component
                  (h3AxisOfFin3 i)))
            x)
        ∂volume)
      -
    ∫ x : Point3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ i x)
        ((h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
          (W (q : ℝ)) (W (q : ℝ)) i x).re)
      ∂volume := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  let R : H3ScalarL2 :=
    h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2
      hNS ht htau hEnd hE hTail hEndpoint
      (q : ℝ) q.property i

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
                (h3SpectralRealVelocityOfPath W (q : ℝ) y).component
                  (h3AxisOfFin3 i)))
            x)
          -
        (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
          (W (q : ℝ)) (W (q : ℝ)) i x).re) := by
    dsimp only [R, W]
    exact
      h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2_ae
        hNS ht htau hEnd hE hTail hEndpoint
        (q : ℝ) q.property i

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
                  (h3SpectralRealVelocityOfPath W (q : ℝ) y).component
                    (h3AxisOfFin3 i)))
              x))
        (volume : Measure Point3) := by
    simpa only [W] using
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_test_mul_secondSpatialDerivative_integrable_closed
        hNS ht htau hEnd hE hTail hEndpoint
        q.property i k (φ i)

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
                    (h3SpectralRealVelocityOfPath W (q : ℝ) y).component
                      (h3AxisOfFin3 i)))
                x))
        (volume : Measure Point3) := by
    exact
      integrable_finset_sum
        (Finset.univ : Finset (Fin 3))
        (fun k _ => hD k)

  have hF :
      Integrable
        (fun x : Point3 =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            ((h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              (W (q : ℝ)) (W (q : ℝ)) i x).re))
        (volume : Measure Point3) := by
    exact
      h3RawFinLerayOuterProductDivergenceWeakPairing_integrable
        (φ i) i (W (q : ℝ))

  have hInner :
      inner ℝ
          (h3WeakTestFunctionPhysicalL2 (φ i))
          R
        =
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (R x)
        ∂volume :=
    h3WeakTestFunctionPhysicalL2_inner_eq_integral
      (φ i) R

  calc
    inner ℝ
        (h3WeakTestFunctionPhysicalL2 (φ i))
        R
        =
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (R x)
        ∂volume :=
      hInner
    _ =
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          ((∑ k : Fin 3,
            spatial3.d
              (h3AxisOfFin3 k)
              (spatial3.d
                (h3AxisOfFin3 k)
                (fun y : Point3 =>
                  (h3SpectralRealVelocityOfPath W (q : ℝ) y).component
                    (h3AxisOfFin3 i)))
              x)
            -
          (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
            (W (q : ℝ)) (W (q : ℝ)) i x).re)
        ∂volume := by
          apply integral_congr_ae
          filter_upwards [hRhsAE] with x hx
          rw [hx]
    _ =
      ∫ x : Point3,
        ((∑ k : Fin 3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (spatial3.d
              (h3AxisOfFin3 k)
              (spatial3.d
                (h3AxisOfFin3 k)
                (fun y : Point3 =>
                  (h3SpectralRealVelocityOfPath W (q : ℝ) y).component
                    (h3AxisOfFin3 i)))
              x))
          -
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          ((h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
            (W (q : ℝ)) (W (q : ℝ)) i x).re))
        ∂volume := by
          apply integral_congr_ae
          filter_upwards with x
          change
            (φ i x) *
                ((∑ k : Fin 3,
                  spatial3.d
                    (h3AxisOfFin3 k)
                    (spatial3.d
                      (h3AxisOfFin3 k)
                      (fun y : Point3 =>
                        (h3SpectralRealVelocityOfPath W (q : ℝ) y).component
                          (h3AxisOfFin3 i)))
                    x)
                  -
                (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
                  (W (q : ℝ)) (W (q : ℝ)) i x).re)
              =
            (∑ k : Fin 3,
              (φ i x) *
                spatial3.d
                  (h3AxisOfFin3 k)
                  (spatial3.d
                    (h3AxisOfFin3 k)
                    (fun y : Point3 =>
                      (h3SpectralRealVelocityOfPath W (q : ℝ) y).component
                        (h3AxisOfFin3 i)))
                  x)
              -
            (φ i x) *
              (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
                (W (q : ℝ)) (W (q : ℝ)) i x).re
          rw [mul_sub, Finset.mul_sum]
    _ =
      (∫ x : Point3,
        ∑ k : Fin 3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (spatial3.d
              (h3AxisOfFin3 k)
              (spatial3.d
                (h3AxisOfFin3 k)
                (fun y : Point3 =>
                  (h3SpectralRealVelocityOfPath W (q : ℝ) y).component
                    (h3AxisOfFin3 i)))
              x)
        ∂volume)
        -
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          ((h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
            (W (q : ℝ)) (W (q : ℝ)) i x).re)
        ∂volume := by
          exact integral_sub hDSum hF
    _ =
      (∑ k : Fin 3,
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (spatial3.d
              (h3AxisOfFin3 k)
              (spatial3.d
                (h3AxisOfFin3 k)
                (fun y : Point3 =>
                  (h3SpectralRealVelocityOfPath W (q : ℝ) y).component
                    (h3AxisOfFin3 i)))
              x)
          ∂volume)
        -
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          ((h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
            (W (q : ℝ)) (W (q : ℝ)) i x).re)
        ∂volume := by
          rw [
            integral_finset_sum
              (Finset.univ : Finset (Fin 3))
              (fun k _ => hD k)
          ]

/-- The quotient-safe physical `L²` RHS pairing and the previously constructed
continuous weak projected RHS pairing are identical on the *entire* closed
elapsed interval.  No temporal derivative and no divergence-free assumption
are needed for this representation theorem. -/
theorem h3PreterminalTailCanonicalProjectedRHSPhysicalL2WeakPairingOnElapsed_eq_weakProjectedRHSPairingOnElapsed
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
    h3PreterminalTailCanonicalProjectedRHSPhysicalL2WeakPairingOnElapsed
        hNS ht htau hEnd hE hTail hEndpoint φ q
      =
    h3PreterminalTailCanonicalWeakProjectedRHSPairingOnElapsed
      hNS ht htau hEnd hE hTail hEndpoint φ q := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  have hCoord
      (i : Fin 3) :
      inner ℝ
          (h3WeakTestFunctionPhysicalL2 (φ i))
          (h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2
            hNS ht htau hEnd hE hTail hEndpoint
            (q : ℝ) q.property i)
        =
      (∑ k : Fin 3,
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (spatial3.d
              (h3AxisOfFin3 k)
              (spatial3.d
                (h3AxisOfFin3 k)
                (fun y : Point3 =>
                  (h3SpectralRealVelocityOfPath W (q : ℝ) y).component
                    (h3AxisOfFin3 i)))
              x)
          ∂volume)
        -
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          ((h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
            (W (q : ℝ)) (W (q : ℝ)) i x).re)
        ∂volume := by
    simpa only [W] using
      h3PreterminalTailCanonicalProjectedRHSPhysicalL2WeakPairingOnElapsed_coordinate_eq
        hNS ht htau hEnd hE hTail hEndpoint φ q i

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
                    (h3SpectralRealVelocityOfPath W (q : ℝ) y).component
                      (h3AxisOfFin3 i)))
                x)
            ∂volume := by
    simpa only [W] using
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
              (W (q : ℝ)) (W (q : ℝ)) i x).re)
          ∂volume := by
    unfold h3PreterminalTailCanonicalWeakForcingPairingOnElapsed
    dsimp only [W]
    rfl

  unfold h3PreterminalTailCanonicalProjectedRHSPhysicalL2WeakPairingOnElapsed
  unfold h3PreterminalTailCanonicalWeakProjectedRHSPairingOnElapsed

  calc
    (∑ i : Fin 3,
      inner ℝ
        (h3WeakTestFunctionPhysicalL2 (φ i))
        (h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2
          hNS ht htau hEnd hE hTail hEndpoint
          (q : ℝ) q.property i))
        =
      ∑ i : Fin 3,
        ((∑ k : Fin 3,
          ∫ x : Point3,
            (ContinuousLinearMap.lsmul ℝ ℝ)
              (φ i x)
              (spatial3.d
                (h3AxisOfFin3 k)
                (spatial3.d
                  (h3AxisOfFin3 k)
                  (fun y : Point3 =>
                    (h3SpectralRealVelocityOfPath W (q : ℝ) y).component
                      (h3AxisOfFin3 i)))
                x)
            ∂volume)
          -
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            ((h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              (W (q : ℝ)) (W (q : ℝ)) i x).re)
          ∂volume) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hCoord i
    _ =
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
                    (h3SpectralRealVelocityOfPath W (q : ℝ) y).component
                      (h3AxisOfFin3 i)))
                x)
            ∂volume)
        -
      ∑ i : Fin 3,
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            ((h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              (W (q : ℝ)) (W (q : ℝ)) i x).re)
          ∂volume := by
            rw [Finset.sum_sub_distrib]
    _ =
      h3PreterminalTailCanonicalWeakDiffusionPairingOnElapsed
          hNS ht hEnd hTail φ q
        -
      h3PreterminalTailCanonicalWeakForcingPairingOnElapsed
          hNS ht htau hEnd hE hTail hEndpoint φ q := by
            rw [hDiff, hForce]
    _ =
      h3PreterminalTailCanonicalWeakDiffusionPairingOnElapsed
          hNS ht hEnd hTail φ q
        -
      h3PreterminalTailCanonicalWeakForcingPairingOnElapsed
          hNS ht htau hEnd hE hTail hEndpoint φ q := rfl

/-- The quotient-safe physical `L²` RHS pairing is continuous on the complete
closed elapsed interval.

This does **not** assert that the `L²`-valued RHS path itself is strongly
continuous; only every fixed compact-test Hilbert pairing is identified with
the already-proved continuous scalar weak RHS. -/
theorem continuous_h3PreterminalTailCanonicalProjectedRHSPhysicalL2WeakPairingOnElapsed
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
      (h3PreterminalTailCanonicalProjectedRHSPhysicalL2WeakPairingOnElapsed
        hNS ht htau hEnd hE hTail hEndpoint φ) := by
  have hEq :
      h3PreterminalTailCanonicalProjectedRHSPhysicalL2WeakPairingOnElapsed
          hNS ht htau hEnd hE hTail hEndpoint φ
        =
      h3PreterminalTailCanonicalWeakProjectedRHSPairingOnElapsed
        hNS ht htau hEnd hE hTail hEndpoint φ := by
    funext q
    exact
      h3PreterminalTailCanonicalProjectedRHSPhysicalL2WeakPairingOnElapsed_eq_weakProjectedRHSPairingOnElapsed
        hNS ht htau hEnd hE hTail hEndpoint φ q

  rw [hEq]

  exact
    continuous_h3PreterminalTailCanonicalWeakProjectedRHSPairingOnElapsed
      hNS ht htau hEnd hE hTail hEndpoint φ

end

end Euclidean
end Bridge
end PrimeTensor
