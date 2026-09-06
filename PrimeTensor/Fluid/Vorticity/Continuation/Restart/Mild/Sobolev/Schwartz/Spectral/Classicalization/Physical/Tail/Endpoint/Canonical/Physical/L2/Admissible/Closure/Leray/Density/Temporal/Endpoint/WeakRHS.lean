import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Advection
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Weak.Projected.RHS.Pairing.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Weak.Pressure.Classical.Bridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Pressure.Force

/-!
# Physical L² temporal admissibility: pressure-free endpoint weak RHS

The endpoint canonical velocity and its first spatial jet are now jointly
continuous without selected/old overlap, and the corresponding physical
advection field is jointly continuous on the physical slab.

This file uses that new physical regularity to identify the already-continuous
weak Leray forcing pairing with the literal physical advection pairing against
divergence-free compact tests.

For the canonical spectral pressure,

    -∂ᵢ p_can
      =
    advectionᵢ - LerayForcingᵢ.

Hence

    LerayForcingᵢ - advectionᵢ = ∂ᵢ p_can.

Summing against a divergence-free compact smooth test vector annihilates the
gradient by the existing classical/distributional integration-by-parts bridge.

Therefore, for every divergence-free weak test,

    weakLerayForcing = weakPhysicalAdvection,

and the continuous weak projected RHS can be written literally as

    weakDiffusion - weakPhysicalAdvection.

This is the pressure-free old-endpoint weak formulation needed for a
non-circular temporal argument.  No selected mild solution, overlap equality,
physical-evolution hypothesis, or second-spatial-jet time regularity is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2TemporalEndpointWeakRHS
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PhysicalL2TemporalEndpointWeakRHS :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Match the norm topology used by the physical weak-test layer. -/
local instance point3NormTopologicalSpaceH3PhysicalL2TemporalEndpointWeakRHS :
    TopologicalSpace Point3 :=
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- Any spatially `C¹` scalar gradient has zero classical pairing with a
divergence-free compact smooth test vector. -/
theorem h3SpatialC1_gradient_pairing_eq_zero_of_testDivergenceFree
    (q : ScalarField3)
    (hq : SpatialC1 q)
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ) :
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
  have hDist :
      ∑ i : Fin 3,
        (((Distribution.lineDerivCLM
          (axisDirection (h3AxisOfFin3 i)) :
            H3WeakScalarDistribution →L[ℝ] H3WeakScalarDistribution)
          (h3WeakDistributionOfFun q))
          (φ i))
        =
      0 :=
    h3DistributionGradient_pairing_eq_zero_of_testDivergenceFree
      q φ hφ

  calc
    (∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (spatial3.d
            (h3AxisOfFin3 i)
            q
            x)
        ∂volume)
        =
      ∑ i : Fin 3,
        (((Distribution.lineDerivCLM
          (axisDirection (h3AxisOfFin3 i)) :
            H3WeakScalarDistribution →L[ℝ] H3WeakScalarDistribution)
          (h3WeakDistributionOfFun q))
          (φ i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      symm
      exact
        h3WeakDistributionOfFun_lineDeriv_apply_eq_integral_spatial3_d
          hq
          (h3AxisOfFin3 i)
          (φ i)
    _ = 0 :=
      hDist

/-- Literal physical endpoint advection pairing against one compact test
vector on a closed elapsed slice. -/
noncomputable def h3PreterminalTailCanonicalWeakPhysicalAdvectionPairingOnElapsed
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
  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint
  ∑ i : Fin 3,
    ∫ x : Point3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ i x)
        ((PrimeTensor.Bridge.RealFluid.advection
          spatial3
          (h3SpectralRealVelocityOfPath W)
          (q : ℝ) x).component
            (h3AxisOfFin3 i))
      ∂volume

/-- On every closed elapsed slice, the Leray-projected nonlinear weak pairing
equals the literal physical advection pairing against every divergence-free
compact smooth test vector. -/
theorem h3PreterminalTailCanonicalWeakForcingPairingOnElapsed_eq_physicalAdvection
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
    (hφ : H3WeakTestVectorDivergenceFree φ)
    (q : Set.Icc (0 : ℝ) tau) :
    h3PreterminalTailCanonicalWeakForcingPairingOnElapsed
        hNS ht htau hEnd hE hTail hEndpoint φ q
      =
    h3PreterminalTailCanonicalWeakPhysicalAdvectionPairingOnElapsed
      hNS ht htau hEnd hE hTail hEndpoint φ q := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  let pCan :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    h3PreterminalTailCanonicalNormalizedRealPressureOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  have hpC1 :
      SpatialC1 (pCan (q : ℝ)) := by
    dsimp only [
      pCan,
      h3PreterminalTailCanonicalNormalizedRealPressureOfL2Endpoint,
      h3RawFinPressureRealC1OfPath
    ]
    exact
      h3RawFinPressureRealC1RepresentativeOnPoint3_contDiff_one
        (W (q : ℝ))
        (W (q : ℝ))

  have hGrad :
      ∑ i : Fin 3,
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (spatial3.d
              (h3AxisOfFin3 i)
              (pCan (q : ℝ))
              x)
          ∂volume
        =
      0 :=
    h3SpatialC1_gradient_pairing_eq_zero_of_testDivergenceFree
      (pCan (q : ℝ)) hpC1 φ hφ

  have hCoord
      (i : Fin 3) :
      h3RawFinLerayOuterProductDivergenceWeakPairing
          (φ i) i (W (q : ℝ))
        -
      (∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          ((PrimeTensor.Bridge.RealFluid.advection
            spatial3
            (h3SpectralRealVelocityOfPath W)
            (q : ℝ) x).component
              (h3AxisOfFin3 i))
        ∂volume)
        =
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (spatial3.d
            (h3AxisOfFin3 i)
            (pCan (q : ℝ))
            x)
        ∂volume := by
    have hForce :
        Integrable
          (fun x : Point3 =>
            (ContinuousLinearMap.lsmul ℝ ℝ)
              (φ i x)
              ((h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
                (W (q : ℝ)) (W (q : ℝ)) i x).re))
          (volume : Measure Point3) :=
      h3RawFinLerayOuterProductDivergenceWeakPairing_integrable
        (φ i) i (W (q : ℝ))

    have hGradCoord :
        Integrable
          (fun x : Point3 =>
            (ContinuousLinearMap.lsmul ℝ ℝ)
              (φ i x)
              (spatial3.d
                (h3AxisOfFin3 i)
                (pCan (q : ℝ))
                x))
          (volume : Measure Point3) := by
      exact
        (φ i).integrable_bilin
          (ContinuousLinearMap.lsmul ℝ ℝ)
          ((h3SpatialC1_spatial3_d_continuous_weakPressure
              hpC1
              (h3AxisOfFin3 i)).locallyIntegrable.locallyIntegrableOn
            Set.univ)

    have hScalar
        (x : Point3) :
        (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
            (W (q : ℝ)) (W (q : ℝ)) i x).re
          -
        (PrimeTensor.Bridge.RealFluid.advection
          spatial3
          (h3SpectralRealVelocityOfPath W)
          (q : ℝ) x).component
            (h3AxisOfFin3 i)
          =
        spatial3.d
          (h3AxisOfFin3 i)
          (pCan (q : ℝ))
          x := by
      have hPressure :=
        h3PreterminalTailCanonicalNormalizedRealPressureOfL2Endpoint_pressureForce_eq_old_advection_sub_leray
          hNS ht htau hEnd hE hTail hEndpoint
          (q : ℝ) q.property i x

      have hAdvectionOld :=
        h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_advection_eq_old
          hNS ht htau hEnd hE hTail hEndpoint
          (q : ℝ) q.property i x

      rw [← hAdvectionOld] at hPressure

      change
        -spatial3.d
            (h3AxisOfFin3 i)
            (pCan (q : ℝ))
            x
          =
        (PrimeTensor.Bridge.RealFluid.advection
          spatial3
          (h3SpectralRealVelocityOfPath W)
          (q : ℝ) x).component
            (h3AxisOfFin3 i)
          -
        (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
          (W (q : ℝ)) (W (q : ℝ)) i x).re
        at hPressure

      linarith

    have hAdvEq :
        (fun x : Point3 =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            ((PrimeTensor.Bridge.RealFluid.advection
              spatial3
              (h3SpectralRealVelocityOfPath W)
              (q : ℝ) x).component
                (h3AxisOfFin3 i)))
          =
        (fun x : Point3 =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            ((h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              (W (q : ℝ)) (W (q : ℝ)) i x).re)
            -
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (spatial3.d
              (h3AxisOfFin3 i)
              (pCan (q : ℝ))
              x)) := by
      funext x
      have hAdvScalar :
          (PrimeTensor.Bridge.RealFluid.advection
            spatial3
            (h3SpectralRealVelocityOfPath W)
            (q : ℝ) x).component
              (h3AxisOfFin3 i)
            =
          (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
            (W (q : ℝ)) (W (q : ℝ)) i x).re
            -
          spatial3.d
            (h3AxisOfFin3 i)
            (pCan (q : ℝ))
            x := by
        linarith [hScalar x]

      change
        (φ i x) *
            (PrimeTensor.Bridge.RealFluid.advection
              spatial3
              (h3SpectralRealVelocityOfPath W)
              (q : ℝ) x).component
                (h3AxisOfFin3 i)
          =
        (φ i x) *
            (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              (W (q : ℝ)) (W (q : ℝ)) i x).re
          -
        (φ i x) *
          spatial3.d
            (h3AxisOfFin3 i)
            (pCan (q : ℝ))
            x

      rw [hAdvScalar]
      ring

    have hAdv :
        Integrable
          (fun x : Point3 =>
            (ContinuousLinearMap.lsmul ℝ ℝ)
              (φ i x)
              ((PrimeTensor.Bridge.RealFluid.advection
                spatial3
                (h3SpectralRealVelocityOfPath W)
                (q : ℝ) x).component
                  (h3AxisOfFin3 i)))
          (volume : Measure Point3) := by
      rw [hAdvEq]
      exact hForce.sub hGradCoord

    unfold
      h3RawFinLerayOuterProductDivergenceWeakPairing

    rw [← integral_sub hForce hAdv]

    apply integral_congr_ae

    exact
      Filter.Eventually.of_forall
        (fun x => by
          change
            (φ i x) *
                (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
                  (W (q : ℝ)) (W (q : ℝ)) i x).re
              -
            (φ i x) *
                (PrimeTensor.Bridge.RealFluid.advection
                  spatial3
                  (h3SpectralRealVelocityOfPath W)
                  (q : ℝ) x).component
                    (h3AxisOfFin3 i)
              =
            (φ i x) *
              spatial3.d
                (h3AxisOfFin3 i)
                (pCan (q : ℝ))
                x

          rw [← mul_sub]
          rw [hScalar x])

  unfold
    h3PreterminalTailCanonicalWeakForcingPairingOnElapsed
    h3PreterminalTailCanonicalWeakPhysicalAdvectionPairingOnElapsed

  dsimp only [W]

  apply sub_eq_zero.mp

  calc
    (∑ i : Fin 3,
      h3RawFinLerayOuterProductDivergenceWeakPairing
        (φ i) i (W (q : ℝ)))
      -
    (∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          ((PrimeTensor.Bridge.RealFluid.advection
            spatial3
            (h3SpectralRealVelocityOfPath W)
            (q : ℝ) x).component
              (h3AxisOfFin3 i))
        ∂volume)
        =
      ∑ i : Fin 3,
        (h3RawFinLerayOuterProductDivergenceWeakPairing
            (φ i) i (W (q : ℝ))
          -
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            ((PrimeTensor.Bridge.RealFluid.advection
              spatial3
              (h3SpectralRealVelocityOfPath W)
              (q : ℝ) x).component
                (h3AxisOfFin3 i))
          ∂volume) := by
      rw [Finset.sum_sub_distrib]
    _ =
      ∑ i : Fin 3,
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (spatial3.d
              (h3AxisOfFin3 i)
              (pCan (q : ℝ))
              x)
          ∂volume := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hCoord i
    _ = 0 :=
      hGrad

/-- Literal pressure-free weak physical RHS pairing:
diffusion, with derivatives already transferred to the compact test, minus
physical endpoint advection. -/
noncomputable def h3PreterminalTailCanonicalWeakPhysicalRHSPairingOnElapsed
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
  h3PreterminalTailCanonicalWeakPhysicalAdvectionPairingOnElapsed
      hNS ht htau hEnd hE hTail hEndpoint φ q

/-- For divergence-free tests, the existing continuous weak projected RHS is
exactly the literal pressure-free physical `diffusion - advection` pairing. -/
theorem h3PreterminalTailCanonicalWeakProjectedRHSPairingOnElapsed_eq_physicalRHS
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
    (hφ : H3WeakTestVectorDivergenceFree φ)
    (q : Set.Icc (0 : ℝ) tau) :
    h3PreterminalTailCanonicalWeakProjectedRHSPairingOnElapsed
        hNS ht htau hEnd hE hTail hEndpoint φ q
      =
    h3PreterminalTailCanonicalWeakPhysicalRHSPairingOnElapsed
      hNS ht htau hEnd hE hTail hEndpoint φ q := by
  unfold
    h3PreterminalTailCanonicalWeakProjectedRHSPairingOnElapsed
    h3PreterminalTailCanonicalWeakPhysicalRHSPairingOnElapsed

  rw [
    h3PreterminalTailCanonicalWeakForcingPairingOnElapsed_eq_physicalAdvection
      hNS ht htau hEnd hE hTail hEndpoint φ hφ q
  ]

/-- Consequently the literal pressure-free physical weak RHS pairing is
continuous on the complete closed elapsed interval. -/
theorem continuous_h3PreterminalTailCanonicalWeakPhysicalRHSPairingOnElapsed
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
    (hφ : H3WeakTestVectorDivergenceFree φ) :
    Continuous
      (h3PreterminalTailCanonicalWeakPhysicalRHSPairingOnElapsed
        hNS ht htau hEnd hE hTail hEndpoint φ) := by
  have hEq :
      h3PreterminalTailCanonicalWeakPhysicalRHSPairingOnElapsed
          hNS ht htau hEnd hE hTail hEndpoint φ
        =
      h3PreterminalTailCanonicalWeakProjectedRHSPairingOnElapsed
          hNS ht htau hEnd hE hTail hEndpoint φ := by
    funext q

    symm

    exact
      h3PreterminalTailCanonicalWeakProjectedRHSPairingOnElapsed_eq_physicalRHS
        hNS ht htau hEnd hE hTail hEndpoint φ hφ q

  rw [hEq]

  exact
    continuous_h3PreterminalTailCanonicalWeakProjectedRHSPairingOnElapsed
      hNS ht htau hEnd hE hTail hEndpoint φ

end

end Euclidean
end Bridge
end PrimeTensor
