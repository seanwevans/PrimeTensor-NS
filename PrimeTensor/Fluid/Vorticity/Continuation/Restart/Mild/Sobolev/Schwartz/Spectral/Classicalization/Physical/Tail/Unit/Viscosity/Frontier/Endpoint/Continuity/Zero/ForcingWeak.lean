import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.RHSReality
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Weak.Forcing.Pairing.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Pressure.Force

/-!
# Zeroth-order endpoint continuity: old weak Leray forcing

The old snapshot nonlinear bridge identifies the unprojected raw Fourier
divergence with the old physical advection.  The bounded projected RHS uses the
Leray-projected divergence instead.

For a single elapsed snapshot `q`, let `U_q` be the canonical old H³ spectral
state and consider the constant auxiliary path

    W(s) = U_q.

The generic spectral pressure construction attached to `W` satisfies

    -∇p_spec
      =
    Re F⁻¹ div̂(U_q ⊗ U_q)
      -
    Re F⁻¹ P div̂(U_q ⊗ U_q).

The first term is exactly old physical advection by `Zero.Advection`.  Pairing
the identity with a compact smooth divergence-free test vector annihilates the
pressure gradient.  Therefore the Leray-projected nonlinear weak pairing is
exactly the old physical advection weak pairing.

Everything here is snapshot-local and endpoint-continuity free.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityZeroOldWeakForcing
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3UnitViscosityZeroOldWeakForcing :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- On one old elapsed snapshot, the Leray-projected nonlinear weak pairing is
exactly the old physical advection pairing against every divergence-free
compact smooth test vector. -/
theorem h3PreterminalTailCanonicalZeroWeakForcingPairingOnElapsed_eq_oldAdvection
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ) :
    (∑ i : Fin 3,
      h3RawFinLerayOuterProductDivergenceWeakPairing
        (φ i) i
        (h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail q))
      =
    ∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          ((PrimeTensor.Bridge.RealFluid.advection
            spatial3
            (logSpaceTimeVectorField u)
            (t + (q : ℝ))
            x).component
              (h3AxisOfFin3 i))
        ∂volume := by
  let U : H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSpectralStateOnElapsed
      hNS ht hEnd hTail q

  let W : ℝ → H3SpectralFinVectorState :=
    fun _ => U

  let pCan :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    h3RawFinPressureRealC1OfPath W

  have hpC1 :
      SpatialC1 (pCan 0) := by
    dsimp only [
      pCan,
      h3RawFinPressureRealC1OfPath,
      W
    ]

    exact
      h3RawFinPressureRealC1RepresentativeOnPoint3_contDiff_one
        U U

  have hGrad :
      ∑ i : Fin 3,
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (spatial3.d
              (h3AxisOfFin3 i)
              (pCan 0)
              x)
          ∂volume
        =
      0 :=
    h3SpatialC1_gradient_pairing_eq_zero_of_testDivergenceFree
      (pCan 0) hpC1 φ hφ

  have hCoord
      (i : Fin 3) :
      h3RawFinLerayOuterProductDivergenceWeakPairing
          (φ i) i U
        -
      (∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          ((PrimeTensor.Bridge.RealFluid.advection
            spatial3
            (logSpaceTimeVectorField u)
            (t + (q : ℝ))
            x).component
              (h3AxisOfFin3 i))
        ∂volume)
        =
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (spatial3.d
            (h3AxisOfFin3 i)
            (pCan 0)
            x)
        ∂volume := by
    have hForce :
        Integrable
          (fun x : Point3 =>
            (ContinuousLinearMap.lsmul ℝ ℝ)
              (φ i x)
              ((h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
                U U i x).re))
          (volume : Measure Point3) :=
      h3RawFinLerayOuterProductDivergenceWeakPairing_integrable
        (φ i) i U

    have hGradCoord :
        Integrable
          (fun x : Point3 =>
            (ContinuousLinearMap.lsmul ℝ ℝ)
              (φ i x)
              (spatial3.d
                (h3AxisOfFin3 i)
                (pCan 0)
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
            U U i x).re
          -
        (PrimeTensor.Bridge.RealFluid.advection
          spatial3
          (logSpaceTimeVectorField u)
          (t + (q : ℝ))
          x).component
            (h3AxisOfFin3 i)
          =
        spatial3.d
          (h3AxisOfFin3 i)
          (pCan 0)
          x := by
      have hPressure :=
        h3RawFinPressureRealC1OfPath_pressureForceComponent_eq_raw_sub_leray
          W 0 i x

      have hAdv :=
        h3PreterminalTailCanonicalRawOuterDivergence_fourierInv_re_eq_old_advection
          hNS ht hEnd hTail q i x

      change
        -spatial3.d
            (h3AxisOfFin3 i)
            (pCan 0)
            x
          =
        (FourierTransformInv.fourierInv
          (h3RawFinOuterProductDivergence
            U U i)
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re
          -
        (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
          U U i x).re
        at hPressure

      have hAdv' :
          (FourierTransformInv.fourierInv
            (h3RawFinOuterProductDivergence
              U U i)
            ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re
            =
          (PrimeTensor.Bridge.RealFluid.advection
            spatial3
            (logSpaceTimeVectorField u)
            (t + (q : ℝ))
            x).component
              (h3AxisOfFin3 i) := by
        simpa only [U] using hAdv

      rw [hAdv'] at hPressure
      linarith

    have hAdvEq :
        (fun x : Point3 =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            ((PrimeTensor.Bridge.RealFluid.advection
              spatial3
              (logSpaceTimeVectorField u)
              (t + (q : ℝ))
              x).component
                (h3AxisOfFin3 i)))
          =
        (fun x : Point3 =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            ((h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              U U i x).re)
            -
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (spatial3.d
              (h3AxisOfFin3 i)
              (pCan 0)
              x)) := by
      funext x

      have hAdvScalar :
          (PrimeTensor.Bridge.RealFluid.advection
            spatial3
            (logSpaceTimeVectorField u)
            (t + (q : ℝ))
            x).component
              (h3AxisOfFin3 i)
            =
          (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
            U U i x).re
            -
          spatial3.d
            (h3AxisOfFin3 i)
            (pCan 0)
            x := by
        linarith [hScalar x]

      change
        (φ i x) *
            (PrimeTensor.Bridge.RealFluid.advection
              spatial3
              (logSpaceTimeVectorField u)
              (t + (q : ℝ))
              x).component
                (h3AxisOfFin3 i)
          =
        (φ i x) *
            (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              U U i x).re
          -
        (φ i x) *
          spatial3.d
            (h3AxisOfFin3 i)
            (pCan 0)
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
                (logSpaceTimeVectorField u)
                (t + (q : ℝ))
                x).component
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
                  U U i x).re
              -
            (φ i x) *
                (PrimeTensor.Bridge.RealFluid.advection
                  spatial3
                  (logSpaceTimeVectorField u)
                  (t + (q : ℝ))
                  x).component
                    (h3AxisOfFin3 i)
              =
            (φ i x) *
              spatial3.d
                (h3AxisOfFin3 i)
                (pCan 0)
                x

          rw [← mul_sub]
          rw [hScalar x])

  apply sub_eq_zero.mp

  calc
    (∑ i : Fin 3,
      h3RawFinLerayOuterProductDivergenceWeakPairing
        (φ i) i U)
      -
    (∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          ((PrimeTensor.Bridge.RealFluid.advection
            spatial3
            (logSpaceTimeVectorField u)
            (t + (q : ℝ))
            x).component
              (h3AxisOfFin3 i))
        ∂volume)
        =
      ∑ i : Fin 3,
        (h3RawFinLerayOuterProductDivergenceWeakPairing
            (φ i) i U
          -
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            ((PrimeTensor.Bridge.RealFluid.advection
              spatial3
              (logSpaceTimeVectorField u)
              (t + (q : ℝ))
              x).component
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
              (pCan 0)
              x)
          ∂volume := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hCoord i
    _ = 0 :=
      hGrad

end

end Euclidean
end Bridge
end PrimeTensor
