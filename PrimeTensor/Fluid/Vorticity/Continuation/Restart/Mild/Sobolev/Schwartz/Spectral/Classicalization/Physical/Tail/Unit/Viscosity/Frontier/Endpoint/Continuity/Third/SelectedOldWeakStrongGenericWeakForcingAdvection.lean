import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.ForcingWeak
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Raw.Outer.Divergence.Advection.Bridge

/-!
# Generic pressure-free weak forcing/advection identity

`Zero.ForcingWeak` proves, for an old preterminal snapshot, that the
Leray-projected nonlinear weak pairing equals the literal physical advection
pairing against every compact smooth divergence-free test vector.

The proof is actually snapshot-generic.  Its only ingredients are:

* physical realizability of the weighted H³ spectral slice;
* raw Fourier divergence-freeness of that slice;
* the generic spectral pressure identity;
* the generic reconstruction of unprojected raw outer-product divergence as
  physical advection;
* annihilation of scalar gradients by compact smooth divergence-free tests.

This file isolates that argument once and for all.  The result can therefore be
instantiated independently on both the selected restart slice and the old
preterminal slice without endpoint continuity or overlap agreement.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongGenericWeakForcingAdvection
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3SelectedOldWeakStrongGenericWeakForcingAdvection :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- For any realizable raw-divergence-free weighted H³ spectral slice, the
Leray-projected nonlinear weak pairing is exactly the physical advection
pairing against every compact smooth divergence-free weak test. -/
theorem h3RawFinLerayOuterProductDivergenceWeakPairing_sum_eq_advection_of_realizable_of_rawDivergenceFree
    (U : H3SpectralFinVectorState)
    (hReal : H3SpectralVelocityRealizable U)
    (hDiv : H3SpectralFinRawDivergenceFree U)
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ) :
    (∑ i : Fin 3,
      h3RawFinLerayOuterProductDivergenceWeakPairing
        (φ i) i U)
      =
    ∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          ((PrimeTensor.Bridge.RealFluid.advection
            spatial3
            (h3SpectralRealVelocityOfPath
              (fun _ : ℝ => U))
            0 x).component
              (h3AxisOfFin3 i))
        ∂volume := by
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
            (h3SpectralRealVelocityOfPath W)
            0 x).component
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
          (h3SpectralRealVelocityOfPath W)
          0
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

      have hAdv :
          (FourierTransformInv.fourierInv
            (h3RawFinOuterProductDivergence
              U U i)
            ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re
            =
          (PrimeTensor.Bridge.RealFluid.advection
            spatial3
            (h3SpectralRealVelocityOfPath W)
            0 x).component
              (h3AxisOfFin3 i) := by
        have hRaw :=
          h3RawFinOuterProductDivergence_fourierInv_re_eq_advection_of_realizable_of_rawDivergenceFree
            W 0
            (by
              simpa only [W] using hReal)
            (by
              simpa only [W] using hDiv)
            i x

        simpa only [W] using hRaw

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

      rw [hAdv] at hPressure
      linarith

    have hAdvEq :
        (fun x : Point3 =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            ((PrimeTensor.Bridge.RealFluid.advection
              spatial3
              (h3SpectralRealVelocityOfPath W)
              0 x).component
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
            (h3SpectralRealVelocityOfPath W)
            0 x).component
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
              (h3SpectralRealVelocityOfPath W)
              0 x).component
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
                (h3SpectralRealVelocityOfPath W)
                0 x).component
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
                  (h3SpectralRealVelocityOfPath W)
                  0 x).component
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
            (h3SpectralRealVelocityOfPath W)
            0 x).component
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
              (h3SpectralRealVelocityOfPath W)
              0 x).component
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
