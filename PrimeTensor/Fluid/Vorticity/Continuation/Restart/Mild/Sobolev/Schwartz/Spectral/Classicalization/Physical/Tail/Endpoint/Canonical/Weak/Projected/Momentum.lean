import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Weak.Pressure.Classical.Bridge

/-!
# Classicalization: pressure-free weak projected momentum

The endpoint reconstructed path satisfies the pointwise identity

    ∂ₛ Wᵢ + (P nonlinear)ᵢ
      = ΔWᵢ - ∂ᵢq,

where `q` is the scalar mismatch between the old preterminal pressure and the
canonical Leray-complement pressure.

The previous file proved the classical weak pressure identity

    Σᵢ ∫ φᵢ ∂ᵢq = 0

for every compactly supported smooth divergence-free test vector `φ`.

This file composes those two facts.  We pair the *whole* projected-momentum
residual before integrating:

    Σᵢ ∫ φᵢ
      (∂ₛ Wᵢ + (P nonlinear)ᵢ - ΔWᵢ)
      = 0.

Keeping the residual intact is deliberate.  At this stage we have not asserted
that the pointwise temporal derivative is globally integrable or `L²`.
Pointwise momentum identifies the residual exactly with the pressure gradient,
whose compactly-supported weak pairing is already legitimate.

This is therefore the first completely pressure-free weak momentum equation
for the endpoint canonical path, without any unjustified Banach-valued time
differentiability claim.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3PhysicalTailEndpointCanonicalWeakProjectedMomentum
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PhysicalTailEndpointCanonicalWeakProjectedMomentum :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The full endpoint projected-momentum residual has zero pairing against
every compactly supported smooth divergence-free test vector.

The residual is kept inside one integral so this theorem does not require a
separate global integrability assertion for the pointwise temporal derivative.
-/
theorem h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_weakProjectedMomentum
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
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  let q : ScalarField3 :=
    h3PreterminalTailCanonicalNormalizedRealPressureScalarDefectOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint s

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

  have hResidual
      (i : Fin 3)
      (x : Point3) :
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
        =
      -
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ i x)
        (spatial3.d
          (h3AxisOfFin3 i)
          q
          x) := by
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
      -
      ((φ i x) *
        spatial3.d
          (h3AxisOfFin3 i)
          q
          x)

    rw [hMomentum]
    ring

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
      ∑ i : Fin 3,
        ∫ x : Point3,
          -
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (spatial3.d
              (h3AxisOfFin3 i)
              q
              x)
          ∂volume := by
      apply Finset.sum_congr rfl
      intro i hi
      apply integral_congr_ae
      exact
        Filter.Eventually.of_forall
          (fun x => hResidual i x)
    _ =
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
      simp_rw [integral_neg]
      rw [Finset.sum_neg_distrib]
    _ = 0 := by
      rw [hPressure]
      simp

end

end Euclidean
end Bridge
end PrimeTensor
