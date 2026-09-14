import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.TemporalFubini

/-!
# Zeroth-order endpoint continuity: summed endpoint-independent old weak FTC

`TemporalFubini` proved the coordinatewise old-branch compact-test FTC once the
endpoint-independent temporal derivative is product integrable.

This file performs the finite three-coordinate sum using the same restricted
open-interval integrability pattern already used by the endpoint weak-Fubini
branch.

The result is the full compact-test velocity increment identity

    sum_i ∫ phi_i (u_i(t+q) - u_i(t))
      =
    ∫_0^q sum_i ∫ phi_i d_t u_i(t+r),

with the measurable continuous-map temporal extension on the right.

No endpoint L2 continuity is used.  The pressure-defect mass frontier remains
only as a sufficient hypothesis for the product-integrability input.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityZeroOldTemporalWeakFTC
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3UnitViscosityZeroOldTemporalWeakFTC :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Product-space integrability gives the complete three-coordinate old weak
FTC identity. -/
theorem h3PreterminalLoggedVelocity_weakPairingDifference_eq_intervalIntegral_of_productIntegrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector)
    (hq : q ∈ Set.Icc (0 : ℝ) tau)
    (hProd :
      H3PreterminalLoggedVelocityTemporalProductIntegrableTo
        hNS t q φ) :
    (∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (loggedVelocityComponent
              u (t + q) (h3AxisOfFin3 i) x
            -
          loggedVelocityComponent
              u t (h3AxisOfFin3 i) x)
        ∂volume)
      =
    ∫ r in (0 : ℝ)..q,
      ∑ i : Fin 3,
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension
              hNS i (t + r) x)
          ∂volume := by
  let g : Fin 3 → ℝ → ℝ :=
    fun i r =>
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension
            hNS i (t + r) x)
        ∂volume

  have hEach
      (i : Fin 3) :
      (∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (loggedVelocityComponent
              u (t + q) (h3AxisOfFin3 i) x
            -
          loggedVelocityComponent
              u t (h3AxisOfFin3 i) x)
        ∂volume)
        =
      ∫ r in (0 : ℝ)..q,
        g i r := by
    dsimp only [g]
    exact
      h3PreterminalLoggedVelocityCoordinate_pairingDifference_eq_intervalIntegral_of_productIntegrable
        hNS ht hEnd hTail φ hq hProd i

  have hOuter
      (i : Fin 3) :
      Integrable
        (g i)
        ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) q)) := by
    let f : ℝ → Point3 → ℝ :=
      fun r x =>
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension
            hNS i (t + r) x)

    have hInt :
        Integrable
          (Function.uncurry f)
          (((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) q)).prod
            (volume : Measure Point3)) := by
      dsimp only [Function.uncurry, f]
      exact hProd i

    have h := hInt.integral_prod_left

    change
      Integrable
        (fun r : ℝ =>
          ∫ x : Point3,
            Function.uncurry f (r, x)
            ∂volume)
        ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) q))

    exact h

  calc
    (∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (loggedVelocityComponent
              u (t + q) (h3AxisOfFin3 i) x
            -
          loggedVelocityComponent
              u t (h3AxisOfFin3 i) x)
        ∂volume)
        =
      ∑ i : Fin 3,
        ∫ r in (0 : ℝ)..q,
          g i r := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hEach i
    _ =
      ∑ i : Fin 3,
        ∫ r in Set.Ioo (0 : ℝ) q,
          g i r := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [intervalIntegral.integral_of_le hq.1]
            rw [← restrict_Ioo_eq_restrict_Ioc]
    _ =
      ∫ r in Set.Ioo (0 : ℝ) q,
        ∑ i : Fin 3,
          g i r := by
            rw [
              integral_finsetSum
                (Finset.univ : Finset (Fin 3))
                (fun i _ => hOuter i)
            ]
    _ =
      ∫ r in (0 : ℝ)..q,
        ∑ i : Fin 3,
          g i r := by
            symm
            rw [intervalIntegral.integral_of_le hq.1]
            rw [← restrict_Ioo_eq_restrict_Ioc]
    _ =
      ∫ r in (0 : ℝ)..q,
        ∑ i : Fin 3,
          ∫ x : Point3,
            (ContinuousLinearMap.lsmul ℝ ℝ)
              (φ i x)
              (h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension
                hNS i (t + r) x)
            ∂volume := by
              rfl

/-- The pressure-defect mass frontier therefore closes the full three-coordinate
old weak FTC identity on every shortened elapsed interval. -/
theorem h3PreterminalLoggedVelocity_weakPairingDifference_eq_intervalIntegral_of_pressureDefect
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector)
    (hq : q ∈ Set.Icc (0 : ℝ) tau)
    (hPressure :
      H3PreterminalTailCanonicalZeroPressureGradientDefectSpatialNormMassUniformlyBoundedOnElapsed
        hNS ht hEnd hTail φ) :
    (∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (loggedVelocityComponent
              u (t + q) (h3AxisOfFin3 i) x
            -
          loggedVelocityComponent
              u t (h3AxisOfFin3 i) x)
        ∂volume)
      =
    ∫ r in (0 : ℝ)..q,
      ∑ i : Fin 3,
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension
              hNS i (t + r) x)
          ∂volume := by
  apply
    h3PreterminalLoggedVelocity_weakPairingDifference_eq_intervalIntegral_of_productIntegrable
      hNS ht hEnd hTail φ hq

  exact
    H3PreterminalLoggedVelocityTemporalProductIntegrableTo_of_pressureDefect
      hNS ht hEnd hE hTail φ
      hq.1 hq.2 hPressure

end

end Euclidean
end Bridge
end PrimeTensor
