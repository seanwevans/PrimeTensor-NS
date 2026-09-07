import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Weak.Pairing.Integral
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Physical L² temporal admissibility: prove weak temporal Fubini from product integrability

`TemporalPairingIntegral` isolated the exact remaining interchange:

    Σᵢ ∫ₓ φᵢ(x) [∫₀^q ∂ₜWᵢ(r,x) dr] dx
      =
    ∫₀^q Σᵢ ∫ₓ φᵢ(x) ∂ₜWᵢ(r,x) dx.

The present file states the minimal analytic hypothesis needed by Mathlib's
Fubini theorem: coordinatewise integrability of the compactly tested temporal
derivative on the product measure

    (volume restricted to (0,q)) × volume.

This is strictly more targeted than the earlier pointwise spatial-majorant
frontier.  No uniform-in-space bound is required.

Under this product-integrability hypothesis we:

1. apply `integral_integral_swap` coordinatewise;
2. convert restricted open-interval time integrals back to interval integrals;
3. commute the finite coordinate sum through the time integral; and
4. discharge `H3PreterminalTailCanonicalWeakTemporalFubiniTo`.

Combining with `TemporalPairingIntegral` gives the full weak projected evolution
identity on every shortened interval `[0,q]`.

This file does not claim that the current separated notion of preterminal
classical regularity implies product integrability.  That is now the sole
regularity-design question left by this route.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2TemporalEndpointTemporalFubini
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PhysicalL2TemporalEndpointTemporalFubini :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Minimal coordinatewise spacetime integrability needed for the endpoint weak
temporal Fubini step at one target `q`. -/
def H3PreterminalTailCanonicalWeakTemporalProductIntegrableTo
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (φ : H3WeakTestVector) : Prop :=
  ∀ i : Fin 3,
    Integrable
      (fun z : ℝ × Point3 =>
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i z.2)
          (temporal.d
            (fun s : ℝ =>
              (h3SpectralRealVelocityOfPath
                (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
                  hNS ht htau.le hEnd hE hTail hEndpoint)
                s z.2).component
                  (h3AxisOfFin3 i))
            z.1))
      (((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) q)).prod
        (volume : Measure Point3))

/-- One coordinate of the compactly tested temporal primitive may be swapped
through space and time whenever its product-space integrand is integrable. -/
theorem h3PreterminalTailCanonicalWeakTemporalCoordinate_fubini_to_of_productIntegrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
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
    (hq : q ∈ Set.Icc (0 : ℝ) tau)
    (hProd :
      H3PreterminalTailCanonicalWeakTemporalProductIntegrableTo
        hNS ht htau hEnd hE hTail hEndpoint
        (q := q) φ)
    (i : Fin 3) :
    (∫ x : Point3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ i x)
        (∫ r in (0 : ℝ)..q,
          temporal.d
            (fun s : ℝ =>
              (h3SpectralRealVelocityOfPath
                (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
                  hNS ht htau.le hEnd hE hTail hEndpoint)
                s x).component
                  (h3AxisOfFin3 i))
            r)
      ∂volume)
      =
    ∫ r in (0 : ℝ)..q,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (temporal.d
            (fun s : ℝ =>
              (h3SpectralRealVelocityOfPath
                (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
                  hNS ht htau.le hEnd hE hTail hEndpoint)
                s x).component
                  (h3AxisOfFin3 i))
            r)
        ∂volume := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  let f : ℝ → Point3 → ℝ :=
    fun r x =>
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ i x)
        (temporal.d
          (fun s : ℝ =>
            (h3SpectralRealVelocityOfPath W s x).component
              (h3AxisOfFin3 i))
          r)

  have hInt :
      Integrable
        (Function.uncurry f)
        (((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) q)).prod
          (volume : Measure Point3)) := by
    dsimp only [Function.uncurry, f, W]
    exact hProd i

  have hSwap :=
    integral_integral_swap
      (μ := (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) q))
      (ν := (volume : Measure Point3))
      (f := f)
      hInt

  have hSwapExpanded :
      (∫ r in Set.Ioo (0 : ℝ) q,
        ∫ x : Point3,
          f r x
          ∂volume)
        =
      ∫ x : Point3,
        ∫ r in Set.Ioo (0 : ℝ) q,
          f r x
        ∂volume := by
    simpa only [f] using hSwap

  have hLeft :
      (∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (∫ r in (0 : ℝ)..q,
            temporal.d
              (fun s : ℝ =>
                (h3SpectralRealVelocityOfPath W s x).component
                  (h3AxisOfFin3 i))
              r)
        ∂volume)
        =
      ∫ x : Point3,
        ∫ r in Set.Ioo (0 : ℝ) q,
          f r x
        ∂volume := by
    apply integral_congr_ae
    filter_upwards with x
    change
      (φ i x) *
          (∫ r in (0 : ℝ)..q,
            temporal.d
              (fun s : ℝ =>
                (h3SpectralRealVelocityOfPath W s x).component
                  (h3AxisOfFin3 i))
              r)
        =
      ∫ r in Set.Ioo (0 : ℝ) q,
        (φ i x) *
          temporal.d
            (fun s : ℝ =>
              (h3SpectralRealVelocityOfPath W s x).component
                (h3AxisOfFin3 i))
            r

    rw [intervalIntegral.integral_of_le hq.1]
    rw [← restrict_Ioo_eq_restrict_Ioc]
    rw [← integral_const_mul]

  have hRight :
      (∫ r in (0 : ℝ)..q,
        ∫ x : Point3,
          f r x
          ∂volume)
        =
      ∫ r in Set.Ioo (0 : ℝ) q,
        ∫ x : Point3,
          f r x
          ∂volume := by
    rw [intervalIntegral.integral_of_le hq.1]
    rw [← restrict_Ioo_eq_restrict_Ioc]

  change
    (∫ x : Point3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ i x)
        (∫ r in (0 : ℝ)..q,
          temporal.d
            (fun s : ℝ =>
              (h3SpectralRealVelocityOfPath W s x).component
                (h3AxisOfFin3 i))
            r)
      ∂volume)
      =
    ∫ r in (0 : ℝ)..q,
      ∫ x : Point3,
        f r x
        ∂volume

  calc
    (∫ x : Point3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ i x)
        (∫ r in (0 : ℝ)..q,
          temporal.d
            (fun s : ℝ =>
              (h3SpectralRealVelocityOfPath W s x).component
                (h3AxisOfFin3 i))
            r)
      ∂volume)
        =
      ∫ x : Point3,
        ∫ r in Set.Ioo (0 : ℝ) q,
          f r x
        ∂volume :=
      hLeft
    _ =
      ∫ r in Set.Ioo (0 : ℝ) q,
        ∫ x : Point3,
          f r x
          ∂volume :=
      hSwapExpanded.symm
    _ =
      ∫ r in (0 : ℝ)..q,
        ∫ x : Point3,
          f r x
          ∂volume :=
      hRight.symm

/-- Product integrability discharges the exact weak temporal Fubini equality
isolated in `TemporalPairingIntegral`. -/
theorem H3PreterminalTailCanonicalWeakTemporalFubiniTo_of_productIntegrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
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
    (hq : q ∈ Set.Icc (0 : ℝ) tau)
    (hProd :
      H3PreterminalTailCanonicalWeakTemporalProductIntegrableTo
        hNS ht htau hEnd hE hTail hEndpoint
        (q := q) φ) :
    H3PreterminalTailCanonicalWeakTemporalFubiniTo
      hNS ht htau hEnd hE hTail hEndpoint
      (q := q) φ := by
  unfold H3PreterminalTailCanonicalWeakTemporalFubiniTo

  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  let g : Fin 3 → ℝ → ℝ :=
    fun i r =>
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (temporal.d
            (fun s : ℝ =>
              (h3SpectralRealVelocityOfPath W s x).component
                (h3AxisOfFin3 i))
            r)
        ∂volume

  have hEach
      (i : Fin 3) :
      (∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (∫ r in (0 : ℝ)..q,
            temporal.d
              (fun s : ℝ =>
                (h3SpectralRealVelocityOfPath W s x).component
                  (h3AxisOfFin3 i))
              r)
        ∂volume)
        =
      ∫ r in (0 : ℝ)..q,
        g i r := by
    dsimp only [g, W]
    exact
      h3PreterminalTailCanonicalWeakTemporalCoordinate_fubini_to_of_productIntegrable
        hNS ht htau hEnd hE hTail hEndpoint
        φ hq hProd i

  have hOuter
      (i : Fin 3) :
      Integrable
        (g i)
        ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) q)) := by
    let f : ℝ → Point3 → ℝ :=
      fun r x =>
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (temporal.d
            (fun s : ℝ =>
              (h3SpectralRealVelocityOfPath W s x).component
                (h3AxisOfFin3 i))
            r)

    have hInt :
        Integrable
          (Function.uncurry f)
          (((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) q)).prod
            (volume : Measure Point3)) := by
      dsimp only [Function.uncurry, f, W]
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
          (∫ r in (0 : ℝ)..q,
            temporal.d
              (fun s : ℝ =>
                (h3SpectralRealVelocityOfPath W s x).component
                  (h3AxisOfFin3 i))
              r)
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
              (temporal.d
                (fun s : ℝ =>
                  (h3SpectralRealVelocityOfPath W s x).component
                    (h3AxisOfFin3 i))
                r)
            ∂volume := by
              rfl

/-- Product-space integrability is sufficient for the full intermediate weak
projected evolution identity, with no pointwise spatial-majorant hypothesis. -/
theorem h3PreterminalTailCanonicalWeakVelocityPairingDifference_eq_intervalIntegral_to_of_productIntegrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
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
    (hq : q ∈ Set.Icc (0 : ℝ) tau)
    (hProd :
      H3PreterminalTailCanonicalWeakTemporalProductIntegrableTo
        hNS ht htau hEnd hE hTail hEndpoint
        (q := q) φ) :
    h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
        hNS ht hEnd hTail φ
        ⟨q, hq⟩
      -
    h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
        hNS ht hEnd hTail φ
        ⟨0, ⟨le_rfl, htau.le⟩⟩
      =
    ∫ r in (0 : ℝ)..q,
      h3PreterminalTailCanonicalWeakProjectedRHSPairingReal
        hNS ht htau hEnd hE hTail hEndpoint φ r := by
  apply
    h3PreterminalTailCanonicalWeakVelocityPairingDifference_eq_intervalIntegral_to_of_temporalFubini
      hNS ht htau hEnd hE hTail hEndpoint
      φ hφ hq

  exact
    H3PreterminalTailCanonicalWeakTemporalFubiniTo_of_productIntegrable
      hNS ht htau hEnd hE hTail hEndpoint
      φ hq hProd

end

end Euclidean
end Bridge
end PrimeTensor
