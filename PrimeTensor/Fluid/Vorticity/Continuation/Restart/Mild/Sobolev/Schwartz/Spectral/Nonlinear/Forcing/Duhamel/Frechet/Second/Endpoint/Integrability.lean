import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Real.C1
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Moment.Smoothing
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Path.First.Moment.Bound

/-!
# Endpoint cancellation for the second spatial Duhamel derivative

The first full-space Duhamel derivative is time-integrable because one extra
Fourier moment costs only the retarded heat singularity

    (t - s)^(-1/2).

A second spatial derivative naively costs a second Fourier moment and hence a
non-integrable `(t - s)^(-1)` endpoint singularity.  The standard parabolic
repair is endpoint cancellation: subtract the nonlinear forcing at the target
time.  If the unheated forcing has a `1/2`-Hölder `L¹` modulus,

    ‖N(s) - N(t)‖_{L¹_ξ} ≤ K sqrt (t - s),

then the second heat moment gains exactly the missing square root and is again
controlled by an integrable `(t - s)^(-1/2)` kernel.

This file isolates that mechanism without assuming the desired time modulus
for the selected path.  It proves:

* the precise raw-forcing endpoint half-Hölder predicate;
* a fixed-source second-Fourier-moment bound for the cancelled heat kernel;
* an integrable scalar cancellation majorant; and
* its exact time integral.

Thus the next classicalization rung has one sharply stated analytic target:
prove the endpoint half-Hölder predicate for the Banach-selected mild path.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped Interval ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralNonlinearForcingSecondEndpoint
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- `L¹` mass of the difference between the unheated nonlinear forcing at
source time `s` and at the terminal time `t`. -/
noncomputable def h3RawFinLerayOuterProductDivergenceEndpointDifferenceL1Mass
    (U V : ℝ → H3SpectralFinVectorState)
    (t s : ℝ)
    (i : Fin 3) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    ‖h3RawFinLerayOuterProductDivergence (U s) (V s) i ξ -
      h3RawFinLerayOuterProductDivergence (U t) (V t) i ξ‖

/-- The exact endpoint time regularity needed to spend a second Fourier
moment in the Duhamel tail. -/
def H3NonlinearForcingEndpointHalfHolderL1
    (U V : ℝ → H3SpectralFinVectorState)
    (t K : ℝ)
    (i : Fin 3) : Prop :=
  ∀ s ∈ Set.Ioo (0 : ℝ) t,
    h3RawFinLerayOuterProductDivergenceEndpointDifferenceL1Mass
        U V t s i
      ≤ K * Real.sqrt (t - s)

/-- Scalar majorant left after the second heat moment is paired with the
endpoint `1/2`-Hölder gain.

It is one extra factor `(sqrt (ν/3))⁻¹` times the already-integrable
first-moment time kernel. -/
noncomputable def h3NonlinearForcingHeatSecondDerivativeCancellationMajorant
    (ν t K s : ℝ) : ℝ :=
  (Real.sqrt (ν / 3))⁻¹ *
    h3NonlinearForcingHeatFirstMomentTimeMajorant ν t K s

/-- The endpoint-cancellation majorant is interval integrable. -/
theorem h3NonlinearForcingHeatSecondDerivativeCancellationMajorant_intervalIntegrable
    {ν t K : ℝ}
    (hν : 0 < ν)
    (ht : 0 ≤ t) :
    IntervalIntegrable
      (h3NonlinearForcingHeatSecondDerivativeCancellationMajorant ν t K)
      volume
      0
      t := by
  unfold h3NonlinearForcingHeatSecondDerivativeCancellationMajorant
  exact
    (h3NonlinearForcingHeatFirstMomentTimeMajorant_intervalIntegrable
      (M := K) hν ht).const_mul (Real.sqrt (ν / 3))⁻¹

/-- Exact integral of the endpoint-cancellation majorant. -/
theorem h3NonlinearForcingHeatSecondDerivativeCancellationMajorant_integral
    {ν t K : ℝ}
    (hν : 0 < ν)
    (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t,
        h3NonlinearForcingHeatSecondDerivativeCancellationMajorant
          ν t K s)
      =
    2 * ((Real.sqrt (ν / 3))⁻¹) ^ 2 * Real.sqrt t * K := by
  unfold h3NonlinearForcingHeatSecondDerivativeCancellationMajorant
  rw [intervalIntegral.integral_const_mul]
  rw [
    h3NonlinearForcingHeatFirstMomentTimeMajorant_integral
      (M := K) hν ht
  ]
  ring

/-- On a strict retarded time slice, one heat coefficient times
`sqrt (t-s)` cancels exactly to the viscosity-only coefficient. -/
theorem h3NonlinearForcingHeatFirstMomentRetardedCoefficient_mul_sqrt_eq
    {ν t s : ℝ}
    (hν : 0 < ν)
    (hs : s ∈ Set.Ioo (0 : ℝ) t) :
    h3NonlinearForcingHeatFirstMomentRetardedCoefficient ν t s *
        Real.sqrt (t - s)
      =
    (Real.sqrt (ν / 3))⁻¹ := by
  have hν3 : 0 < ν / 3 := by positivity
  have hτ : 0 < t - s := sub_pos.mpr hs.2
  have hsν : Real.sqrt (ν / 3) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 hν3)
  have hsτ : Real.sqrt (t - s) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 hτ)

  unfold h3NonlinearForcingHeatFirstMomentRetardedCoefficient
  unfold h3NonlinearForcingHeatFirstMomentCoefficient
  rw [show ν * ((t - s) / 3) = (ν / 3) * (t - s) by ring]
  rw [Real.sqrt_mul hν3.le]
  field_simp

/-- The fixed-lag second Fourier moment of the endpoint-cancelled nonlinear
forcing is bounded by the integrable scalar cancellation majorant. -/
theorem h3RawFinLerayOuterProductDivergenceHeat_endpointDifference_secondMoment_le
    {ν t K s : ℝ}
    (hν : 0 < ν)
    (U V : ℝ → H3SpectralFinVectorState)
    (i : Fin 3)
    (hs : s ∈ Set.Ioo (0 : ℝ) t)
    (hHolder : H3NonlinearForcingEndpointHalfHolderL1 U V t K i) :
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3HeatFourierSymbol ν (t - s) ξ *
            (h3RawFinLerayOuterProductDivergence (U s) (V s) i ξ -
              h3RawFinLerayOuterProductDivergence (U t) (V t) i ξ)‖)
      ≤
    h3NonlinearForcingHeatSecondDerivativeCancellationMajorant
      ν t K s := by
  have hτ : 0 < t - s := sub_pos.mpr hs.2

  let C : ℝ := (Real.sqrt (ν * ((t - s) / 3)))⁻¹
  let D : H3FourierPoint3 → ℂ :=
    fun ξ =>
      h3RawFinLerayOuterProductDivergence (U s) (V s) i ξ -
        h3RawFinLerayOuterProductDivergence (U t) (V t) i ξ

  have hDs :
      Integrable
        (h3RawFinLerayOuterProductDivergence (U s) (V s) i)
        (volume : Measure H3FourierPoint3) :=
    h3RawFinLerayOuterProductDivergence_integrable (U s) (V s) i

  have hDt :
      Integrable
        (h3RawFinLerayOuterProductDivergence (U t) (V t) i)
        (volume : Measure H3FourierPoint3) :=
    h3RawFinLerayOuterProductDivergence_integrable (U t) (V t) i

  have hD : Integrable D (volume : Measure H3FourierPoint3) := by
    dsimp only [D]
    exact hDs.sub hDt

  have hMajorantInt :
      Integrable
        (fun ξ : H3FourierPoint3 => C ^ 2 * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hD.norm.const_mul (C ^ 2)

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν (t - s) ξ * D ξ‖)
        (volume : Measure H3FourierPoint3) := by
    exact
      ((continuous_norm.pow 2).aestronglyMeasurable).mul
        ((continuous_h3HeatFourierSymbol ν (t - s)).aestronglyMeasurable.mul
          hD.aestronglyMeasurable).norm

  have hTargetInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν (t - s) ξ * D ξ‖)
        (volume : Measure H3FourierPoint3) := by
    refine hMajorantInt.mono' hTargetMeas ?_
    filter_upwards with ξ
    have hMoment :=
      h3HeatFourierMomentMultiplier_le_three
        hν hτ 2 (by norm_num) ξ
    have hNonneg :
        0 ≤
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν (t - s) ξ * D ξ‖ := by
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hNonneg]
    rw [norm_mul]
    calc
      ‖ξ‖ ^ 2 *
          (‖h3HeatFourierSymbol ν (t - s) ξ‖ * ‖D ξ‖)
          =
        (‖ξ‖ ^ 2 *
          ‖h3HeatFourierSymbol ν (t - s) ξ‖) * ‖D ξ‖ := by
            ring
      _ ≤ C ^ 2 * ‖D ξ‖ := by
        dsimp only [C]
        exact
          mul_le_mul_of_nonneg_right
            hMoment
            (norm_nonneg _)

  have hIntegralBound :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν (t - s) ξ * D ξ‖)
        ≤
      C ^ 2 *
        (∫ ξ : H3FourierPoint3, ‖D ξ‖) := by
    calc
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν (t - s) ξ * D ξ‖)
          ≤
        ∫ ξ : H3FourierPoint3, C ^ 2 * ‖D ξ‖ := by
          refine integral_mono_ae hTargetInt hMajorantInt ?_
          filter_upwards with ξ
          have hMoment :=
            h3HeatFourierMomentMultiplier_le_three
              hν hτ 2 (by norm_num) ξ
          rw [norm_mul]
          calc
            ‖ξ‖ ^ 2 *
                (‖h3HeatFourierSymbol ν (t - s) ξ‖ * ‖D ξ‖)
                =
              (‖ξ‖ ^ 2 *
                ‖h3HeatFourierSymbol ν (t - s) ξ‖) * ‖D ξ‖ := by
                  ring
            _ ≤ C ^ 2 * ‖D ξ‖ := by
              dsimp only [C]
              exact
                mul_le_mul_of_nonneg_right
                  hMoment
                  (norm_nonneg _)
      _ =
        C ^ 2 *
          (∫ ξ : H3FourierPoint3, ‖D ξ‖) := by
            rw [integral_const_mul]

  have hHolderAt :
      (∫ ξ : H3FourierPoint3, ‖D ξ‖)
        ≤ K * Real.sqrt (t - s) := by
    simpa only [
      D,
      h3RawFinLerayOuterProductDivergenceEndpointDifferenceL1Mass
    ] using hHolder s hs

  have hCoeff :
      C * Real.sqrt (t - s)
        =
      (Real.sqrt (ν / 3))⁻¹ := by
    dsimp only [C]
    simpa only [
      h3NonlinearForcingHeatFirstMomentRetardedCoefficient,
      h3NonlinearForcingHeatFirstMomentCoefficient
    ] using
      (h3NonlinearForcingHeatFirstMomentRetardedCoefficient_mul_sqrt_eq
        hν hs)

  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3HeatFourierSymbol ν (t - s) ξ *
            (h3RawFinLerayOuterProductDivergence (U s) (V s) i ξ -
              h3RawFinLerayOuterProductDivergence (U t) (V t) i ξ)‖)
        =
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3HeatFourierSymbol ν (t - s) ξ * D ξ‖ := by
            rfl
    _ ≤
      C ^ 2 * (∫ ξ : H3FourierPoint3, ‖D ξ‖) :=
        hIntegralBound
    _ ≤
      C ^ 2 * (K * Real.sqrt (t - s)) := by
        exact
          mul_le_mul_of_nonneg_left
            hHolderAt
            (sq_nonneg C)
    _ =
      (Real.sqrt (ν / 3))⁻¹ *
        (C * K) := by
      calc
        C ^ 2 * (K * Real.sqrt (t - s))
            =
          (C * Real.sqrt (t - s)) * (C * K) := by
              ring
        _ =
          (Real.sqrt (ν / 3))⁻¹ * (C * K) := by
              rw [hCoeff]
    _ =
      h3NonlinearForcingHeatSecondDerivativeCancellationMajorant
        ν t K s := by
      unfold h3NonlinearForcingHeatSecondDerivativeCancellationMajorant
      unfold h3NonlinearForcingHeatFirstMomentTimeMajorant
      unfold h3NonlinearForcingHeatFirstMomentRetardedCoefficient
      unfold h3NonlinearForcingHeatFirstMomentCoefficient
      dsimp only [C]

end

end Euclidean
end Bridge
end PrimeTensor
