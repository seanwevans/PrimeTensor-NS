import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Path.First.Moment.Bound
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Heat.Divergence

/-!
# Pathwise derivative-L¹ bound for the nonlinear Duhamel kernel

`SchwartzSpectralNonlinearForcingPathFirstMomentBound` controls the first
Fourier moment of the positive-lag retarded nonlinear forcing by an integrable
`(t-s)⁻¹/²` scalar majorant.

A concrete spatial coordinate derivative corresponds to multiplication by
`h3FourierDerivativeSymbol j`.  Its norm is bounded by the radial derivative
magnitude `2π ‖ξ‖`.  Therefore the already-proved first-moment estimate can be
spent directly on one coordinate derivative:

    ∫ ‖D_j(ξ) K_{t-s}(ξ)‖ dξ
      ≤ 2π · firstMomentMajorant(s).

This file packages that derivative amplitude in Fourier `L¹`, proves the
pathwise bound, and records the resulting integrable time majorant.  The next
layer can use these statements when interchanging one spatial derivative with
the near-endpoint Duhamel time integral.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory
open scoped Interval

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralNonlinearForcingPathDerivativeL1Bound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- One Fourier coordinate derivative of the positive-lag raw nonlinear
forcing is genuinely integrable. -/
theorem h3RawFinLerayOuterProductDivergenceHeatRepresentative_derivative_integrable
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i j : Fin 3) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierDerivativeSymbol j ξ *
          h3RawFinLerayOuterProductDivergenceHeatRepresentative
            ν τ U V i ξ)
      (volume : Measure H3FourierPoint3) := by
  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierDerivativeSymbol j ξ *
            h3RawFinLerayOuterProductDivergenceHeatRepresentative
              ν τ U V i ξ)
        (volume : Measure H3FourierPoint3) := by
    exact
      (h3FourierDerivativeSymbol_continuous j).aestronglyMeasurable.mul
        (h3RawFinLerayOuterProductDivergenceHeatRepresentative_aestronglyMeasurable
          ν τ U V i)

  have hMomentInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ *
            ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
              ν τ U V i ξ‖)
        (volume : Measure H3FourierPoint3) := by
    simpa using
      (h3RawFinLerayOuterProductDivergenceHeatRepresentative_moment_integrable
        hν hτ U V i 1 (by norm_num))

  have hMajorantInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (2 * Real.pi) *
            (‖ξ‖ *
              ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
                ν τ U V i ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hMomentInt.const_mul (2 * Real.pi)

  refine Integrable.mono' hMajorantInt hTargetMeas ?_
  filter_upwards with ξ

  have hMajorantNonneg :
      0 ≤
        (2 * Real.pi) *
          (‖ξ‖ *
            ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
              ν τ U V i ξ‖) := by
    positivity

  have hBound :
      ‖h3FourierDerivativeSymbol j ξ *
          h3RawFinLerayOuterProductDivergenceHeatRepresentative
            ν τ U V i ξ‖
        ≤
      (2 * Real.pi) *
        (‖ξ‖ *
          ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
            ν τ U V i ξ‖) := by
    calc
      ‖h3FourierDerivativeSymbol j ξ *
          h3RawFinLerayOuterProductDivergenceHeatRepresentative
            ν τ U V i ξ‖
          =
        ‖h3FourierDerivativeSymbol j ξ‖ *
          ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
            ν τ U V i ξ‖ := by
              rw [norm_mul]
      _ ≤
        h3FourierGradientMagnitude ξ *
          ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
            ν τ U V i ξ‖ :=
          mul_le_mul_of_nonneg_right
            (norm_h3FourierDerivativeSymbol_le_gradientMagnitude j ξ)
            (norm_nonneg _)
      _ =
        (2 * Real.pi) *
          (‖ξ‖ *
            ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
              ν τ U V i ξ‖) := by
          unfold h3FourierGradientMagnitude
          ring

  exact hBound

/-- Scalar time majorant for one concrete coordinate derivative of the
retarded nonlinear heat kernel. -/
noncomputable def h3NonlinearForcingHeatFirstDerivativePathMajorant
    (ν t MU MV s : ℝ) : ℝ :=
  (2 * Real.pi) *
    h3NonlinearForcingHeatFirstMomentPathMajorant ν t MU MV s

/-- The one-derivative path majorant is interval integrable. -/
theorem h3NonlinearForcingHeatFirstDerivativePathMajorant_intervalIntegrable
    {ν t MU MV : ℝ}
    (hν : 0 < ν)
    (ht : 0 ≤ t) :
    IntervalIntegrable
      (h3NonlinearForcingHeatFirstDerivativePathMajorant ν t MU MV)
      volume
      0
      t := by
  change
    IntervalIntegrable
      (fun s : ℝ =>
        (2 * Real.pi) *
          h3NonlinearForcingHeatFirstMomentPathMajorant ν t MU MV s)
      volume
      0
      t
  exact
    (h3NonlinearForcingHeatFirstMomentPathMajorant_intervalIntegrable
      (MU := MU) (MV := MV) hν ht).const_mul (2 * Real.pi)

/-- Exact integral of the one-derivative path majorant. -/
theorem h3NonlinearForcingHeatFirstDerivativePathMajorant_integral
    {ν t MU MV : ℝ}
    (hν : 0 < ν)
    (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t,
        h3NonlinearForcingHeatFirstDerivativePathMajorant ν t MU MV s)
      =
    (2 * Real.pi) *
      (2 * (Real.sqrt (ν / 3))⁻¹ * Real.sqrt t *
        h3NonlinearForcingL1Coefficient * MU * MV) := by
  unfold h3NonlinearForcingHeatFirstDerivativePathMajorant
  rw [intervalIntegral.integral_const_mul]
  rw [h3NonlinearForcingHeatFirstMomentPathMajorant_integral hν ht]

/-- Under uniform bounds on the two input paths, the Fourier `L¹` mass of one
coordinate derivative of the retarded nonlinear heat kernel is controlled by
the integrable derivative majorant. -/
theorem h3RawFinLerayOuterProductDivergenceHeatRepresentative_derivative_norm_integral_le_pathMajorant
    {ν t MU MV s : ℝ}
    (hν : 0 < ν)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hs : s ∈ Set.Ioo (0 : ℝ) t)
    (hU : ‖U s‖ ≤ MU)
    (hV : ‖V s‖ ≤ MV)
    (i j : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        ‖h3FourierDerivativeSymbol j ξ *
          h3RawFinLerayOuterProductDivergenceHeatRepresentative
            ν (t - s) (U s) (V s) i ξ‖)
      ≤
    h3NonlinearForcingHeatFirstDerivativePathMajorant ν t MU MV s := by
  have hτ : 0 < t - s := sub_pos.mpr hs.2

  have hTargetInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawFinLerayOuterProductDivergenceHeatRepresentative
              ν (t - s) (U s) (V s) i ξ‖)
        (volume : Measure H3FourierPoint3) :=
    (h3RawFinLerayOuterProductDivergenceHeatRepresentative_derivative_integrable
      hν hτ (U s) (V s) i j).norm

  have hMomentInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ *
            ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
              ν (t - s) (U s) (V s) i ξ‖)
        (volume : Measure H3FourierPoint3) := by
    simpa using
      (h3RawFinLerayOuterProductDivergenceHeatRepresentative_moment_integrable
        hν hτ (U s) (V s) i 1 (by norm_num))

  have hMajorantInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (2 * Real.pi) *
            (‖ξ‖ *
              ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
                ν (t - s) (U s) (V s) i ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hMomentInt.const_mul (2 * Real.pi)

  calc
    (∫ ξ : H3FourierPoint3,
        ‖h3FourierDerivativeSymbol j ξ *
          h3RawFinLerayOuterProductDivergenceHeatRepresentative
            ν (t - s) (U s) (V s) i ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        (2 * Real.pi) *
          (‖ξ‖ *
            ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
              ν (t - s) (U s) (V s) i ξ‖) := by
        refine integral_mono_ae hTargetInt hMajorantInt ?_
        filter_upwards with ξ
        calc
          ‖h3FourierDerivativeSymbol j ξ *
              h3RawFinLerayOuterProductDivergenceHeatRepresentative
                ν (t - s) (U s) (V s) i ξ‖
              =
            ‖h3FourierDerivativeSymbol j ξ‖ *
              ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
                ν (t - s) (U s) (V s) i ξ‖ := by
                  rw [norm_mul]
          _ ≤
            h3FourierGradientMagnitude ξ *
              ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
                ν (t - s) (U s) (V s) i ξ‖ :=
              mul_le_mul_of_nonneg_right
                (norm_h3FourierDerivativeSymbol_le_gradientMagnitude j ξ)
                (norm_nonneg _)
          _ =
            (2 * Real.pi) *
              (‖ξ‖ *
                ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
                  ν (t - s) (U s) (V s) i ξ‖) := by
              unfold h3FourierGradientMagnitude
              ring
    _ =
      (2 * Real.pi) *
        (∫ ξ : H3FourierPoint3,
          ‖ξ‖ *
            ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
              ν (t - s) (U s) (V s) i ξ‖) := by
        rw [integral_const_mul]
    _ ≤
      (2 * Real.pi) *
        h3NonlinearForcingHeatFirstMomentPathMajorant ν t MU MV s := by
        exact
          mul_le_mul_of_nonneg_left
            (h3RawFinLerayOuterProductDivergenceHeatRepresentative_firstMoment_le_pathMajorant
              hν hMU hMV U V hs hU hV i)
            (by positivity)
    _ =
      h3NonlinearForcingHeatFirstDerivativePathMajorant ν t MU MV s := by
        rfl

end

end Euclidean
end Bridge
end PrimeTensor
