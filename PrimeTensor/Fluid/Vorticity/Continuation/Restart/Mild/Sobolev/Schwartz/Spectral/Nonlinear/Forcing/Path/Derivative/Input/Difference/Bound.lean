import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Path.Derivative.Bilinear

/-!
# Bilinear pointwise bounds for derivative input differences

The previous module gives the exact three-term decomposition of a retarded
pointwise derivative-path difference.  To prove continuity, the first two
terms must vanish when the two spectral inputs approach their values at the
base time.

This file packages the quantitative estimate needed for that squeeze.  At any
positive heat lag `τ`, one coordinate derivative of the classical nonlinear
representative satisfies

    ‖D_j K_τ(U,V)(x)‖
      ≤ 2π k_ν(τ) C_force ‖U‖ ‖V‖,

uniformly in `x`.  Applying the same estimate to `U - U₀` and `V - V₀`
produces the two input-difference bounds needed by the retarded continuity
argument.

No time-continuity statement is used here; the frozen-input time-difference
term remains the only analytic term not controlled by bilinearity.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralNonlinearForcingPathDerivativeInputDifferenceBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Fixed positive-lag bilinear pointwise bound for one coordinate derivative
of the classical nonlinear heat representative. -/
theorem norm_h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_le_bilinear
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i j : Fin 3)
    (x : H3FourierPoint3) :
    ‖h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
        ν τ U V i j x‖
      ≤
    (2 * Real.pi) *
      h3NonlinearForcingHeatFirstMomentCoefficient ν τ *
      h3NonlinearForcingL1Coefficient * ‖U‖ * ‖V‖ := by
  have hTargetInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawFinLerayOuterProductDivergenceHeatRepresentative
              ν τ U V i ξ‖)
        (volume : Measure H3FourierPoint3) :=
    (h3RawFinLerayOuterProductDivergenceHeatRepresentative_derivative_integrable
      hν hτ U V i j).norm

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

  have hTwoPi : 0 ≤ 2 * Real.pi := by
    positivity

  have hCoeff :
      0 ≤ h3NonlinearForcingHeatFirstMomentCoefficient ν τ :=
    h3NonlinearForcingHeatFirstMomentCoefficient_nonneg ν τ

  calc
    ‖h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
        ν τ U V i j x‖
        ≤
      ∫ ξ : H3FourierPoint3,
        ‖h3FourierDerivativeSymbol j ξ *
          h3RawFinLerayOuterProductDivergenceHeatRepresentative
            ν τ U V i ξ‖ :=
      norm_h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_le_integral
        hν hτ U V i j x
    _ ≤
      ∫ ξ : H3FourierPoint3,
        (2 * Real.pi) *
          (‖ξ‖ *
            ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
              ν τ U V i ξ‖) := by
        refine integral_mono_ae hTargetInt hMajorantInt ?_
        filter_upwards with ξ
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
    _ =
      (2 * Real.pi) *
        (∫ ξ : H3FourierPoint3,
          ‖ξ‖ *
            ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
              ν τ U V i ξ‖) := by
        rw [integral_const_mul]
    _ ≤
      (2 * Real.pi) *
        (h3NonlinearForcingHeatFirstMomentCoefficient ν τ *
          h3RawFinLerayOuterProductDivergenceL1Mass U V i) := by
        exact
          mul_le_mul_of_nonneg_left
            (h3RawFinLerayOuterProductDivergenceHeatRepresentative_firstMoment_integral_le
              hν hτ U V i)
            hTwoPi
    _ ≤
      (2 * Real.pi) *
        (h3NonlinearForcingHeatFirstMomentCoefficient ν τ *
          (h3NonlinearForcingL1Coefficient * ‖U‖ * ‖V‖)) := by
        exact
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (h3RawFinLerayOuterProductDivergenceL1Mass_le U V i)
              hCoeff)
            hTwoPi
    _ =
      (2 * Real.pi) *
        h3NonlinearForcingHeatFirstMomentCoefficient ν τ *
        h3NonlinearForcingL1Coefficient * ‖U‖ * ‖V‖ := by
      ring

/-- The first input-variation term is controlled linearly by the size of the
first spectral difference. -/
theorem norm_h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_sub_left_le
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U U₀ V : H3SpectralFinVectorState)
    (i j : Fin 3)
    (x : H3FourierPoint3) :
    ‖h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
        ν τ (U - U₀) V i j x‖
      ≤
    (2 * Real.pi) *
      h3NonlinearForcingHeatFirstMomentCoefficient ν τ *
      h3NonlinearForcingL1Coefficient * ‖U - U₀‖ * ‖V‖ := by
  exact
    norm_h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_le_bilinear
      hν hτ (U - U₀) V i j x

/-- The second input-variation term is controlled linearly by the size of the
second spectral difference. -/
theorem norm_h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_sub_right_le
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V V₀ : H3SpectralFinVectorState)
    (i j : Fin 3)
    (x : H3FourierPoint3) :
    ‖h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
        ν τ U (V - V₀) i j x‖
      ≤
    (2 * Real.pi) *
      h3NonlinearForcingHeatFirstMomentCoefficient ν τ *
      h3NonlinearForcingL1Coefficient * ‖U‖ * ‖V - V₀‖ := by
  exact
    norm_h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_le_bilinear
      hν hτ U (V - V₀) i j x

end

end Euclidean
end Bridge
end PrimeTensor
