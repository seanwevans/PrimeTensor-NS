import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.ProfileLagVariation

/-!
# Positive-lag continuity of the frozen second-moment forcing profile

For fixed spectral data `U`, consider

    τ ↦ ∫ |ξ|² |H_τ(ξ) N(U,U)(ξ)| dξ.

At a positive lag `τ₀`, choose the fixed earlier lag `a = τ₀ / 2`.
Every nearby `τ > a` factors as an extra contractive heat step applied after
`a`, so the second-moment integrand at `a` dominates the nearby family.
That dominator is Fourier-L¹ by the existing positive-lag moment theorem.

Dominated convergence therefore gives continuity at every strictly positive
heat lag.  This is the frozen-input time-variation term needed for continuity
of the selected second-moment source-time profile.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzQuarterForcingProfileFrozenContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Frozen diagonal nonlinear forcing after a heat lag, measured with two
Fourier moments. -/
noncomputable def h3NonlinearForcingHeatSecondMomentFrozenProfile
    (ν : ℝ)
    (U : H3SpectralFinVectorState)
    (i : Fin 3)
    (τ : ℝ) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    ‖ξ‖ ^ 2 *
      ‖h3HeatFourierSymbol ν τ ξ *
        h3RawFinLerayOuterProductDivergence U U i ξ‖

/-- The frozen second-moment integrand is continuous in the heat lag at every
fixed frequency. -/
theorem continuous_h3NonlinearForcingHeatSecondMomentFrozenKernel_lag
    (ν : ℝ)
    (U : H3SpectralFinVectorState)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    Continuous
      (fun τ : ℝ =>
        ‖ξ‖ ^ 2 *
          ‖h3HeatFourierSymbol ν τ ξ *
            h3RawFinLerayOuterProductDivergence U U i ξ‖) := by
  unfold h3HeatFourierSymbol
  fun_prop

/-- A later heat lag is pointwise dominated by any fixed earlier positive lag. -/
theorem h3NonlinearForcingHeatSecondMomentFrozenKernel_le_of_le
    {ν a τ : ℝ}
    (hν : 0 < ν)
    (ha : 0 < a)
    (haτ : a ≤ τ)
    (U : H3SpectralFinVectorState)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    ‖ξ‖ ^ 2 *
        ‖h3HeatFourierSymbol ν τ ξ *
          h3RawFinLerayOuterProductDivergence U U i ξ‖
      ≤
    ‖ξ‖ ^ 2 *
        ‖h3HeatFourierSymbol ν a ξ *
          h3RawFinLerayOuterProductDivergence U U i ξ‖ := by
  have hb : 0 ≤ τ - a := sub_nonneg.mpr haτ
  have hsplit : a + (τ - a) = τ := by ring
  have hheat :
      h3HeatFourierSymbol ν τ ξ
        =
      h3HeatFourierSymbol ν (τ - a) ξ *
        h3HeatFourierSymbol ν a ξ := by
    simpa only [hsplit] using
      (h3HeatFourierSymbol_add ν a (τ - a) ξ)

  have hcontract :
      ‖h3HeatFourierSymbol ν (τ - a) ξ‖ ≤ 1 :=
    norm_h3HeatFourierSymbol_le_one hν.le hb ξ

  rw [hheat]
  simp only [norm_mul]

  have hweight : 0 ≤ ‖ξ‖ ^ 2 := sq_nonneg ‖ξ‖
  have hrest :
      0 ≤
        ‖h3HeatFourierSymbol ν a ξ‖ *
          ‖h3RawFinLerayOuterProductDivergence U U i ξ‖ := by
    positivity

  calc
    ‖ξ‖ ^ 2 *
        (‖h3HeatFourierSymbol ν (τ - a) ξ‖ *
            ‖h3HeatFourierSymbol ν a ξ‖ *
          ‖h3RawFinLerayOuterProductDivergence U U i ξ‖)
        =
      ‖ξ‖ ^ 2 *
        (‖h3HeatFourierSymbol ν (τ - a) ξ‖ *
          (‖h3HeatFourierSymbol ν a ξ‖ *
            ‖h3RawFinLerayOuterProductDivergence U U i ξ‖)) := by
      ring
    _ ≤
      ‖ξ‖ ^ 2 * (1 *
        (‖h3HeatFourierSymbol ν a ξ‖ *
          ‖h3RawFinLerayOuterProductDivergence U U i ξ‖)) := by
      exact
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hcontract hrest)
          hweight
    _ =
      ‖ξ‖ ^ 2 *
        (‖h3HeatFourierSymbol ν a ξ‖ *
          ‖h3RawFinLerayOuterProductDivergence U U i ξ‖) := by
      ring

/-- The frozen second-moment profile is continuous at every strictly positive
heat lag. -/
theorem continuousAt_h3NonlinearForcingHeatSecondMomentFrozenProfile_lag
    {ν τ₀ : ℝ}
    (hν : 0 < ν)
    (hτ₀ : 0 < τ₀)
    (U : H3SpectralFinVectorState)
    (i : Fin 3) :
    ContinuousAt
      (h3NonlinearForcingHeatSecondMomentFrozenProfile ν U i)
      τ₀ := by
  let a : ℝ := τ₀ / 2
  have ha : 0 < a := by
    dsimp only [a]
    linarith
  have haτ₀ : a < τ₀ := by
    dsimp only [a]
    linarith
  have hnear : Set.Ioi a ∈ 𝓝 τ₀ :=
    Ioi_mem_nhds haτ₀

  have hBoundInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν a ξ *
              h3RawFinLerayOuterProductDivergence U U i ξ‖)
        (volume : Measure H3FourierPoint3) := by
    have hMoment :=
      h3RawFinLerayOuterProductDivergenceHeatRepresentative_moment_integrable
        hν ha U U i 2 (by norm_num)
    simpa only [
      h3RawFinLerayOuterProductDivergenceHeatRepresentative
    ] using hMoment

  have hIntegral :
      Tendsto
        (fun τ : ℝ =>
          ∫ ξ : H3FourierPoint3,
            ‖ξ‖ ^ 2 *
              ‖h3HeatFourierSymbol ν τ ξ *
                h3RawFinLerayOuterProductDivergence U U i ξ‖)
        (𝓝 τ₀)
        (𝓝
          (∫ ξ : H3FourierPoint3,
            ‖ξ‖ ^ 2 *
              ‖h3HeatFourierSymbol ν τ₀ ξ *
                h3RawFinLerayOuterProductDivergence U U i ξ‖)) := by
    exact
      MeasureTheory.tendsto_integral_filter_of_dominated_convergence
        (l := 𝓝 τ₀)
        (F := fun τ : ℝ => fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν τ ξ *
              h3RawFinLerayOuterProductDivergence U U i ξ‖)
        (f := fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν τ₀ ξ *
              h3RawFinLerayOuterProductDivergence U U i ξ‖)
        (bound := fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν a ξ *
              h3RawFinLerayOuterProductDivergence U U i ξ‖)
        (by
          filter_upwards [hnear] with τ hτ
          have hτpos : 0 < τ := lt_trans ha hτ
          have hMoment :=
            h3RawFinLerayOuterProductDivergenceHeatRepresentative_moment_integrable
              hν hτpos U U i 2 (by norm_num)
          have hInt :
              Integrable
                (fun ξ : H3FourierPoint3 =>
                  ‖ξ‖ ^ 2 *
                    ‖h3HeatFourierSymbol ν τ ξ *
                      h3RawFinLerayOuterProductDivergence U U i ξ‖)
                (volume : Measure H3FourierPoint3) := by
            simpa only [
              h3RawFinLerayOuterProductDivergenceHeatRepresentative
            ] using hMoment
          exact hInt.aestronglyMeasurable)
        (by
          filter_upwards [hnear] with τ hτ
          exact
            Eventually.of_forall fun ξ => by
              have hdom :=
                h3NonlinearForcingHeatSecondMomentFrozenKernel_le_of_le
                  hν ha hτ.le U i ξ
              have hnonneg :
                  0 ≤
                    ‖ξ‖ ^ 2 *
                      ‖h3HeatFourierSymbol ν τ ξ *
                        h3RawFinLerayOuterProductDivergence U U i ξ‖ := by
                positivity
              rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
              exact hdom)
        hBoundInt
        (Eventually.of_forall fun ξ =>
          (continuous_h3NonlinearForcingHeatSecondMomentFrozenKernel_lag
            ν U i ξ).continuousAt)

  change
    Tendsto
      (fun τ : ℝ =>
        ∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν τ ξ *
              h3RawFinLerayOuterProductDivergence U U i ξ‖)
      (𝓝 τ₀)
      (𝓝
        (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν τ₀ ξ *
              h3RawFinLerayOuterProductDivergence U U i ξ‖))
  exact hIntegral

end

end Euclidean
end Bridge
end PrimeTensor
