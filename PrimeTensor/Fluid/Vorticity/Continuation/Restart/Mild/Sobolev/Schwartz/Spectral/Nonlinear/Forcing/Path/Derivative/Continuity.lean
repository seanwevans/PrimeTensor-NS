import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Path.Derivative.Lag.Continuity

/-!
# Continuity of the retarded pointwise nonlinear first-derivative path

The previous modules isolated the three terms in a retarded derivative-path
difference.  The first two are controlled quantitatively by bilinearity, and
the third is continuous because the heat lag stays strictly positive at every
interior source time.

This file assembles those ingredients.  For continuous spectral paths `U` and
`V`, the pointwise first spatial derivative of the retarded nonlinear heat
representative is continuous at every `s₀ < t`, hence continuous on `(0,t)`.
The time-integrability theorem then applies immediately, closing the
measurability premise without any additional endpoint estimate.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped Topology Interval

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralNonlinearForcingPathDerivativeContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- For continuous spectral input paths, the retarded pointwise first
spatial derivative is continuous at every source time strictly before the
observation time. -/
theorem continuousAt_h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
    {ν t s₀ : ℝ}
    (hν : 0 < ν)
    (hs₀ : s₀ < t)
    (U V : ℝ → H3SpectralFinVectorState)
    (hU : Continuous U)
    (hV : Continuous V)
    (i j : Fin 3)
    (x : H3FourierPoint3) :
    ContinuousAt
      (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
        ν t U V i j x)
      s₀ := by
  have hs₀lag : 0 < t - s₀ :=
    sub_pos.mpr hs₀

  let c : ℝ → ℝ :=
    fun s =>
      (2 * Real.pi) *
        h3NonlinearForcingHeatFirstMomentCoefficient ν (t - s) *
        h3NonlinearForcingL1Coefficient

  let T : ℝ → ℂ :=
    fun s =>
      h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
        ν (t - s) (U s₀) (V s₀) i j x

  let g : ℝ → ℝ :=
    fun s =>
      c s * ‖U s - U s₀‖ * ‖V s‖
        +
      c s * ‖U s₀‖ * ‖V s - V s₀‖
        +
      ‖T s - T s₀‖

  have hLag :
      ContinuousAt (fun s : ℝ => t - s) s₀ :=
    continuousAt_const.sub continuousAt_id

  have hScaledLag :
      ContinuousAt (fun s : ℝ => (t - s) / 3) s₀ :=
    hLag.div_const 3

  have hSqrt :
      ContinuousAt
        (fun s : ℝ =>
          Real.sqrt (ν * ((t - s) / 3)))
        s₀ := by
    exact
      (continuousAt_const.mul hScaledLag).sqrt

  have hSqrtNe :
      Real.sqrt (ν * ((t - s₀) / 3)) ≠ 0 := by
    apply Real.sqrt_ne_zero'.mpr
    exact
      mul_pos hν (div_pos hs₀lag (by norm_num))

  have hc :
      ContinuousAt c s₀ := by
    dsimp [c, h3NonlinearForcingHeatFirstMomentCoefficient]
    exact
      (continuousAt_const.mul (hSqrt.inv₀ hSqrtNe)).mul continuousAt_const

  have hTimeAt :
      ContinuousAt T s₀ := by
    dsimp [T]
    exact
      continuousAt_h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_retarded_frozen
        hν hs₀ (U s₀) (V s₀) i j x

  have hgCont :
      ContinuousAt g s₀ := by
    dsimp [g]
    exact
      (((hc.mul
          ((hU.continuousAt.sub continuousAt_const).norm)).mul
          hV.continuousAt.norm).add
        ((hc.mul continuousAt_const).mul
          (hV.continuousAt.sub continuousAt_const).norm)).add
        (hTimeAt.sub continuousAt_const).norm

  have hgZero :
      Tendsto g (𝓝 s₀) (𝓝 0) := by
    simpa [g] using hgCont.tendsto

  have hNear :
      ∀ᶠ s : ℝ in 𝓝 s₀, s < t :=
    eventually_lt_nhds hs₀

  have hUpper :
      ∀ᶠ s : ℝ in 𝓝 s₀,
        ‖h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
              ν t U V i j x s
            -
          h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
              ν t U V i j x s₀‖
          ≤
        g s := by
    filter_upwards [hNear] with s hs
    have hlag : 0 < t - s :=
      sub_pos.mpr hs

    have hDiff :=
      h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath_sub_decomposition
        hν hs hs₀ U V i j x

    rw [hDiff]

    have hAbound :
        ‖h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
            ν (t - s) (U s - U s₀) (V s) i j x‖
          ≤
        c s * ‖U s - U s₀‖ * ‖V s‖ := by
      dsimp [c]
      exact
        norm_h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_sub_left_le
          hν hlag (U s) (U s₀) (V s) i j x

    have hBbound :
        ‖h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
            ν (t - s) (U s₀) (V s - V s₀) i j x‖
          ≤
        c s * ‖U s₀‖ * ‖V s - V s₀‖ := by
      dsimp [c]
      exact
        norm_h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_sub_right_le
          hν hlag (U s₀) (V s) (V s₀) i j x

    change
      ‖h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
            ν (t - s) (U s - U s₀) (V s) i j x
          +
        h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
            ν (t - s) (U s₀) (V s - V s₀) i j x
          +
        (T s - T s₀)‖
        ≤ g s

    calc
      ‖h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
              ν (t - s) (U s - U s₀) (V s) i j x
          +
        h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
              ν (t - s) (U s₀) (V s - V s₀) i j x
          +
        (T s - T s₀)‖
          ≤
        ‖h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
              ν (t - s) (U s - U s₀) (V s) i j x
          +
        h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
              ν (t - s) (U s₀) (V s - V s₀) i j x‖
          +
        ‖T s - T s₀‖ :=
        norm_add_le _ _
      _ ≤
        (‖h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
              ν (t - s) (U s - U s₀) (V s) i j x‖
          +
        ‖h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
              ν (t - s) (U s₀) (V s - V s₀) i j x‖)
          +
        ‖T s - T s₀‖ := by
        exact
          add_le_add
            (norm_add_le _ _)
            (le_refl _)
      _ ≤
        (c s * ‖U s - U s₀‖ * ‖V s‖
          +
        c s * ‖U s₀‖ * ‖V s - V s₀‖)
          +
        ‖T s - T s₀‖ := by
        exact
          add_le_add
            (add_le_add hAbound hBbound)
            (le_refl _)
      _ = g s := by
        rfl

  exact
    (tendsto_iff_norm_sub_tendsto_zero).2
      (squeeze_zero'
        (Eventually.of_forall fun s =>
          norm_nonneg
            (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
                ν t U V i j x s
              -
            h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
                ν t U V i j x s₀))
        hUpper
        hgZero)

/-- The retarded pointwise first-derivative path is continuous on the entire
open Duhamel interval. -/
theorem continuousOn_h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath_Ioo
    {ν t : ℝ}
    (hν : 0 < ν)
    (U V : ℝ → H3SpectralFinVectorState)
    (hU : Continuous U)
    (hV : Continuous V)
    (i j : Fin 3)
    (x : H3FourierPoint3) :
    ContinuousOn
      (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
        ν t U V i j x)
      (Set.Ioo (0 : ℝ) t) := by
  intro s hs
  exact
    (continuousAt_h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
      hν hs.2 U V hU hV i j x).continuousWithinAt

/-- Continuous spectral paths with uniform interior bounds have a genuinely
interval-integrable pointwise retarded first derivative.  This discharges the
measurability premise of the preceding time-integrability layer. -/
theorem h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath_intervalIntegrable_of_continuous
    {ν t MU MV : ℝ}
    (hν : 0 < ν)
    (ht : 0 ≤ t)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU :
      ∀ s ∈ Set.Ioo (0 : ℝ) t,
        ‖U s‖ ≤ MU)
    (hV :
      ∀ s ∈ Set.Ioo (0 : ℝ) t,
        ‖V s‖ ≤ MV)
    (i j : Fin 3)
    (x : H3FourierPoint3) :
    IntervalIntegrable
      (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
        ν t U V i j x)
      volume
      0
      t := by
  exact
    h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath_intervalIntegrable_of_continuousOn
      hν ht hMU hMV U V hU hV i j x
      (continuousOn_h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath_Ioo
        hν U V hUcont hVcont i j x)

end

end Euclidean
end Bridge
end PrimeTensor
