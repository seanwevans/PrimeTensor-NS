import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.FourierL2HeatMovingState

/-!
# Physical L² temporal admissibility: jointly moving heat time and state

The interaction-picture slope contains both a moving raw Fourier `L²` state
and a moving nonnegative heat time.  Strong continuity for a fixed state plus
contractivity is enough to control both simultaneously.

If

    τₙ → τ₀
    and
    Vₙ → V₀

strongly, then

    S(τₙ) Vₙ → S(τ₀) V₀.

No operator-norm continuity of the heat semigroup is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Interval

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2TemporalEndpointFourierL2HeatMovingTime
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Joint strong continuity of the quotient-safe raw Fourier heat action in
both nonnegative time and the moving `L²` state. -/
theorem tendsto_h3RawFourierL2HeatApplyNN_moving
    {ι : Type*}
    {l : Filter ι}
    (ν : ℝ)
    (hν : 0 ≤ ν)
    {τ : ι → ℝ≥0}
    {τ₀ : ℝ≥0}
    {V : ι → H3RawFourierL2FinVectorState}
    {V₀ : H3RawFourierL2FinVectorState}
    (hτ :
      Tendsto
        τ
        l
        (𝓝 τ₀))
    (hV :
      Tendsto
        V
        l
        (𝓝 V₀)) :
    Tendsto
      (fun n : ι =>
        h3RawFourierL2HeatApplyNN
          ν hν (τ n) (V n))
      l
      (𝓝
        (h3RawFourierL2HeatApplyNN
          ν hν τ₀ V₀)) := by
  let E : H3RawFourierL2FinVectorState :=
    h3RawFourierL2HeatApplyNN
      ν hν τ₀ V₀

  let g : ι → ℝ :=
    fun n =>
      ‖V n - V₀‖ +
        ‖h3RawFourierL2HeatApplyNN
              ν hν (τ n) V₀
            - E‖

  have hVConst :
      Tendsto
        (fun _n : ι => V₀)
        l
        (𝓝 V₀) :=
    tendsto_const_nhds

  have hEConst :
      Tendsto
        (fun _n : ι => E)
        l
        (𝓝 E) :=
    tendsto_const_nhds

  have hVdiff :
      Tendsto
        (fun n : ι => ‖V n - V₀‖)
        l
        (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      (hV.sub hVConst).norm

  have hHeatAt :
      Tendsto
        (fun r : ℝ≥0 =>
          h3RawFourierL2HeatApplyNN
            ν hν r V₀)
        (𝓝 τ₀)
        (𝓝 E) := by
    dsimp only [E]
    exact
      (continuous_h3RawFourierL2HeatApplyNN
        ν hν V₀).continuousAt

  have hHeatFixed :
      Tendsto
        (fun n : ι =>
          h3RawFourierL2HeatApplyNN
            ν hν (τ n) V₀)
        l
        (𝓝 E) :=
    hHeatAt.comp hτ

  have hHeatDiff :
      Tendsto
        (fun n : ι =>
          ‖h3RawFourierL2HeatApplyNN
                ν hν (τ n) V₀
              - E‖)
        l
        (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      (hHeatFixed.sub hEConst).norm

  have hgZero :
      Tendsto
        g
        l
        (𝓝 0) := by
    dsimp only [g]
    simpa using
      hVdiff.add hHeatDiff

  have hUpper :
      ∀ᶠ n : ι in l,
        ‖h3RawFourierL2HeatApplyNN
              ν hν (τ n) (V n)
            - E‖
          ≤
        g n := by
    refine Eventually.of_forall ?_
    intro n

    have hDiff :
        h3RawFourierL2HeatApplyNN
              ν hν (τ n) (V n)
            - E
          =
        h3RawFourierL2HeatApplyNN
              ν hν (τ n) (V n - V₀)
          +
        (h3RawFourierL2HeatApplyNN
              ν hν (τ n) V₀
            - E) := by
      change
        h3RawFourierL2HeatCLM
              ν hν (τ n) (V n)
            - E
          =
        h3RawFourierL2HeatCLM
              ν hν (τ n) (V n - V₀)
          +
        (h3RawFourierL2HeatCLM
              ν hν (τ n) V₀
            - E)
      rw [map_sub]
      abel

    rw [hDiff]

    calc
      ‖h3RawFourierL2HeatApplyNN
              ν hν (τ n) (V n - V₀)
          +
        (h3RawFourierL2HeatApplyNN
              ν hν (τ n) V₀
            - E)‖
          ≤
        ‖h3RawFourierL2HeatApplyNN
            ν hν (τ n) (V n - V₀)‖
          +
        ‖h3RawFourierL2HeatApplyNN
              ν hν (τ n) V₀
            - E‖ :=
        norm_add_le _ _
      _ ≤
        ‖V n - V₀‖
          +
        ‖h3RawFourierL2HeatApplyNN
              ν hν (τ n) V₀
            - E‖ := by
        exact
          add_le_add
            (norm_h3RawFourierL2HeatApplyNN_le
              ν hν (τ n) (V n - V₀))
            (le_refl _)
      _ = g n := by
        rfl

  have hNonneg :
      ∀ᶠ n : ι in l,
        0 ≤
          ‖h3RawFourierL2HeatApplyNN
                ν hν (τ n) (V n)
              - E‖ :=
    Eventually.of_forall fun n =>
      norm_nonneg _

  have hResult :
      Tendsto
        (fun n : ι =>
          h3RawFourierL2HeatApplyNN
            ν hν (τ n) (V n))
        l
        (𝓝 E) := by
    exact
      (tendsto_iff_norm_sub_tendsto_zero).2
        (squeeze_zero'
          hNonneg
          hUpper
          hgZero)

  simpa only [E] using hResult

end

end Euclidean
end Bridge
end PrimeTensor
