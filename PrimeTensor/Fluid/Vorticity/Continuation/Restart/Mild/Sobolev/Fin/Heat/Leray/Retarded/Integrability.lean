import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Spatial.Continuity
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Retarded H³ heat--Leray integrability for continuous paths

The existing Fin-indexed Duhamel operator is formulated for real-time paths

    U V : ℝ → H3SpectralFinVectorState.

This file proves the exact analytic fact it needs before any normalized-path
wrapper is introduced:

* if `U` and `V` are continuous,
* and are uniformly bounded on `(0,t]`,
* then the endpoint-safe retarded heat--Leray integrand is genuinely
  `IntervalIntegrable` on `0..t`.

The proof has two parts.

First, on the open region `s < t`, continuity follows from:

1. positive-lag continuity with the spatial inputs frozen;
2. bilinearity in the two spatial inputs;
3. the existing positive-time kernel bound.

At a fixed `s₀ < t`, write

    K_{t-s}(U(s),V(s)) - K_{t-s₀}(U(s₀),V(s₀))

as two spatial difference terms plus one frozen-input time difference.
The two spatial terms are squeezed to zero by the bilinear norm estimate,
while the frozen-input term tends to zero by
`FinHeatLerayContinuity`.

Second, the existing reciprocal-square-root scalar majorant is already
interval integrable.  Since Lebesgue measure has no atoms,
`IntegrableOn` on `(0,t]` is equivalent to `IntegrableOn` on `(0,t)`.
Thus the singular endpoint does not create any measurability obligation.

This closes the explicit `hInt` hypothesis in `FinHeatLerayDuhamel` for
continuous bounded real-time paths.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Interval

noncomputable section

/-! ## Continuity before the retarded endpoint -/

/--
For continuous real-time velocity paths, the endpoint-safe heat--Leray
Duhamel integrand is continuous at every `s₀ < t`.
-/
theorem continuousAt_h3SpectralFinHeatLerayDuhamelIntegrand
    {ν t s₀ : ℝ}
    (hν : 0 < ν)
    (hs₀ : s₀ < t)
    (U V : ℝ → H3SpectralFinVectorState)
    (hU : Continuous U)
    (hV : Continuous V) :
    ContinuousAt
      (h3SpectralFinHeatLerayDuhamelIntegrand
        ν t hν U V)
      s₀ := by
  have hs₀lag : 0 < t - s₀ :=
    sub_pos.mpr hs₀

  let c : ℝ → ℝ :=
    fun s =>
      288 * h3SobolevDeweightingConstant *
        (Real.sqrt (ν * (t - s)))⁻¹

  let T : ℝ → H3SpectralFinVectorState :=
    fun s =>
      h3SpectralFinHeatLerayVelocityApplyZero
        ν (t - s) hν (U s₀) (V s₀)

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

  have hSqrt :
      ContinuousAt
        (fun s : ℝ =>
          Real.sqrt (ν * (t - s)))
        s₀ := by
    exact
      (continuousAt_const.mul hLag).sqrt

  have hSqrtNe :
      Real.sqrt (ν * (t - s₀)) ≠ 0 := by
    exact
      Real.sqrt_ne_zero'.mpr
        (mul_pos hν hs₀lag)

  have hc :
      ContinuousAt c s₀ := by
    dsimp [c]
    exact
      continuousAt_const.mul
        (hSqrt.inv₀ hSqrtNe)

  have hTimeAt :
      ContinuousAt T s₀ := by
    have hKernelWithin :=
      continuousOn_h3SpectralFinHeatLerayVelocityApplyZero
        hν (U s₀) (V s₀)
        (t - s₀) hs₀lag
    have hKernelAt :
        ContinuousAt
          (fun r : ℝ =>
            h3SpectralFinHeatLerayVelocityApplyZero
              ν r hν (U s₀) (V s₀))
          (t - s₀) :=
      hKernelWithin.continuousAt
        (Ioi_mem_nhds hs₀lag)
    exact
      hKernelAt.comp hLag

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
        ‖h3SpectralFinHeatLerayDuhamelIntegrand
              ν t hν U V s
            -
          h3SpectralFinHeatLerayDuhamelIntegrand
              ν t hν U V s₀‖
          ≤
        g s := by
    filter_upwards [hNear] with s hs
    have hlag : 0 < t - s :=
      sub_pos.mpr hs

    have hA :=
      h3SpectralFinHeatLerayVelocityApply_sub_left
        hν hlag (U s) (U s₀) (V s)

    have hB :=
      h3SpectralFinHeatLerayVelocityApply_sub_right
        hν hlag (U s₀) (V s) (V s₀)

    have hTs :
        T s =
          h3SpectralFinHeatLerayVelocityApply
            ν (t - s) hν hlag (U s₀) (V s₀) := by
      dsimp [T]
      exact
        h3SpectralFinHeatLerayVelocityApplyZero_of_pos
          hν hlag (U s₀) (V s₀)

    have hTs₀ :
        T s₀ =
          h3SpectralFinHeatLerayVelocityApply
            ν (t - s₀) hν hs₀lag (U s₀) (V s₀) := by
      dsimp [T]
      exact
        h3SpectralFinHeatLerayVelocityApplyZero_of_pos
          hν hs₀lag (U s₀) (V s₀)

    have hDiff :
        h3SpectralFinHeatLerayDuhamelIntegrand
              ν t hν U V s
            -
          h3SpectralFinHeatLerayDuhamelIntegrand
              ν t hν U V s₀
          =
        h3SpectralFinHeatLerayVelocityApply
              ν (t - s) hν hlag
              (U s - U s₀) (V s)
          +
        h3SpectralFinHeatLerayVelocityApply
              ν (t - s) hν hlag
              (U s₀) (V s - V s₀)
          +
        (T s - T s₀) := by
      rw [
        h3SpectralFinHeatLerayDuhamelIntegrand,
        dif_pos hlag,
        h3SpectralFinHeatLerayDuhamelIntegrand,
        dif_pos hs₀lag
      ]
      rw [hTs, hTs₀]
      rw [hA, hB]
      abel

    rw [hDiff]

    have hAbound :
        ‖h3SpectralFinHeatLerayVelocityApply
              ν (t - s) hν hlag
              (U s - U s₀) (V s)‖
          ≤
        c s * ‖U s - U s₀‖ * ‖V s‖ := by
      dsimp [c]
      exact
        norm_h3SpectralFinHeatLerayVelocityApply_le
          hν hlag (U s - U s₀) (V s)

    have hBbound :
        ‖h3SpectralFinHeatLerayVelocityApply
              ν (t - s) hν hlag
              (U s₀) (V s - V s₀)‖
          ≤
        c s * ‖U s₀‖ * ‖V s - V s₀‖ := by
      dsimp [c]
      exact
        norm_h3SpectralFinHeatLerayVelocityApply_le
          hν hlag (U s₀) (V s - V s₀)

    calc
      ‖h3SpectralFinHeatLerayVelocityApply
              ν (t - s) hν hlag
              (U s - U s₀) (V s)
          +
        h3SpectralFinHeatLerayVelocityApply
              ν (t - s) hν hlag
              (U s₀) (V s - V s₀)
          +
        (T s - T s₀)‖
          ≤
        ‖h3SpectralFinHeatLerayVelocityApply
              ν (t - s) hν hlag
              (U s - U s₀) (V s)
          +
        h3SpectralFinHeatLerayVelocityApply
              ν (t - s) hν hlag
              (U s₀) (V s - V s₀)‖
          +
        ‖T s - T s₀‖ :=
        norm_add_le _ _
      _ ≤
        (‖h3SpectralFinHeatLerayVelocityApply
              ν (t - s) hν hlag
              (U s - U s₀) (V s)‖
          +
        ‖h3SpectralFinHeatLerayVelocityApply
              ν (t - s) hν hlag
              (U s₀) (V s - V s₀)‖)
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
            (h3SpectralFinHeatLerayDuhamelIntegrand
                ν t hν U V s
              -
            h3SpectralFinHeatLerayDuhamelIntegrand
                ν t hν U V s₀))
        hUpper
        hgZero)

/--
For continuous real-time velocity paths, the retarded integrand is continuous
on the entire open integration region `(0,t)`.
-/
theorem continuousOn_h3SpectralFinHeatLerayDuhamelIntegrand_Ioo
    {ν t : ℝ}
    (hν : 0 < ν)
    (U V : ℝ → H3SpectralFinVectorState)
    (hU : Continuous U)
    (hV : Continuous V) :
    ContinuousOn
      (h3SpectralFinHeatLerayDuhamelIntegrand
        ν t hν U V)
      (Set.Ioo (0 : ℝ) t) := by
  intro s hs
  exact
    (continuousAt_h3SpectralFinHeatLerayDuhamelIntegrand
      hν hs.2 U V hU hV).continuousWithinAt

/-! ## Genuine interval integrability -/

/--
A continuous pair of real-time H³ velocity paths with uniform bounds on
`(0,t]` has a genuinely Bochner-integrable retarded heat--Leray kernel.

This is the concrete theorem that discharges the explicit `hInt` hypothesis
of `norm_h3SpectralFinHeatLerayDuhamel_le`.
-/
theorem h3SpectralFinHeatLerayDuhamelIntegrand_intervalIntegrable_of_continuous
    {ν t MU MV : ℝ}
    (hν : 0 < ν)
    (ht : 0 ≤ t)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU :
      ∀ s ∈ Set.Ioc (0 : ℝ) t,
        ‖U s‖ ≤ MU)
    (hV :
      ∀ s ∈ Set.Ioc (0 : ℝ) t,
        ‖V s‖ ≤ MV) :
    IntervalIntegrable
      (h3SpectralFinHeatLerayDuhamelIntegrand
        ν t hν U V)
      volume
      0
      t := by
  rw [
    intervalIntegrable_iff_integrableOn_Ioc_of_le ht,
    integrableOn_Ioc_iff_integrableOn_Ioo
  ]

  have hMajorantIoo :
      IntegrableOn
        (h3HeatLerayDuhamelMajorant
          ν t MU MV)
        (Set.Ioo (0 : ℝ) t)
        volume := by
    rw [
      ← integrableOn_Ioc_iff_integrableOn_Ioo,
      ← intervalIntegrable_iff_integrableOn_Ioc_of_le ht
    ]
    exact
      h3HeatLerayDuhamelMajorant_intervalIntegrable
        hν ht

  have hMeas :
      AEStronglyMeasurable
        (h3SpectralFinHeatLerayDuhamelIntegrand
          ν t hν U V)
        (volume.restrict (Set.Ioo (0 : ℝ) t)) := by
    exact
      (continuousOn_h3SpectralFinHeatLerayDuhamelIntegrand_Ioo
        hν U V hUcont hVcont).aestronglyMeasurable
          measurableSet_Ioo

  refine
    hMajorantIoo.mono'
      hMeas
      ?_

  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards with s hs

  have hsIoc :
      s ∈ Set.Ioc (0 : ℝ) t :=
    ⟨hs.1, hs.2.le⟩

  have hKernel :
      0 ≤
        288 * h3SobolevDeweightingConstant *
          h3ViscousTimeSingularKernel ν t s := by
    unfold h3ViscousTimeSingularKernel
    positivity [h3SobolevDeweightingConstant_nonneg]

  have hProduct :
      ‖U s‖ * ‖V s‖ ≤ MU * MV := by
    exact
      mul_le_mul
        (hU s hsIoc)
        (hV s hsIoc)
        (norm_nonneg (V s))
        hMU

  calc
    ‖h3SpectralFinHeatLerayDuhamelIntegrand
        ν t hν U V s‖
        ≤
      288 * h3SobolevDeweightingConstant *
        h3ViscousTimeSingularKernel ν t s *
        ‖U s‖ * ‖V s‖ :=
      norm_h3SpectralFinHeatLerayDuhamelIntegrand_le
        hν hsIoc U V
    _ =
      (288 * h3SobolevDeweightingConstant *
        h3ViscousTimeSingularKernel ν t s) *
        (‖U s‖ * ‖V s‖) := by
          ring
    _ ≤
      (288 * h3SobolevDeweightingConstant *
        h3ViscousTimeSingularKernel ν t s) *
        (MU * MV) :=
      mul_le_mul_of_nonneg_left
        hProduct hKernel
    _ =
      h3HeatLerayDuhamelMajorant
        ν t MU MV s := by
          rfl

end

end Euclidean
end Bridge
end PrimeTensor
