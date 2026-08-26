import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Kernel

/-!
# Fin-indexed H³ heat--Leray Duhamel bound

`FinHeatLerayKernel` proves the genuine instantaneous velocity estimate

    ‖P e^{νtΔ} div (U ⊗ V)‖
      ≤ 288 C_deweight (sqrt (ν t))⁻¹ ‖U‖ ‖V‖.

This file inserts that kernel at retarded time `t - s`, defines the actual
interval-integral Duhamel term, and proves

    ‖Dν[U,V](t)‖
      ≤ 576 C_deweight (sqrt ν)⁻¹ sqrt(t) MU MV

for uniformly bounded paths.

As in `FinDuhamelBound`, genuine Banach-valued interval integrability is kept
as an explicit hypothesis.  This prevents Lean's convention for the integral
of a nonintegrable function from being mistaken for the analytic theorem.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory
open scoped ENNReal NNReal Interval

noncomputable section

/--
The genuine heat--Leray velocity kernel inserted at retarded time `t - s`.

The endpoint `s = t` is defined to be zero so no positive-time witness is
required at the singular endpoint.
-/
noncomputable def h3SpectralFinHeatLerayDuhamelIntegrand
    (ν t : ℝ)
    (hν : 0 < ν)
    (U V : ℝ → H3SpectralFinVectorState)
    (s : ℝ) :
    H3SpectralFinVectorState :=
  if hs : 0 < t - s then
    h3SpectralFinHeatLerayVelocityApply
      ν (t - s) hν hs (U s) (V s)
  else
    0

/-- Pointwise norm envelope for the retarded heat--Leray velocity kernel. -/
theorem norm_h3SpectralFinHeatLerayDuhamelIntegrand_le
    {ν t s : ℝ}
    (hν : 0 < ν)
    (hs : s ∈ Set.Ioc (0 : ℝ) t)
    (U V : ℝ → H3SpectralFinVectorState) :
    ‖h3SpectralFinHeatLerayDuhamelIntegrand
        ν t hν U V s‖
      ≤
    288 * h3SobolevDeweightingConstant *
      h3ViscousTimeSingularKernel ν t s *
      ‖U s‖ * ‖V s‖ := by
  by_cases hst : 0 < t - s
  · rw [h3SpectralFinHeatLerayDuhamelIntegrand, dif_pos hst]
    unfold h3ViscousTimeSingularKernel
    exact
      norm_h3SpectralFinHeatLerayVelocityApply_le
        hν hst (U s) (V s)
  · have hnonneg :
        0 ≤ t - s :=
      sub_nonneg.mpr hs.2
    have hzero :
        t - s = 0 :=
      le_antisymm (le_of_not_gt hst) hnonneg
    rw [h3SpectralFinHeatLerayDuhamelIntegrand, dif_neg hst]
    simp [h3ViscousTimeSingularKernel, hzero]

/-- Scalar majorant after inserting uniform path bounds. -/
def h3HeatLerayDuhamelMajorant
    (ν t MU MV : ℝ)
    (s : ℝ) : ℝ :=
  (288 * h3SobolevDeweightingConstant *
      h3ViscousTimeSingularKernel ν t s) *
    (MU * MV)

/-- The bounded-path scalar heat--Leray majorant is interval integrable. -/
theorem h3HeatLerayDuhamelMajorant_intervalIntegrable
    {ν t MU MV : ℝ}
    (hν : 0 < ν)
    (ht : 0 ≤ t) :
    IntervalIntegrable
      (h3HeatLerayDuhamelMajorant ν t MU MV)
      volume
      0
      t := by
  have hk :=
    h3ViscousTimeSingularKernel_intervalIntegrable
      hν ht
  have hscaled :=
    hk.const_mul
      (288 * h3SobolevDeweightingConstant)
  have hbounded :=
    hscaled.mul_const (MU * MV)
  refine hbounded.congr ?_
  intro s _hs
  unfold h3HeatLerayDuhamelMajorant
  ring

/-- Exact integral of the bounded-path heat--Leray scalar majorant. -/
theorem h3HeatLerayDuhamelMajorant_integral
    {ν t MU MV : ℝ}
    (hν : 0 < ν)
    (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t,
        h3HeatLerayDuhamelMajorant ν t MU MV s)
      =
    h3HeatLerayDuhamelCoefficient ν *
      Real.sqrt t * MU * MV := by
  calc
    (∫ s in (0 : ℝ)..t,
        h3HeatLerayDuhamelMajorant ν t MU MV s)
        =
      (∫ s in (0 : ℝ)..t,
        288 * h3SobolevDeweightingConstant *
          h3ViscousTimeSingularKernel ν t s) *
        (MU * MV) := by
          unfold h3HeatLerayDuhamelMajorant
          rw [intervalIntegral.integral_mul_const]
    _ =
      (h3HeatLerayDuhamelCoefficient ν *
        Real.sqrt t) * (MU * MV) := by
          rw [h3_heatLerayKernelEnvelope_integral hν ht]
    _ =
      h3HeatLerayDuhamelCoefficient ν *
        Real.sqrt t * MU * MV := by
          ring

/-- Actual Fin-indexed H³ heat--Leray Duhamel interval integral. -/
noncomputable def h3SpectralFinHeatLerayDuhamel
    (ν t : ℝ)
    (hν : 0 < ν)
    (U V : ℝ → H3SpectralFinVectorState) :
    H3SpectralFinVectorState :=
  ∫ s in (0 : ℝ)..t,
    h3SpectralFinHeatLerayDuhamelIntegrand
      ν t hν U V s

/--
Concrete square-root-time H³ heat--Leray Duhamel estimate.

`hInt` explicitly records genuine Bochner interval integrability of the
retarded nonlinear kernel.
-/
theorem norm_h3SpectralFinHeatLerayDuhamel_le
    {ν t MU MV : ℝ}
    (hν : 0 < ν)
    (ht : 0 ≤ t)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hInt :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand
          ν t hν U V)
        volume
        0
        t)
    (hU :
      ∀ s ∈ Set.Ioc (0 : ℝ) t,
        ‖U s‖ ≤ MU)
    (hV :
      ∀ s ∈ Set.Ioc (0 : ℝ) t,
        ‖V s‖ ≤ MV) :
    ‖h3SpectralFinHeatLerayDuhamel
        ν t hν U V‖
      ≤
    h3HeatLerayDuhamelCoefficient ν *
      Real.sqrt t * MU * MV := by
  have hMajorantInt :
      IntervalIntegrable
        (h3HeatLerayDuhamelMajorant ν t MU MV)
        volume
        0
        t :=
    h3HeatLerayDuhamelMajorant_intervalIntegrable
      hν ht

  have hPointwise :
      ∀ᵐ s : ℝ ∂volume,
        s ∈ Set.Ioc (0 : ℝ) t →
          ‖h3SpectralFinHeatLerayDuhamelIntegrand
              ν t hν U V s‖
            ≤
          h3HeatLerayDuhamelMajorant
            ν t MU MV s := by
    filter_upwards with s
    intro hs
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
          (hU s hs)
          (hV s hs)
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
          hν hs U V
      _ =
        (288 * h3SobolevDeweightingConstant *
          h3ViscousTimeSingularKernel ν t s) *
          (‖U s‖ * ‖V s‖) := by
            ring
      _ ≤
        (288 * h3SobolevDeweightingConstant *
          h3ViscousTimeSingularKernel ν t s) *
          (MU * MV) :=
        mul_le_mul_of_nonneg_left hProduct hKernel
      _ =
        h3HeatLerayDuhamelMajorant
          ν t MU MV s := by
            rfl

  have hBound :
      ‖h3SpectralFinHeatLerayDuhamel
          ν t hν U V‖
        ≤
      ∫ s in (0 : ℝ)..t,
        h3HeatLerayDuhamelMajorant
          ν t MU MV s := by
    unfold h3SpectralFinHeatLerayDuhamel
    exact
      intervalIntegral.norm_integral_le_of_norm_le
        ht
        hPointwise
        hMajorantInt

  exact
    hBound.trans_eq
      (h3HeatLerayDuhamelMajorant_integral
        hν ht)

end

end Euclidean
end Bridge
end PrimeTensor
