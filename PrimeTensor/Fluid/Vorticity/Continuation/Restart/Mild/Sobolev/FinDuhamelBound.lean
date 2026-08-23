import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.FinVorticityFlux
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Fin-indexed H³ vorticity Duhamel bound

The one-time nonlinear kernel is now available in the native `Fin 3` restart
indexing:

    ‖Nν(t; U, Ω)‖
      ≤ 96 C_deweight (sqrt (ν t))⁻¹ ‖U‖ ‖Ω‖.

This file performs the next logically separate step.  For paths `U(s), Ω(s)`
it defines the actual interval-integral Duhamel term

    ∫₀ᵗ Nν(t-s; U(s), Ω(s)) ds,

with the endpoint `s = t` defined to be zero.  Under an explicit
`IntervalIntegrable` hypothesis on that Banach-valued kernel, the scalar
majorant proves

    ‖Dν[U,Ω](t)‖
      ≤ 192 C_deweight (sqrt ν)⁻¹ sqrt(t) M_U M_Ω

whenever the two paths are bounded by `M_U` and `M_Ω` on `(0,t]`.

The integrability hypothesis is intentionally explicit.  Lean defines the
integral of a nonintegrable function to be zero; retaining the hypothesis here
prevents that convention from masquerading as the analytic Duhamel theorem.
The next rung will discharge it from time continuity/measurability.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory
open scoped ENNReal NNReal Interval

noncomputable section

/-- The viscous reciprocal-square-root time kernel. -/
def h3ViscousTimeSingularKernel
    (ν t s : ℝ) : ℝ :=
  (Real.sqrt (ν * (t - s)))⁻¹

/--
The viscous reciprocal-square-root kernel is interval integrable on `[0,t]`
for positive viscosity and nonnegative terminal time.
-/
theorem h3ViscousTimeSingularKernel_intervalIntegrable
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 ≤ t) :
    IntervalIntegrable
      (h3ViscousTimeSingularKernel ν t)
      volume
      0
      t := by
  have hr :
      IntervalIntegrable
        (fun x : ℝ => x ^ (-(1 / 2 : ℝ)))
        volume
        0
        t :=
    intervalIntegral.intervalIntegrable_rpow'
      (by norm_num)

  have hshift :
      IntervalIntegrable
        (fun s : ℝ => (t - s) ^ (-(1 / 2 : ℝ)))
        volume
        0
        t := by
    have h := hr.comp_sub_left t
    simpa using h.symm

  have hscaled :
      IntervalIntegrable
        (fun s : ℝ =>
          (Real.sqrt ν)⁻¹ *
            (t - s) ^ (-(1 / 2 : ℝ)))
        volume
        0
        t :=
    hshift.const_mul (Real.sqrt ν)⁻¹

  refine hscaled.congr ?_
  intro s hs
  rw [Set.uIoc_of_le ht] at hs
  have hts :
      0 ≤ t - s :=
    sub_nonneg.mpr hs.2
  unfold h3ViscousTimeSingularKernel
  rw [Real.sqrt_mul hν.le]
  change
    (Real.sqrt ν)⁻¹ * (t - s) ^ (-(1 / 2 : ℝ))
      =
    (Real.sqrt ν * Real.sqrt (t - s))⁻¹
  rw [← h3_inv_sqrt_eq_rpow_neg_half hts]
  rw [mul_inv_rev]
  ring

/-- One-time nonlinear kernel inserted at retarded time `t - s`. -/
noncomputable def h3SpectralFinVorticityDuhamelIntegrand
    (ν t : ℝ)
    (hν : 0 < ν)
    (U Ω : ℝ → H3SpectralFinVectorState)
    (s : ℝ) :
    H3SpectralFinVectorState :=
  if hs : 0 < t - s then
    h3SpectralFinVorticityHeatDivergenceApply
      ν (t - s) hν hs (U s) (Ω s)
  else
    0

/-- Pointwise norm envelope for the retarded nonlinear kernel on `(0,t]`. -/
theorem norm_h3SpectralFinVorticityDuhamelIntegrand_le
    {ν t s : ℝ}
    (hν : 0 < ν)
    (hs : s ∈ Set.Ioc (0 : ℝ) t)
    (U Ω : ℝ → H3SpectralFinVectorState) :
    ‖h3SpectralFinVorticityDuhamelIntegrand
        ν t hν U Ω s‖
      ≤
    96 * h3SobolevDeweightingConstant *
      h3ViscousTimeSingularKernel ν t s *
      ‖U s‖ * ‖Ω s‖ := by
  by_cases hst : 0 < t - s
  · rw [h3SpectralFinVorticityDuhamelIntegrand, dif_pos hst]
    unfold h3ViscousTimeSingularKernel
    exact
      norm_h3SpectralFinVorticityHeatDivergenceApply_le
        hν hst (U s) (Ω s)
  · have hnonneg :
        0 ≤ t - s :=
      sub_nonneg.mpr hs.2
    have hzero :
        t - s = 0 :=
      le_antisymm (le_of_not_gt hst) hnonneg
    rw [h3SpectralFinVorticityDuhamelIntegrand, dif_neg hst]
    simp [h3ViscousTimeSingularKernel, hzero]

/-- Scalar majorant after inserting uniform path bounds. -/
def h3VorticityDuhamelMajorant
    (ν t MU MO : ℝ)
    (s : ℝ) : ℝ :=
  (96 * h3SobolevDeweightingConstant *
      h3ViscousTimeSingularKernel ν t s) *
    (MU * MO)

/-- The bounded-path scalar Duhamel majorant is interval integrable. -/
theorem h3VorticityDuhamelMajorant_intervalIntegrable
    {ν t MU MO : ℝ}
    (hν : 0 < ν)
    (ht : 0 ≤ t) :
    IntervalIntegrable
      (h3VorticityDuhamelMajorant ν t MU MO)
      volume
      0
      t := by
  have hk :=
    h3ViscousTimeSingularKernel_intervalIntegrable
      hν ht
  have hscaled :=
    hk.const_mul
      (96 * h3SobolevDeweightingConstant)
  have hbounded :=
    hscaled.mul_const (MU * MO)
  refine hbounded.congr ?_
  intro s _hs
  unfold h3VorticityDuhamelMajorant
  ring

/-- Exact integral of the bounded-path scalar majorant. -/
theorem h3VorticityDuhamelMajorant_integral
    {ν t MU MO : ℝ}
    (hν : 0 < ν)
    (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t,
        h3VorticityDuhamelMajorant ν t MU MO s)
      =
    h3VorticityDuhamelCoefficient ν *
      Real.sqrt t * MU * MO := by
  calc
    (∫ s in (0 : ℝ)..t,
        h3VorticityDuhamelMajorant ν t MU MO s)
        =
      (∫ s in (0 : ℝ)..t,
        96 * h3SobolevDeweightingConstant *
          h3ViscousTimeSingularKernel ν t s) *
        (MU * MO) := by
          simp only [h3VorticityDuhamelMajorant]
          rw [intervalIntegral.integral_mul_const]
    _ =
      (h3VorticityDuhamelCoefficient ν *
        Real.sqrt t) * (MU * MO) := by
          simp only [h3ViscousTimeSingularKernel]
          rw [h3_vorticityKernelEnvelope_integral hν ht]
    _ =
      h3VorticityDuhamelCoefficient ν *
        Real.sqrt t * MU * MO := by
          ring

/-- Actual Fin-indexed H³ vorticity Duhamel interval integral. -/
noncomputable def h3SpectralFinVorticityDuhamel
    (ν t : ℝ)
    (hν : 0 < ν)
    (U Ω : ℝ → H3SpectralFinVectorState) :
    H3SpectralFinVectorState :=
  ∫ s in (0 : ℝ)..t,
    h3SpectralFinVorticityDuhamelIntegrand
      ν t hν U Ω s

/--
The concrete square-root-time Duhamel estimate.

`hInt` records the genuine Bochner interval integrability of the nonlinear
kernel; the following rung will derive this hypothesis from path regularity.
-/
theorem norm_h3SpectralFinVorticityDuhamel_le
    {ν t MU MO : ℝ}
    (hν : 0 < ν)
    (ht : 0 ≤ t)
    (hMU : 0 ≤ MU)
    (hMO : 0 ≤ MO)
    (U Ω : ℝ → H3SpectralFinVectorState)
    (hInt :
      IntervalIntegrable
        (h3SpectralFinVorticityDuhamelIntegrand
          ν t hν U Ω)
        volume
        0
        t)
    (hU :
      ∀ s ∈ Set.Ioc (0 : ℝ) t,
        ‖U s‖ ≤ MU)
    (hΩ :
      ∀ s ∈ Set.Ioc (0 : ℝ) t,
        ‖Ω s‖ ≤ MO) :
    ‖h3SpectralFinVorticityDuhamel
        ν t hν U Ω‖
      ≤
    h3VorticityDuhamelCoefficient ν *
      Real.sqrt t * MU * MO := by
  have hMajorantInt :
      IntervalIntegrable
        (h3VorticityDuhamelMajorant ν t MU MO)
        volume
        0
        t :=
    h3VorticityDuhamelMajorant_intervalIntegrable
      hν ht

  have hPointwise :
      ∀ᵐ s : ℝ ∂volume,
        s ∈ Set.Ioc (0 : ℝ) t →
          ‖h3SpectralFinVorticityDuhamelIntegrand
              ν t hν U Ω s‖
            ≤
          h3VorticityDuhamelMajorant
            ν t MU MO s := by
    filter_upwards with s
    intro hs
    have hKernel :
        0 ≤
          96 * h3SobolevDeweightingConstant *
            h3ViscousTimeSingularKernel ν t s := by
      unfold h3ViscousTimeSingularKernel
      positivity [h3SobolevDeweightingConstant_nonneg]

    have hProduct :
        ‖U s‖ * ‖Ω s‖ ≤ MU * MO := by
      exact
        mul_le_mul
          (hU s hs)
          (hΩ s hs)
          (norm_nonneg (Ω s))
          hMU

    calc
      ‖h3SpectralFinVorticityDuhamelIntegrand
          ν t hν U Ω s‖
          ≤
        96 * h3SobolevDeweightingConstant *
          h3ViscousTimeSingularKernel ν t s *
          ‖U s‖ * ‖Ω s‖ :=
        norm_h3SpectralFinVorticityDuhamelIntegrand_le
          hν hs U Ω
      _ =
        (96 * h3SobolevDeweightingConstant *
          h3ViscousTimeSingularKernel ν t s) *
          (‖U s‖ * ‖Ω s‖) := by
            ring
      _ ≤
        (96 * h3SobolevDeweightingConstant *
          h3ViscousTimeSingularKernel ν t s) *
          (MU * MO) :=
        mul_le_mul_of_nonneg_left hProduct hKernel
      _ =
        h3VorticityDuhamelMajorant
          ν t MU MO s := by
            rfl

  have hBound :
      ‖h3SpectralFinVorticityDuhamel
          ν t hν U Ω‖
        ≤
      ∫ s in (0 : ℝ)..t,
        h3VorticityDuhamelMajorant
          ν t MU MO s := by
    unfold h3SpectralFinVorticityDuhamel
    exact
      intervalIntegral.norm_integral_le_of_norm_le
        ht
        hPointwise
        hMajorantInt

  exact
    hBound.trans_eq
      (h3VorticityDuhamelMajorant_integral
        hν ht)

end

end Euclidean
end Bridge
end PrimeTensor
