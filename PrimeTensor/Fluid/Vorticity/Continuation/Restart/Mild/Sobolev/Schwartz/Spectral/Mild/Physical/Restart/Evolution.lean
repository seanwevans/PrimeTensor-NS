import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Physical.Restart.Semigroup
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Mild.Restart.Physical.Realization

/-!
# Canonical physical restart evolution for the selected mild path

The Duhamel restart remainder is now mesh-independent and satisfies its own
semigroup law.  This file attaches that canonical remainder directly to the
Banach-selected mild solution.

For every admissible restart origin `a` and positive elapsed duration `T`, the
selected path satisfies the exact spectral identity

    W(a + T) = H_T (W a) + R(a,T),

where `R(a,T)` is the canonical restart remainder.  After decoding, the same
identity holds in physical `L²`, and the nonlinear remainder belongs to the
Schwartz heat--Leray physical-realization set for duration `T`.

This is the mesh-free evolution law intended for the continuation layer: a
restart step carries only its origin and elapsed time, not an auxiliary
partition or tail integral.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

/-- Exact canonical restart equation for the Banach-selected physical-time
mild extension. -/
theorem h3SpectralFinHeatLerayMildSolutionPhysicalExtension_restart_eq_restartRemainder
    {ν τ A a : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hsmall :
      8 * h3HeatLerayDuhamelPathCoefficient ν * A * Real.sqrt τ ≤ 1)
    (T : NNReal)
    (ha : 0 ≤ a)
    (hT : 0 < T)
    (haT : a + (T : ℝ) ≤ τ) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionPhysicalExtension
        hν hτ U₀ hA hU₀ hsmall
    h3SpectralVelocityHeatApplyNN ν hν.le T (W a)
      + h3SpectralFinHeatLerayDuhamelRestartRemainder
          ν a hν W W T
      = W (a + (T : ℝ)) := by
  dsimp only
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionPhysicalExtension
      hν hτ U₀ hA hU₀ hsmall

  have hTR : 0 < (T : ℝ) := by
    exact_mod_cast hT
  have hTR0 : 0 ≤ (T : ℝ) := hTR.le
  have haTR0 : 0 ≤ a + (T : ℝ) := add_nonneg ha hTR0
  have haτ : a ≤ τ := by
    exact le_trans (le_add_of_nonneg_right hTR0) haT

  let qa : Set.Icc (0 : ℝ) τ :=
    ⟨a, ha, haτ⟩
  let qaT : Set.Icc (0 : ℝ) τ :=
    ⟨a + (T : ℝ), haTR0, haT⟩

  have hMildA0 :=
    h3SpectralFinHeatLerayPhysicalMildSolution_satisfies_mild_at
      hν hτ U₀ hA hU₀ hsmall qa
  have hqaNN :
      h3PhysicalTimePointNN qa = NNReal.mk a ha := by
    rfl
  rw [hqaNN] at hMildA0
  have hMildA :
      h3SpectralVelocityHeatApplyNN
          ν hν.le (NNReal.mk a ha) U₀
        +
      h3SpectralFinHeatLerayDuhamel
          ν a hν W W
        =
      W a := by
    simpa only [W, qa,
      h3SpectralFinHeatLerayPhysicalMildSolution_apply] using hMildA0

  have hMildAT0 :=
    h3SpectralFinHeatLerayPhysicalMildSolution_satisfies_mild_at
      hν hτ U₀ hA hU₀ hsmall qaT
  have hqaTNN :
      h3PhysicalTimePointNN qaT =
        NNReal.mk (a + (T : ℝ)) haTR0 := by
    rfl
  rw [hqaTNN] at hMildAT0

  have hsumNN :
      NNReal.mk (a + (T : ℝ)) haTR0
        = NNReal.mk a ha + T := by
    apply Subtype.ext
    simp
  rw [hsumNN] at hMildAT0
  have hMildAT :
      h3SpectralVelocityHeatApplyNN
          ν hν.le (NNReal.mk a ha + T) U₀
        +
      h3SpectralFinHeatLerayDuhamel
          ν (a + (T : ℝ)) hν W W
        =
      W (a + (T : ℝ)) := by
    simpa only [W, qaT,
      h3SpectralFinHeatLerayPhysicalMildSolution_apply] using hMildAT0

  have hWb :=
    h3SpectralFinHeatLerayMildSolutionPhysicalExtension_continuous_bounded
      hν hτ U₀ hA hU₀ hsmall
  have hWcont : Continuous W := by
    simpa only [W] using hWb.1
  have hWbound : ∀ s : ℝ, ‖W s‖ ≤ 2 * A := by
    intro s
    simpa only [W] using hWb.2 s
  have htwoA : 0 ≤ 2 * A :=
    mul_nonneg (by norm_num) hA.le

  have hIntA :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand ν a hν W W)
        volume 0 a := by
    exact
      h3SpectralFinHeatLerayDuhamelIntegrand_intervalIntegrable_of_continuous
        hν ha htwoA htwoA W W hWcont hWcont
        (fun s _ => hWbound s)
        (fun s _ => hWbound s)

  have hIntAT :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand
          ν (a + (T : ℝ)) hν W W)
        volume 0 (a + (T : ℝ)) := by
    exact
      h3SpectralFinHeatLerayDuhamelIntegrand_intervalIntegrable_of_continuous
        hν haTR0 htwoA htwoA W W hWcont hWcont
        (fun s _ => hWbound s)
        (fun s _ => hWbound s)

  have hTmk : NNReal.mk (T : ℝ) hTR0 = T := by
    apply Subtype.ext
    rfl

  have hMildAT' :
      h3SpectralVelocityHeatApplyNN
          ν hν.le
          (NNReal.mk a ha + NNReal.mk (T : ℝ) hTR0)
          U₀
        +
      h3SpectralFinHeatLerayDuhamel
          ν (a + (T : ℝ)) hν W W
        =
      W (a + (T : ℝ)) := by
    simpa only [hTmk] using hMildAT

  have hRestart :=
    h3SpectralFinHeatLerayMild_restart_tail
      (a := a)
      (b := (T : ℝ))
      hν ha hTR0 U₀ W
      hMildA hMildAT' hIntAT hIntA

  rw [h3SpectralFinHeatLerayDuhamel_tail_eq_shifted hν W W] at hRestart
  simpa only [
    h3SpectralFinHeatLerayDuhamelRestartRemainder,
    hTmk
  ] using hRestart

/-- Mesh-free physical restart equation for the selected mild path, together
with Schwartz realization of its canonical nonlinear remainder. -/
theorem h3SpectralFinHeatLerayMildSolutionPhysicalExtension_restart_decodeComplexL2_realized
    {ν τ A a : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hsmall :
      8 * h3HeatLerayDuhamelPathCoefficient ν * A * Real.sqrt τ ≤ 1)
    (T : NNReal)
    (ha : 0 ≤ a)
    (hT : 0 < T)
    (haT : a + (T : ℝ) ≤ τ) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionPhysicalExtension
        hν hτ U₀ hA hU₀ hsmall
    let R :=
      h3SpectralFinHeatLerayDuhamelRestartRemainder
        ν a hν W W T
    h3SpectralFinVectorDecodeComplexL2 (W (a + (T : ℝ)))
        =
      h3ComplexPhysicalVelocityHeatApplyNN ν hν.le T (W a)
        + h3SpectralFinVectorDecodeComplexL2 R
      ∧
    h3SpectralFinVectorDecodeComplexL2 R
        ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization
            ν (T : ℝ) hν := by
  dsimp only
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionPhysicalExtension
      hν hτ U₀ hA hU₀ hsmall
  let R : H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayDuhamelRestartRemainder
      ν a hν W W T

  have hSpec :=
    h3SpectralFinHeatLerayMildSolutionPhysicalExtension_restart_eq_restartRemainder
      hν hτ U₀ hA hU₀ hsmall T ha hT haT
  have hDec := congrArg h3SpectralFinVectorDecodeComplexL2 hSpec
  rw [h3SpectralFinVectorDecodeComplexL2_add] at hDec
  rw [h3SpectralFinVectorDecodeComplexL2_velocityHeatApplyNN] at hDec

  have hWb :=
    h3SpectralFinHeatLerayMildSolutionPhysicalExtension_continuous_bounded
      hν hτ U₀ hA hU₀ hsmall
  have hWcont : Continuous W := by
    simpa only [W] using hWb.1
  have hWbound : ∀ s : ℝ, ‖W s‖ ≤ 2 * A := by
    intro s
    simpa only [W] using hWb.2 s
  have htwoA : 0 ≤ 2 * A :=
    mul_nonneg (by norm_num) hA.le

  have hR :=
    h3SpectralFinHeatLerayDuhamelRestartRemainder_decodeComplexL2_mem_physicalRealization_of_continuous
      (a := a)
      hν htwoA htwoA W W hWcont hWcont hWbound hWbound T hT

  constructor
  · simpa only [W, R] using hDec.symm
  · simpa only [R] using hR

end

end Euclidean
end Bridge
end PrimeTensor
