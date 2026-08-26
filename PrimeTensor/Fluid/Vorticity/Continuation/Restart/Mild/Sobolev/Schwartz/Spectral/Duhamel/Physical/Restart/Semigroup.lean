import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Physical.Restart.Interface

/-!
# Mesh-independent physical Duhamel restart semigroup

The canonical restart interface removes finite restart meshes from downstream
statements.  This file records the corresponding two-interval law directly at
the canonical level.

If a nonlinear remainder begins at `a`, runs for `b`, and is then restarted for
another duration `c`, the total canonical remainder over `b + c` is exactly the
heat advance by `c` of the first remainder plus the fresh canonical remainder
beginning at `(b : ℝ) + a`.

Thus restart composition is expressed only in terms of origins and elapsed
`NNReal` durations; no partition witness appears in the API.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

/-- Exact semigroup law for the canonical mesh-independent restart remainder. -/
theorem h3SpectralFinHeatLerayDuhamelRestartRemainder_add
    {ν a MU MV : ℝ}
    (hν : 0 < ν)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s : ℝ, ‖U s‖ ≤ MU)
    (hV : ∀ s : ℝ, ‖V s‖ ≤ MV)
    (b c : NNReal)
    (hb : 0 < b)
    (hc : 0 < c) :
    h3SpectralFinHeatLerayDuhamelRestartRemainder ν a hν U V (b + c)
      =
    h3SpectralVelocityHeatApplyNN
        ν hν.le c
        (h3SpectralFinHeatLerayDuhamelRestartRemainder ν a hν U V b)
      +
    h3SpectralFinHeatLerayDuhamelRestartRemainder
        ν ((b : ℝ) + a) hν U V c := by
  have hbR : 0 < (b : ℝ) := by
    exact_mod_cast hb
  have hcR : 0 < (c : ℝ) := by
    exact_mod_cast hc

  have hsplit :=
    h3SpectralFinHeatLerayDuhamel_shifted_add_time_of_continuous
      (a := a)
      hν hbR hcR hMU hMV U V hUcont hVcont hU hV

  have hmk : NNReal.mk (c : ℝ) hcR.le = c := by
    apply Subtype.ext
    simp

  rw [hmk] at hsplit
  simpa only [
    h3SpectralFinHeatLerayDuhamelRestartRemainder,
    NNReal.coe_add,
    add_assoc
  ] using hsplit

/-- The canonical restart semigroup law after physical decoding, together with
Schwartz physical realization of the first, fresh, and total remainders. -/
theorem h3SpectralFinHeatLerayDuhamelRestartRemainder_decodeComplexL2_realized_add
    {ν a MU MV : ℝ}
    (hν : 0 < ν)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s : ℝ, ‖U s‖ ≤ MU)
    (hV : ∀ s : ℝ, ‖V s‖ ≤ MV)
    (b c : NNReal)
    (hb : 0 < b)
    (hc : 0 < c) :
    let Rb :=
      h3SpectralFinHeatLerayDuhamelRestartRemainder ν a hν U V b
    let Rc :=
      h3SpectralFinHeatLerayDuhamelRestartRemainder
        ν ((b : ℝ) + a) hν U V c
    let Rbc :=
      h3SpectralFinHeatLerayDuhamelRestartRemainder ν a hν U V (b + c)
    h3SpectralFinVectorDecodeComplexL2 Rb
        ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization ν (b : ℝ) hν
      ∧
    h3SpectralFinVectorDecodeComplexL2 Rc
        ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization ν (c : ℝ) hν
      ∧
    h3SpectralFinVectorDecodeComplexL2 Rbc
        ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization ν ((b + c : NNReal) : ℝ) hν
      ∧
    h3SpectralFinVectorDecodeComplexL2 Rbc
      =
    h3ComplexPhysicalVelocityHeatApplyNN ν hν.le c Rb
      + h3SpectralFinVectorDecodeComplexL2 Rc := by
  dsimp only

  have hbc : 0 < b + c := add_pos hb hc

  have hRb :=
    h3SpectralFinHeatLerayDuhamelRestartRemainder_decodeComplexL2_mem_physicalRealization_of_continuous
      (a := a)
      hν hMU hMV U V hUcont hVcont hU hV b hb

  have hRc :=
    h3SpectralFinHeatLerayDuhamelRestartRemainder_decodeComplexL2_mem_physicalRealization_of_continuous
      (a := (b : ℝ) + a)
      hν hMU hMV U V hUcont hVcont hU hV c hc

  have hRbc :=
    h3SpectralFinHeatLerayDuhamelRestartRemainder_decodeComplexL2_mem_physicalRealization_of_continuous
      (a := a)
      hν hMU hMV U V hUcont hVcont hU hV (b + c) hbc

  have hSpec :=
    h3SpectralFinHeatLerayDuhamelRestartRemainder_add
      (a := a)
      hν hMU hMV U V hUcont hVcont hU hV b c hb hc
  have hDec := congrArg h3SpectralFinVectorDecodeComplexL2 hSpec
  rw [h3SpectralFinVectorDecodeComplexL2_add] at hDec
  rw [h3SpectralFinVectorDecodeComplexL2_velocityHeatApplyNN] at hDec

  exact ⟨hRb, hRc, hRbc, hDec⟩

/-- The Banach-selected globally clamped mild path exposes the same canonical
mesh-independent restart semigroup at every origin. -/
theorem h3SpectralFinHeatLerayMildSolutionPhysicalExtension_restartRemainder_realized_add
    {ν τ A a : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hsmall :
      8 * h3HeatLerayDuhamelPathCoefficient ν * A * Real.sqrt τ ≤ 1)
    (b c : NNReal)
    (hb : 0 < b)
    (hc : 0 < c) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionPhysicalExtension
        hν hτ U₀ hA hU₀ hsmall
    let Rb :=
      h3SpectralFinHeatLerayDuhamelRestartRemainder ν a hν W W b
    let Rc :=
      h3SpectralFinHeatLerayDuhamelRestartRemainder
        ν ((b : ℝ) + a) hν W W c
    let Rbc :=
      h3SpectralFinHeatLerayDuhamelRestartRemainder ν a hν W W (b + c)
    h3SpectralFinVectorDecodeComplexL2 Rb
        ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization ν (b : ℝ) hν
      ∧
    h3SpectralFinVectorDecodeComplexL2 Rc
        ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization ν (c : ℝ) hν
      ∧
    h3SpectralFinVectorDecodeComplexL2 Rbc
        ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization ν ((b + c : NNReal) : ℝ) hν
      ∧
    h3SpectralFinVectorDecodeComplexL2 Rbc
      =
    h3ComplexPhysicalVelocityHeatApplyNN ν hν.le c Rb
      + h3SpectralFinVectorDecodeComplexL2 Rc := by
  dsimp only
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionPhysicalExtension
      hν hτ U₀ hA hU₀ hsmall

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

  simpa only [W] using
    (h3SpectralFinHeatLerayDuhamelRestartRemainder_decodeComplexL2_realized_add
      (a := a)
      hν htwoA htwoA W W hWcont hWcont hWbound hWbound
      b c hb hc)

end

end Euclidean
end Bridge
end PrimeTensor
