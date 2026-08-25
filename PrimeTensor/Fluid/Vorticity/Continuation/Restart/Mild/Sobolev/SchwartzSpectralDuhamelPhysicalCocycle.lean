import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.SchwartzSpectralMildRestartPhysicalRealization

/-!
# Physical cocycle for realized heat--Leray Duhamel remainders

Interior restart realization is now available for every positive tail.  The
remaining algebraic fact needed for repeated restart is that those nonlinear
remainders concatenate correctly.

For the path translated to an interior time `a`, the ordinary Duhamel restart
identity gives

    D_{b+c}(U_a,V_a)
      = H_c D_b(U_a,V_a) + D_c(U_{a+b},V_{a+b}).

This file packages that identity on continuous globally bounded paths and then
decodes it.  Each of the three terms belongs to the already-established
Schwartz physical realization set at its own elapsed time.  Thus the realized
nonlinear remainder is a genuine restart cocycle: repeated positive-time
restarts compose without reopening the Schwartz approximation or Bochner
integration arguments.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

/-- Exact Duhamel cocycle for a path translated to the interior time `a`.
Continuity and global bounds provide the two interval-integrability hypotheses
needed by the existing Duhamel restart theorem. -/
theorem h3SpectralFinHeatLerayDuhamel_shifted_add_time_of_continuous
    {ν a b c MU MV : ℝ}
    (hν : 0 < ν)
    (hb : 0 < b)
    (hc : 0 < c)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s : ℝ, ‖U s‖ ≤ MU)
    (hV : ∀ s : ℝ, ‖V s‖ ≤ MV) :
    h3SpectralFinHeatLerayDuhamel
        ν (b + c) hν
        (fun q => U (q + a))
        (fun q => V (q + a))
      =
    h3SpectralVelocityHeatApplyNN
        ν hν.le (NNReal.mk c hc.le)
        (h3SpectralFinHeatLerayDuhamel
          ν b hν
          (fun q => U (q + a))
          (fun q => V (q + a)))
      +
    h3SpectralFinHeatLerayDuhamel
        ν c hν
        (fun r => U ((r + b) + a))
        (fun r => V ((r + b) + a)) := by
  let Ua : ℝ → H3SpectralFinVectorState :=
    fun q => U (q + a)
  let Va : ℝ → H3SpectralFinVectorState :=
    fun q => V (q + a)

  have hUaCont : Continuous Ua := by
    dsimp [Ua]
    exact hUcont.comp (continuous_id.add continuous_const)
  have hVaCont : Continuous Va := by
    dsimp [Va]
    exact hVcont.comp (continuous_id.add continuous_const)

  have hUa : ∀ q : ℝ, ‖Ua q‖ ≤ MU := by
    intro q
    exact hU (q + a)
  have hVa : ∀ q : ℝ, ‖Va q‖ ≤ MV := by
    intro q
    exact hV (q + a)

  have hbc : 0 ≤ b + c := add_nonneg hb.le hc.le

  have hIntB :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand ν b hν Ua Va)
        volume 0 b := by
    exact
      h3SpectralFinHeatLerayDuhamelIntegrand_intervalIntegrable_of_continuous
        hν hb.le hMU hMV Ua Va hUaCont hVaCont
        (fun q _ => hUa q)
        (fun q _ => hVa q)

  have hIntBC :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand ν (b + c) hν Ua Va)
        volume 0 (b + c) := by
    exact
      h3SpectralFinHeatLerayDuhamelIntegrand_intervalIntegrable_of_continuous
        hν hbc hMU hMV Ua Va hUaCont hVaCont
        (fun q _ => hUa q)
        (fun q _ => hVa q)

  have hAdd :=
    h3SpectralFinHeatLerayDuhamel_add_time
      hν hb.le hc.le Ua Va hIntBC hIntB

  have hTail :=
    h3SpectralFinHeatLerayDuhamel_tail_eq_shifted
      (a := b) (b := c) hν Ua Va

  rw [hTail] at hAdd
  simpa only [Ua, Va] using hAdd

/-- Decoded physical cocycle together with Schwartz physical realization of
all three elapsed-time remainders. -/
theorem h3SpectralFinHeatLerayDuhamel_shifted_decodeComplexL2_realized_cocycle_of_continuous
    {ν a b c MU MV : ℝ}
    (hν : 0 < ν)
    (hb : 0 < b)
    (hc : 0 < c)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s : ℝ, ‖U s‖ ≤ MU)
    (hV : ∀ s : ℝ, ‖V s‖ ≤ MV) :
    let RabS :=
      h3SpectralFinHeatLerayDuhamel
        ν b hν
        (fun q => U (q + a))
        (fun q => V (q + a))
    let RbcS :=
      h3SpectralFinHeatLerayDuhamel
        ν c hν
        (fun r => U ((r + b) + a))
        (fun r => V ((r + b) + a))
    let RacS :=
      h3SpectralFinHeatLerayDuhamel
        ν (b + c) hν
        (fun q => U (q + a))
        (fun q => V (q + a))
    h3SpectralFinVectorDecodeComplexL2 RabS
        ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization ν b hν
      ∧
    h3SpectralFinVectorDecodeComplexL2 RbcS
        ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization ν c hν
      ∧
    h3SpectralFinVectorDecodeComplexL2 RacS
        ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization ν (b + c) hν
      ∧
    h3SpectralFinVectorDecodeComplexL2 RacS
      =
    h3ComplexPhysicalVelocityHeatApplyNN
        ν hν.le (NNReal.mk c hc.le) RabS
      + h3SpectralFinVectorDecodeComplexL2 RbcS := by
  dsimp only

  let Ua : ℝ → H3SpectralFinVectorState :=
    fun q => U (q + a)
  let Va : ℝ → H3SpectralFinVectorState :=
    fun q => V (q + a)
  let Uab : ℝ → H3SpectralFinVectorState :=
    fun r => Ua (r + b)
  let Vab : ℝ → H3SpectralFinVectorState :=
    fun r => Va (r + b)

  have hUaCont : Continuous Ua := by
    dsimp [Ua]
    exact hUcont.comp (continuous_id.add continuous_const)
  have hVaCont : Continuous Va := by
    dsimp [Va]
    exact hVcont.comp (continuous_id.add continuous_const)
  have hUabCont : Continuous Uab := by
    dsimp [Uab]
    exact hUaCont.comp (continuous_id.add continuous_const)
  have hVabCont : Continuous Vab := by
    dsimp [Vab]
    exact hVaCont.comp (continuous_id.add continuous_const)

  have hUa : ∀ q : ℝ, ‖Ua q‖ ≤ MU := by
    intro q
    exact hU (q + a)
  have hVa : ∀ q : ℝ, ‖Va q‖ ≤ MV := by
    intro q
    exact hV (q + a)
  have hUab : ∀ r : ℝ, ‖Uab r‖ ≤ MU := by
    intro r
    exact hUa (r + b)
  have hVab : ∀ r : ℝ, ‖Vab r‖ ≤ MV := by
    intro r
    exact hVa (r + b)

  have hbcPos : 0 < b + c := add_pos hb hc

  have hRab :
      h3SpectralFinVectorDecodeComplexL2
          (h3SpectralFinHeatLerayDuhamel ν b hν Ua Va)
        ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization ν b hν := by
    exact
      h3SpectralFinHeatLerayDuhamel_decodeComplexL2_mem_physicalRealization_of_continuous
        hν hb hMU hMV Ua Va hUaCont hVaCont hUa hVa

  have hRbc :
      h3SpectralFinVectorDecodeComplexL2
          (h3SpectralFinHeatLerayDuhamel ν c hν Uab Vab)
        ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization ν c hν := by
    exact
      h3SpectralFinHeatLerayDuhamel_decodeComplexL2_mem_physicalRealization_of_continuous
        hν hc hMU hMV Uab Vab hUabCont hVabCont hUab hVab

  have hRac :
      h3SpectralFinVectorDecodeComplexL2
          (h3SpectralFinHeatLerayDuhamel ν (b + c) hν Ua Va)
        ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization
            ν (b + c) hν := by
    exact
      h3SpectralFinHeatLerayDuhamel_decodeComplexL2_mem_physicalRealization_of_continuous
        hν hbcPos hMU hMV Ua Va hUaCont hVaCont hUa hVa

  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Ua, Va] using hRab
  · simpa only [Ua, Va, Uab, Vab] using hRbc
  · simpa only [Ua, Va] using hRac
  · have hSpec :=
      h3SpectralFinHeatLerayDuhamel_shifted_add_time_of_continuous
        (a := a) hν hb hc hMU hMV U V hUcont hVcont hU hV
    have hDec :=
      congrArg h3SpectralFinVectorDecodeComplexL2 hSpec
    rw [h3SpectralFinVectorDecodeComplexL2_add] at hDec
    rw [h3SpectralFinVectorDecodeComplexL2_velocityHeatApplyNN] at hDec
    exact hDec

/-- The Banach-selected globally clamped mild path inherits the realized
Duhamel cocycle at every interior translation `a` and every pair of positive
elapsed times `b,c`. -/
theorem h3SpectralFinHeatLerayMildSolutionPhysicalExtension_realized_remainder_cocycle
    {ν τ A a b c : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hsmall :
      8 * h3HeatLerayDuhamelPathCoefficient ν * A * Real.sqrt τ ≤ 1)
    (hb : 0 < b)
    (hc : 0 < c) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionPhysicalExtension
        hν hτ U₀ hA hU₀ hsmall
    let RabS :=
      h3SpectralFinHeatLerayDuhamel
        ν b hν
        (fun q => W (q + a))
        (fun q => W (q + a))
    let RbcS :=
      h3SpectralFinHeatLerayDuhamel
        ν c hν
        (fun r => W ((r + b) + a))
        (fun r => W ((r + b) + a))
    let RacS :=
      h3SpectralFinHeatLerayDuhamel
        ν (b + c) hν
        (fun q => W (q + a))
        (fun q => W (q + a))
    h3SpectralFinVectorDecodeComplexL2 RabS
        ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization ν b hν
      ∧
    h3SpectralFinVectorDecodeComplexL2 RbcS
        ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization ν c hν
      ∧
    h3SpectralFinVectorDecodeComplexL2 RacS
        ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization ν (b + c) hν
      ∧
    h3SpectralFinVectorDecodeComplexL2 RacS
      =
    h3ComplexPhysicalVelocityHeatApplyNN
        ν hν.le (NNReal.mk c hc.le) RabS
      + h3SpectralFinVectorDecodeComplexL2 RbcS := by
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
    (h3SpectralFinHeatLerayDuhamel_shifted_decodeComplexL2_realized_cocycle_of_continuous
      (a := a)
      hν hb hc htwoA htwoA W W
      hWcont hWcont hWbound hWbound)

end

end Euclidean
end Bridge
end PrimeTensor
