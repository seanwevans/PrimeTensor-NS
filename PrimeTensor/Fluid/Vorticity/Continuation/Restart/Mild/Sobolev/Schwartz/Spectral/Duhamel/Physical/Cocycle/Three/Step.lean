import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Physical.Cocycle

/-!
# Three-step physical Duhamel cocycle

The two-step cocycle already shows that one interior restart composes exactly.
This file records the first genuinely iterated consequence, for three positive
elapsed times `b`, `c`, and `d`.

Starting from an interior origin `a`, write `R_b`, `R_c`, and `R_d` for the
three consecutive Duhamel remainders, and `R_{b+c}`, `R_{b+c+d}` for the
corresponding accumulated remainders.  Then all five decoded remainders are
Schwartz physically realized, while

    R_{b+c}   = H_c R_b       + R_c,
    R_{b+c+d} = H_d R_{b+c}   + R_d.

No new analytic estimate enters: this is the compiled induction seed for
arbitrary finite restart chains.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

/-- Three consecutive positive elapsed times give two compatible realized
physical cocycle identities.  This is the finite induction seed used by
iterated restart. -/
theorem h3SpectralFinHeatLerayDuhamel_shifted_decodeComplexL2_realized_three_step_cocycle_of_continuous
    {ν a b c d MU MV : ℝ}
    (hν : 0 < ν)
    (hb : 0 < b)
    (hc : 0 < c)
    (hd : 0 < d)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s : ℝ, ‖U s‖ ≤ MU)
    (hV : ∀ s : ℝ, ‖V s‖ ≤ MV) :
    let RbS :=
      h3SpectralFinHeatLerayDuhamel
        ν b hν
        (fun q => U (q + a))
        (fun q => V (q + a))
    let RcS :=
      h3SpectralFinHeatLerayDuhamel
        ν c hν
        (fun r => U ((r + b) + a))
        (fun r => V ((r + b) + a))
    let RdS :=
      h3SpectralFinHeatLerayDuhamel
        ν d hν
        (fun s => U ((s + (b + c)) + a))
        (fun s => V ((s + (b + c)) + a))
    let RbcS :=
      h3SpectralFinHeatLerayDuhamel
        ν (b + c) hν
        (fun q => U (q + a))
        (fun q => V (q + a))
    let RbcdS :=
      h3SpectralFinHeatLerayDuhamel
        ν ((b + c) + d) hν
        (fun q => U (q + a))
        (fun q => V (q + a))
    h3SpectralFinVectorDecodeComplexL2 RbS
        ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization ν b hν
      ∧
    h3SpectralFinVectorDecodeComplexL2 RcS
        ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization ν c hν
      ∧
    h3SpectralFinVectorDecodeComplexL2 RdS
        ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization ν d hν
      ∧
    h3SpectralFinVectorDecodeComplexL2 RbcS
        ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization ν (b + c) hν
      ∧
    h3SpectralFinVectorDecodeComplexL2 RbcdS
        ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization ν ((b + c) + d) hν
      ∧
    h3SpectralFinVectorDecodeComplexL2 RbcS
      =
    h3ComplexPhysicalVelocityHeatApplyNN
        ν hν.le (NNReal.mk c hc.le) RbS
      + h3SpectralFinVectorDecodeComplexL2 RcS
      ∧
    h3SpectralFinVectorDecodeComplexL2 RbcdS
      =
    h3ComplexPhysicalVelocityHeatApplyNN
        ν hν.le (NNReal.mk d hd.le) RbcS
      + h3SpectralFinVectorDecodeComplexL2 RdS := by
  dsimp only
  have hbc : 0 < b + c := add_pos hb hc

  have h1 :=
    h3SpectralFinHeatLerayDuhamel_shifted_decodeComplexL2_realized_cocycle_of_continuous
      (a := a) hν hb hc hMU hMV U V hUcont hVcont hU hV

  have h2 :=
    h3SpectralFinHeatLerayDuhamel_shifted_decodeComplexL2_realized_cocycle_of_continuous
      (a := a) hν hbc hd hMU hMV U V hUcont hVcont hU hV

  exact
    ⟨h1.1,
      h1.2.1,
      h2.2.1,
      h1.2.2.1,
      h2.2.2.1,
      h1.2.2.2,
      h2.2.2.2⟩

/-- The Banach-selected globally clamped mild path inherits the three-step
realized physical cocycle at every interior origin. -/
theorem h3SpectralFinHeatLerayMildSolutionPhysicalExtension_realized_three_step_remainder_cocycle
    {ν τ A a b c d : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hsmall :
      8 * h3HeatLerayDuhamelPathCoefficient ν * A * Real.sqrt τ ≤ 1)
    (hb : 0 < b)
    (hc : 0 < c)
    (hd : 0 < d) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionPhysicalExtension
        hν hτ U₀ hA hU₀ hsmall
    let RbS :=
      h3SpectralFinHeatLerayDuhamel
        ν b hν
        (fun q => W (q + a))
        (fun q => W (q + a))
    let RcS :=
      h3SpectralFinHeatLerayDuhamel
        ν c hν
        (fun r => W ((r + b) + a))
        (fun r => W ((r + b) + a))
    let RdS :=
      h3SpectralFinHeatLerayDuhamel
        ν d hν
        (fun s => W ((s + (b + c)) + a))
        (fun s => W ((s + (b + c)) + a))
    let RbcS :=
      h3SpectralFinHeatLerayDuhamel
        ν (b + c) hν
        (fun q => W (q + a))
        (fun q => W (q + a))
    let RbcdS :=
      h3SpectralFinHeatLerayDuhamel
        ν ((b + c) + d) hν
        (fun q => W (q + a))
        (fun q => W (q + a))
    h3SpectralFinVectorDecodeComplexL2 RbS
        ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization ν b hν
      ∧
    h3SpectralFinVectorDecodeComplexL2 RcS
        ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization ν c hν
      ∧
    h3SpectralFinVectorDecodeComplexL2 RdS
        ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization ν d hν
      ∧
    h3SpectralFinVectorDecodeComplexL2 RbcS
        ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization ν (b + c) hν
      ∧
    h3SpectralFinVectorDecodeComplexL2 RbcdS
        ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization ν ((b + c) + d) hν
      ∧
    h3SpectralFinVectorDecodeComplexL2 RbcS
      =
    h3ComplexPhysicalVelocityHeatApplyNN
        ν hν.le (NNReal.mk c hc.le) RbS
      + h3SpectralFinVectorDecodeComplexL2 RcS
      ∧
    h3SpectralFinVectorDecodeComplexL2 RbcdS
      =
    h3ComplexPhysicalVelocityHeatApplyNN
        ν hν.le (NNReal.mk d hd.le) RbcS
      + h3SpectralFinVectorDecodeComplexL2 RdS := by
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
    (h3SpectralFinHeatLerayDuhamel_shifted_decodeComplexL2_realized_three_step_cocycle_of_continuous
      (a := a)
      hν hb hc hd htwoA htwoA W W
      hWcont hWcont hWbound hWbound)

end

end Euclidean
end Bridge
end PrimeTensor
