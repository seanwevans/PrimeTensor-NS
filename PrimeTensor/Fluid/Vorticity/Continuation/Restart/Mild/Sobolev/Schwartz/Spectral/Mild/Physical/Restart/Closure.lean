import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Mild.Physical.Restart.Evolution
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Physical.Restart.Semigroup

/-!
# Physical restart closure for the selected mild path

The canonical positive restart remainder is mesh-independent, physically
realized, and satisfies a two-interval semigroup law.  This file packages
those facts directly with the selected mild path.

For two successive positive elapsed times `b` and `c`, the selected path has a
signed physical restart equation on the first leg, on the fresh second leg,
and on the single combined leg `b + c`.  The three positive nonlinear
remainders are physically realized by Schwartz heat--Leray anchors, and the
combined decoded remainder is exactly the heat advance of the first decoded
remainder plus the fresh decoded remainder.

Thus the selected solution evolves by

    W(a+t) = H_t W(a) - R(a,t),

while the positive remainders themselves retain the semigroup law

    R(a,b+c) = H_c R(a,b) + R(a+b,c).

This is a continuation-facing closure statement: downstream arguments may
advance by two restart steps or by their combined elapsed time without
carrying a partition witness or reopening the Duhamel construction.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

/-- Two successive positive restart steps of the Banach-selected mild path are
closed under the canonical physical restart interface. -/
theorem h3SpectralFinHeatLerayMildSolutionPhysicalExtension_restart_physical_closed_twoStep
    {ν τ A a : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hsmall :
      8 * h3HeatLerayDuhamelPathCoefficient ν * A * Real.sqrt τ ≤ 1)
    (b c : NNReal)
    (ha : 0 ≤ a)
    (hb : 0 < b)
    (hc : 0 < c)
    (haBC : a + ((b + c : NNReal) : ℝ) ≤ τ) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionPhysicalExtension
        hν hτ U₀ hA hU₀ hsmall
    let Rb :=
      h3SpectralFinHeatLerayDuhamelRestartRemainder
        ν a hν W W b
    let Rc :=
      h3SpectralFinHeatLerayDuhamelRestartRemainder
        ν ((b : ℝ) + a) hν W W c
    let Rbc :=
      h3SpectralFinHeatLerayDuhamelRestartRemainder
        ν a hν W W (b + c)
    h3SpectralFinVectorDecodeComplexL2 (W (a + (b : ℝ)))
        = h3ComplexPhysicalVelocityHeatApplyNN ν hν.le b (W a)
          - h3SpectralFinVectorDecodeComplexL2 Rb
      ∧
    h3SpectralFinVectorDecodeComplexL2
        (W (((b : ℝ) + a) + (c : ℝ)))
        = h3ComplexPhysicalVelocityHeatApplyNN
            ν hν.le c (W ((b : ℝ) + a))
          - h3SpectralFinVectorDecodeComplexL2 Rc
      ∧
    h3SpectralFinVectorDecodeComplexL2
        (W (a + ((b + c : NNReal) : ℝ)))
        = h3ComplexPhysicalVelocityHeatApplyNN ν hν.le (b + c) (W a)
          - h3SpectralFinVectorDecodeComplexL2 Rbc
      ∧
    h3SpectralFinVectorDecodeComplexL2 Rb
        ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization ν (b : ℝ) hν
      ∧
    h3SpectralFinVectorDecodeComplexL2 Rc
        ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization ν (c : ℝ) hν
      ∧
    h3SpectralFinVectorDecodeComplexL2 Rbc
        ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization
            ν ((b + c : NNReal) : ℝ) hν
      ∧
    h3SpectralFinVectorDecodeComplexL2 Rbc
        = h3ComplexPhysicalVelocityHeatApplyNN ν hν.le c Rb
          + h3SpectralFinVectorDecodeComplexL2 Rc := by
  dsimp only
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionPhysicalExtension
      hν hτ U₀ hA hU₀ hsmall
  let Rb : H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayDuhamelRestartRemainder
      ν a hν W W b
  let Rc : H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayDuhamelRestartRemainder
      ν ((b : ℝ) + a) hν W W c
  let Rbc : H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayDuhamelRestartRemainder
      ν a hν W W (b + c)

  have hbR0 : 0 ≤ (b : ℝ) := by exact_mod_cast hb.le
  have hcR0 : 0 ≤ (c : ℝ) := by exact_mod_cast hc.le

  have haB : a + (b : ℝ) ≤ τ := by
    calc
      a + (b : ℝ) ≤ a + ((b : ℝ) + (c : ℝ)) := by
        linarith
      _ = a + ((b + c : NNReal) : ℝ) := by simp
      _ ≤ τ := haBC

  have hba0 : 0 ≤ (b : ℝ) + a := add_nonneg hbR0 ha
  have hbaC : ((b : ℝ) + a) + (c : ℝ) ≤ τ := by
    simpa only [NNReal.coe_add, add_assoc, add_comm, add_left_comm] using haBC

  have hbc : 0 < b + c := add_pos hb hc

  have hB0 :=
    h3SpectralFinHeatLerayMildSolutionPhysicalExtension_restart_decodeComplexL2_realized
      (a := a)
      hν hτ U₀ hA hU₀ hsmall b ha hb haB
  have hB :
      h3SpectralFinVectorDecodeComplexL2 (W (a + (b : ℝ)))
          = h3ComplexPhysicalVelocityHeatApplyNN ν hν.le b (W a)
            - h3SpectralFinVectorDecodeComplexL2 Rb
        ∧
      h3SpectralFinVectorDecodeComplexL2 Rb
          ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization
              ν (b : ℝ) hν := by
    simpa only [W, Rb] using hB0

  have hC0 :=
    h3SpectralFinHeatLerayMildSolutionPhysicalExtension_restart_decodeComplexL2_realized
      (a := (b : ℝ) + a)
      hν hτ U₀ hA hU₀ hsmall c hba0 hc hbaC
  have hC :
      h3SpectralFinVectorDecodeComplexL2
          (W (((b : ℝ) + a) + (c : ℝ)))
          = h3ComplexPhysicalVelocityHeatApplyNN
              ν hν.le c (W ((b : ℝ) + a))
            - h3SpectralFinVectorDecodeComplexL2 Rc
        ∧
      h3SpectralFinVectorDecodeComplexL2 Rc
          ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization
              ν (c : ℝ) hν := by
    simpa only [W, Rc] using hC0

  have hBC0 :=
    h3SpectralFinHeatLerayMildSolutionPhysicalExtension_restart_decodeComplexL2_realized
      (a := a)
      hν hτ U₀ hA hU₀ hsmall (b + c) ha hbc haBC
  have hBC :
      h3SpectralFinVectorDecodeComplexL2
          (W (a + ((b + c : NNReal) : ℝ)))
          = h3ComplexPhysicalVelocityHeatApplyNN
              ν hν.le (b + c) (W a)
            - h3SpectralFinVectorDecodeComplexL2 Rbc
        ∧
      h3SpectralFinVectorDecodeComplexL2 Rbc
          ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization
              ν ((b + c : NNReal) : ℝ) hν := by
    simpa only [W, Rbc] using hBC0

  have hCocycle0 :=
    h3SpectralFinHeatLerayMildSolutionPhysicalExtension_restartRemainder_realized_add
      (a := a)
      hν hτ U₀ hA hU₀ hsmall b c hb hc
  have hCocycle :
      h3SpectralFinVectorDecodeComplexL2 Rb
          ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization ν (b : ℝ) hν
        ∧
      h3SpectralFinVectorDecodeComplexL2 Rc
          ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization ν (c : ℝ) hν
        ∧
      h3SpectralFinVectorDecodeComplexL2 Rbc
          ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization
              ν ((b + c : NNReal) : ℝ) hν
        ∧
      h3SpectralFinVectorDecodeComplexL2 Rbc
          = h3ComplexPhysicalVelocityHeatApplyNN ν hν.le c Rb
            + h3SpectralFinVectorDecodeComplexL2 Rc := by
    simpa only [W, Rb, Rc, Rbc] using hCocycle0

  rcases hB with ⟨hEqB, hMemB⟩
  rcases hC with ⟨hEqC, hMemC⟩
  rcases hBC with ⟨hEqBC, hMemBC⟩
  rcases hCocycle with ⟨_, _, _, hEqCocycle⟩
  exact ⟨hEqB, hEqC, hEqBC, hMemB, hMemC, hMemBC, hEqCocycle⟩

end

end Euclidean
end Bridge
end PrimeTensor
