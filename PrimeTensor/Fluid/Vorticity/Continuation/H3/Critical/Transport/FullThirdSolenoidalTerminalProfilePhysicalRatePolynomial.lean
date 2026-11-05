import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileAnchoredRateBarrier
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessEndpointViscousAnnularQuinticRate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEQuadraticEighthCutoff244
import Mathlib.Tactic

/-!
# Physical quintic/eighth-power content of the anchored terminal H3 PDE barrier

The anchored terminal rate is not an arbitrary scalar: its linear part is the
actual initial weighted H3 amplitude times the projected physical momentum
source ceiling, multiplied by a fifth-order Fourier cutoff factor. Its
quadratic part is the *square* of that source ceiling, multiplied by an
explicit eighth-order cutoff factor. This module turns the previously proved
quadratic rate barrier into an exact physical alternative, without introducing
a new source hypothesis or a uniform bound on the outer annulus radius.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

/-- The genuine physical quadratic-rate barrier has only two possible
sources of amplification: an H3-state-times-source quintic frequency cost,
or a source-squared eighth-power frequency cost. -/
theorem thirdFull_quadraticPDESum_forces_quinticOrEighth244
    (R Q K C M : ℝ)
    (hR : 1 ≤ R) (hQ : 1 ≤ Q)
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hRate : M ^ 2 < 8 *
      (h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C +
       h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244 R Q C + 1)) :
    M ^ 2 < 384 * K * C * ((Q + 1) ^ 5 + (R + 1) ^ 5) + 8 ∨
    M ^ 2 < 576 * C ^ 2 * ((Q + 1) ^ 8 + (R + 1) ^ 8) + 8 := by
  let Λ : ℝ := h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C
  let Ξ : ℝ := h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244 R Q C
  have hRate' : M ^ 2 < 8 * (Λ + Ξ + 1) := hRate
  have hSplit : M ^ 2 < 16 * Λ + 8 ∨ M ^ 2 < 16 * Ξ + 8 := by
    by_contra hNot
    push_neg at hNot
    linarith only [hRate', hNot.1, hNot.2]
  rcases hSplit with hLinear | hQuadratic
  · left
    have hUpper : Λ ≤
        24 * K * C * ((Q + 1) ^ 5 + (R + 1) ^ 5) :=
      h3Critical_annularPDE_variationRate_le_quinticPhysicalProduct
        R Q K C hR hQ hK hC
    have hScaled := mul_le_mul_of_nonneg_left hUpper (by norm_num : (0 : ℝ) ≤ 16)
    calc
      M ^ 2 < 16 * Λ + 8 := hLinear
      _ ≤ 16 * (24 * K * C * ((Q + 1) ^ 5 + (R + 1) ^ 5)) + 8 :=
        add_le_add_left hScaled 8
      _ = 384 * K * C * ((Q + 1) ^ 5 + (R + 1) ^ 5) + 8 := by ring
  · right
    have hUpper : Ξ ≤
        36 * C ^ 2 * ((Q + 1) ^ 8 + (R + 1) ^ 8) :=
      h3Path_quadraticPDESourceRate_le_eighthRadiusSum244
        R Q C (by linarith only [hR]) (by linarith only [hQ])
    have hScaled := mul_le_mul_of_nonneg_left hUpper (by norm_num : (0 : ℝ) ≤ 16)
    calc
      M ^ 2 < 16 * Ξ + 8 := hQuadratic
      _ ≤ 16 * (36 * C ^ 2 * ((Q + 1) ^ 8 + (R + 1) ^ 8)) + 8 :=
        add_le_add_left hScaled 8
      _ = 576 * C ^ 2 * ((Q + 1) ^ 8 + (R + 1) ^ 8) + 8 := by ring

/-- If a chosen physical projected-source ceiling is at most S, a large
annular PDE rate must be paid by the *explicit* state/outer-frequency gains
evaluated at S. Thus a high rate forces either a large selected source
ceiling or genuine amplification in the spectral gains; it cannot be an
unexplained rate constant. -/
theorem thirdFull_quadraticPDESum_forces_sourceOrSpectralGains244
    (R Q K C S M : ℝ)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hS : 0 ≤ S)
    (hRate : M ^ 2 < 8 *
      (h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C +
       h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244 R Q C + 1)) :
    S < C ∨
      M ^ 2 < 8 *
        (S * h3PathFiniteAnnulusPDELinearGain244 R Q K +
          S ^ 2 * h3PathFiniteAnnulusPDEQuadraticGain244 R Q + 1) := by
  by_cases hSC : S < C
  · exact Or.inl hSC
  · right
    have hCS : C ≤ S := le_of_not_gt hSC
    have hGains := h3Path_finiteAnnulusPDEGains_nonneg244 R Q K hK
    have hCS2 : C ^ 2 ≤ S ^ 2 :=
      (sq_le_sq₀ hC hS).mpr hCS
    have hLinear :
        C * h3PathFiniteAnnulusPDELinearGain244 R Q K ≤
        S * h3PathFiniteAnnulusPDELinearGain244 R Q K :=
      mul_le_mul_of_nonneg_right hCS hGains.1
    have hQuadratic :
        C ^ 2 * h3PathFiniteAnnulusPDEQuadraticGain244 R Q ≤
        S ^ 2 * h3PathFiniteAnnulusPDEQuadraticGain244 R Q :=
      mul_le_mul_of_nonneg_right hCS2 hGains.2
    rw [h3Path_finiteAnnulusPDERate_sourcePolynomial244] at hRate
    have hSum :
        C * h3PathFiniteAnnulusPDELinearGain244 R Q K +
            C ^ 2 * h3PathFiniteAnnulusPDEQuadraticGain244 R Q + 1 ≤
        S * h3PathFiniteAnnulusPDELinearGain244 R Q K +
            S ^ 2 * h3PathFiniteAnnulusPDEQuadraticGain244 R Q + 1 := by
      linarith only [hLinear, hQuadratic]
    exact hRate.trans_le
      (mul_le_mul_of_nonneg_left hSum (by norm_num : (0 : ℝ) ≤ 8))

end
end PrimeTensor.FirstMonomialTriad
