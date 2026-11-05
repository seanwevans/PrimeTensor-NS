import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalPhysicalTerminalHighRadialEscape
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialPhysicalZeroJetL2
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Spectral.Realizability.Closure
import Mathlib.Tactic

/-!
# Exact finite-band H³/kinetic transfer

Unlike the high-frequency Fourier projection, the low-frequency multiplier
`W₃(ξ)` is bounded on each fixed sharp gradient ball. Thus the native weighted
H³ low-band norm of a difference is controlled by its unweighted raw Fourier
L² difference, with an explicit constant depending on the cutoff radius.
This is the bridge needed to reuse the established kinetic trace machinery.
It does not assert a physical terminal L² trace or the projected momentum FTC.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Filter Topology
open scoped BigOperators ENNReal

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

private abbrev V3 := H3FourierPoint3
noncomputable local instance axisFintypeFiniteBandKineticTransfer244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- A concrete finite constant bounding the exact `W₃` weight on the ball
`2π‖ξ‖ < R + 1`. The power six is the third-derivative contribution. -/
noncomputable def thirdFullFiniteBandH3WeightCeiling244 (R : ℕ) : ℝ :=
  Real.sqrt (1 + ((R : ℝ) + 1) ^ 2 + ((R : ℝ) + 1) ^ 4 +
    ((R : ℝ) + 1) ^ 6)

/-- The finite-band multiplier ceiling is nonnegative. -/
theorem thirdFullFiniteBandH3WeightCeiling_nonneg244 (R : ℕ) :
    0 ≤ thirdFullFiniteBandH3WeightCeiling244 R := by
  exact Real.sqrt_nonneg _

/-- Exact H³ multiplier stays below its polynomial radial bound on the
sharp low-frequency ball. -/
theorem thirdFullFiniteBandH3Weight_le244 (R : ℕ) (ξ : V3)
    (hξ : ξ ∈ h3TerminalRadialFrequencyBelow ((R : ℝ) + 1)) :
    h3SobolevFrequencyWeight ξ ≤ thirdFullFiniteBandH3WeightCeiling244 R := by
  let ρ : ℝ := (R : ℝ) + 1
  let q : ℝ := h3FourierGradientSquare ξ
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hRad : h3FourierGradientMagnitude ξ < ρ := by
    simpa only [h3TerminalRadialFrequencyBelow, Set.mem_ofPred_eq] using hξ
  have hq : q ≤ ρ ^ 2 := by
    dsimp only [q]
    rw [← h3FourierGradientMagnitude_sq]
    exact pow_le_pow_left₀ (h3FourierGradientMagnitude_nonneg ξ) hRad.le 2
  have hq0 : 0 ≤ q := h3FourierGradientSquare_nonneg ξ
  have hq2 : q ^ 2 ≤ (ρ ^ 2) ^ 2 :=
    pow_le_pow_left₀ hq0 hq 2
  have hq3 : q ^ 3 ≤ (ρ ^ 2) ^ 3 :=
    pow_le_pow_left₀ hq0 hq 3
  have hPoly : h3SobolevFrequencyWeightSq ξ ≤
      1 + ρ ^ 2 + ρ ^ 4 + ρ ^ 6 := by
    dsimp only [h3SobolevFrequencyWeightSq]
    dsimp only [q] at hq hq2 hq3
    nlinarith only [hq, hq2, hq3]
  change Real.sqrt (h3SobolevFrequencyWeightSq ξ) ≤
    Real.sqrt (1 + ρ ^ 2 + ρ ^ 4 + ρ ^ 6)
  exact Real.sqrt_le_sqrt hPoly

/-- The scalar complementary low-band Fourier projection is exactly the
indicator on the sharp natural ball, a.e., including its boundary convention. -/
theorem thirdFullSpectralScalarLowRadial_ae244 (R : ℕ)
    (G : H3SpectralScalarState) :
    ((G - thirdFullSpectralHighRadialApply244 R G :
        H3SpectralScalarState) : V3 → ℂ) =ᵐ[volume]
      (h3TerminalRadialFrequencyBelow ((R : ℝ) + 1)).indicator G := by
  filter_upwards [
    MeasureTheory.Lp.coeFn_sub G (thirdFullSpectralHighRadialApply244 R G),
    thirdFullSpectralHighRadialApply_ae244 R G
  ] with ξ hSub hHigh
  -- `hSub` exposes subtraction of functions; reduce it pointwise
  -- before rewriting the high-cutoff representative at `ξ`.
  rw [hSub, Pi.sub_apply, hHigh]
  by_cases hξ : ξ ∈ h3TerminalRadialFrequencyBelow ((R : ℝ) + 1)
  · have hNot : ξ ∉ h3TopTailNaturalHighRadialSet R := by
      simpa only [h3TopTailNaturalHighRadialSet, Set.mem_compl_iff, not_not] using hξ
    simp only [Set.indicator_of_mem hξ, Set.indicator_of_notMem hNot, sub_zero]
  · have hIn : ξ ∈ h3TopTailNaturalHighRadialSet R := by
      simpa only [h3TopTailNaturalHighRadialSet, Set.mem_compl_iff] using hξ
    simp only [Set.indicator_of_notMem hξ, Set.indicator_of_mem hIn, sub_self]

/-- HARD FOURIER ESTIMATE: a low-band H³ state difference needs only raw
Fourier L². The multiplier is bounded because the band is finite. -/
theorem thirdFullSpectralScalarLowRadial_norm_le_raw244
    (R : ℕ) (G : H3SpectralScalarState) :
    ‖G - thirdFullSpectralHighRadialApply244 R G‖ ≤
      thirdFullFiniteBandH3WeightCeiling244 R *
        ‖h3SpectralScalarRawFourierL2 G‖ := by
  apply MeasureTheory.Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [
    thirdFullSpectralScalarLowRadial_ae244 R G,
    h3SpectralScalarRawFourierL2_ae G,
    h3SpectralScalarRawFourier_reweight_ae G
  ] with ξ hLow hRaw hWeight
  rw [hLow, hRaw]
  by_cases hξ : ξ ∈ h3TerminalRadialFrequencyBelow ((R : ℝ) + 1)
  · rw [Set.indicator_of_mem hξ, ← hWeight, norm_mul,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (h3SobolevFrequencyWeight_pos ξ).le]
    exact mul_le_mul_of_nonneg_right
      (thirdFullFiniteBandH3Weight_le244 R ξ hξ) (norm_nonneg _)
  · rw [Set.indicator_of_notMem hξ, norm_zero]
    exact mul_nonneg (thirdFullFiniteBandH3WeightCeiling_nonneg244 R)
      (norm_nonneg _)

/-- Exact vector low-band kinetic comparison, with the native sup norm on
three H³ spectral components. -/
theorem thirdFullSpectralVelocityLowRadial_norm_le_raw244
    (R : ℕ) (U : H3SpectralVelocityState) :
    ‖thirdFullSpectralVelocityLowRadialApply244 R U‖ ≤
      thirdFullFiniteBandH3WeightCeiling244 R *
        ‖fun j : Fin 3 => h3SpectralScalarRawFourierL2 (U j)‖ := by
  apply (pi_norm_le_iff_of_nonneg
    (mul_nonneg (thirdFullFiniteBandH3WeightCeiling_nonneg244 R)
      (norm_nonneg _))).2
  intro j
  change ‖U j - thirdFullSpectralHighRadialApply244 R (U j)‖ ≤ _
  calc
    ‖U j - thirdFullSpectralHighRadialApply244 R (U j)‖ ≤
      thirdFullFiniteBandH3WeightCeiling244 R *
        ‖h3SpectralScalarRawFourierL2 (U j)‖ :=
      thirdFullSpectralScalarLowRadial_norm_le_raw244 R (U j)
    _ ≤ thirdFullFiniteBandH3WeightCeiling244 R *
        ‖fun k : Fin 3 => h3SpectralScalarRawFourierL2 (U k)‖ :=
      mul_le_mul_of_nonneg_left
        (h3SpectralVelocity_coordinate_norm_le
          (fun k : Fin 3 => h3SpectralScalarRawFourierL2 (U k)) j)
        (thirdFullFiniteBandH3WeightCeiling_nonneg244 R)

/-- The low-band H³ difference is bounded by the ordinary raw Fourier
L² difference at the same time pair. No temporal regularity is needed. -/
theorem thirdFullSpectralVelocityLowRadial_distance_le_raw244
    (R : ℕ) (U V : H3SpectralVelocityState) :
    ‖thirdFullSpectralVelocityLowRadialApply244 R U -
        thirdFullSpectralVelocityLowRadialApply244 R V‖ ≤
      thirdFullFiniteBandH3WeightCeiling244 R *
        ‖(fun j : Fin 3 => h3SpectralScalarRawFourierL2 (U j)) -
          (fun j : Fin 3 => h3SpectralScalarRawFourierL2 (V j))‖ := by
  have hLowSub :
      thirdFullSpectralVelocityLowRadialApply244 R U -
        thirdFullSpectralVelocityLowRadialApply244 R V =
      thirdFullSpectralVelocityLowRadialApply244 R (U - V) := by
    have hHigh := thirdFullSpectralVelocityHighRadialApply_add244 R (U - V) V
    rw [sub_add_cancel] at hHigh
    unfold thirdFullSpectralVelocityLowRadialApply244
    rw [hHigh]
    abel
  rw [hLowSub]
  have hRawSub :
      (fun j : Fin 3 => h3SpectralScalarRawFourierL2 ((U - V) j)) =
        (fun j : Fin 3 => h3SpectralScalarRawFourierL2 (U j)) -
          (fun j : Fin 3 => h3SpectralScalarRawFourierL2 (V j)) := by
    funext j
    simp only [Pi.sub_apply, h3SpectralScalarRawFourierL2_sub]
  simpa only [hRawSub] using
    thirdFullSpectralVelocityLowRadial_norm_le_raw244 R (U - V)

end
end PrimeTensor.FirstMonomialTriad
