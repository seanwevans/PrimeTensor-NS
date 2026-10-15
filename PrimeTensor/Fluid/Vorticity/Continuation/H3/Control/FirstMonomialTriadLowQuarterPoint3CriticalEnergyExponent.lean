import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullEnergyBarrier
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The half-energy exponent forced by cubic first-monomial scaling

For the explicitly constructed real solenoidal Schwartz velocity, the positive
signed first monomial is cubic in amplitude. Its complete unnormalized H3
energy and the fourth-derivative L2 dissipation are quadratic in amplitude.

This module excludes every fixed positive coefficient times a subcritical
(nonnegative exponent strictly below one half) energy weight multiplied by
quadratic dissipation. The proof uses real-power growth, with no PDE path
assumption. We use the absolute values of both quadratic quantities, yielding
a stronger inequality than a signed quadratic budget and avoiding any hidden
nonnegativity hypothesis on the abstract scaling lemma.

The endpoint exponent 1/2 is NOT shown to be sufficient. Energy-dependent
interpolation bounds and the complete Navier--Stokes energy balance remain
separate mathematical questions.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean Filter

noncomputable section

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

-- The canonical Fourier carrier is a EuclideanSpace over Axis Depth.three;
-- its normed-space and Schwartz instances require this local finite index.
noncomputable local instance axisFintypeQuarterCriticalEnergy (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Scalar sharpness lemma: a positive cubic amplitude defeats any
quadratic form multiplied by a normalized quadratic-energy weight raised to
an exponent strictly below one half. The quadratic coefficients need not be
assumed nonnegative because absolute values are taken. -/
private theorem exists_amplitude_exceeding_subcritical_power
    (M E D C θ : ℝ) (hM : 0 < M) (hC : 0 ≤ C)
    (hθ0 : 0 ≤ θ) (hθhalf : θ < 1 / 2) :
    ∃ a : ℝ, 1 ≤ a ∧
      C * (1 + a ^ 2 * |E|) ^ θ * (a ^ 2 * |D|) < a ^ 3 * M := by
  let H : ℝ := 1 + |E|
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hDelta : 0 < 1 - 2 * θ := by linarith
  let K : ℝ := C * H ^ θ * |D| / M + 1
  obtain ⟨a, ha, hLarge⟩ :=
    ((eventually_ge_atTop (1 : ℝ)).and
      ((tendsto_rpow_atTop hDelta).eventually_gt_atTop K)).exists
  have ha_pos : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have ha2 : 1 ≤ a ^ 2 := by nlinarith [sq_nonneg (a - 1)]
  have hInput : 0 ≤ 1 + a ^ 2 * |E| := by positivity
  have hInputBound : 1 + a ^ 2 * |E| ≤ a ^ 2 * H := by
    dsimp [H]
    nlinarith
  have hPowerBound :
      (1 + a ^ 2 * |E|) ^ θ ≤ (a ^ 2 * H) ^ θ :=
    Real.rpow_le_rpow hInput hInputBound hθ0
  have hPowerRewrite : (a ^ 2 * H) ^ θ = a ^ (2 * θ) * H ^ θ := by
    calc
      _ = (a ^ 2) ^ θ * H ^ θ := Real.mul_rpow (sq_nonneg a) hH
      _ = a ^ (2 * θ) * H ^ θ := by
        rw [← Real.rpow_natCast_mul ha_pos.le 2 θ]
        norm_num
  have hCoefficient : C * H ^ θ * |D| < a ^ (1 - 2 * θ) * M := by
    have h' : C * H ^ θ * |D| / M < a ^ (1 - 2 * θ) := by
      change C * H ^ θ * |D| / M + 1 < a ^ (1 - 2 * θ) at hLarge
      linarith
    have h'' := mul_lt_mul_of_pos_right h' hM
    simpa only [div_mul_cancel₀ _ hM.ne'] using h''
  have hPowerPos : 0 < a ^ (2 * θ) := Real.rpow_pos_of_pos ha_pos _
  have hSubcritical :
      C * (1 + a ^ 2 * |E|) ^ θ * |D| < a * M := by
    calc
      _ ≤ C * (a ^ 2 * H) ^ θ * |D| := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hPowerBound hC) (abs_nonneg D)
      _ = (C * H ^ θ * |D|) * a ^ (2 * θ) := by
        rw [hPowerRewrite]
        ring
      _ < (a ^ (1 - 2 * θ) * M) * a ^ (2 * θ) :=
        mul_lt_mul_of_pos_right hCoefficient hPowerPos
      _ = (a ^ (1 - 2 * θ) * a ^ (2 * θ)) * M := by ring
      _ = a * M := by
        rw [← Real.rpow_add ha_pos]
        have he : (1 - 2 * θ) + 2 * θ = 1 := by ring
        rw [he, Real.rpow_one]
  have hPositiveSq : 0 < a ^ 2 := pow_pos ha_pos _
  have hAmplified := mul_lt_mul_of_pos_left hSubcritical hPositiveSq
  refine ⟨a, ha, ?_⟩
  calc
    C * (1 + a ^ 2 * |E|) ^ θ * (a ^ 2 * |D|) =
        a ^ 2 * (C * (1 + a ^ 2 * |E|) ^ θ * |D|) := by ring
    _ < a ^ 2 * (a * M) := hAmplified
    _ = a ^ 3 * M := by ring

set_option maxHeartbeats 800000

/-- Sharp *necessary* exponent from the concrete real solenoidal Schwartz
witness: a fixed coefficient times a nonnegative power strictly below 1/2 of
the normalized quadratic H3 energy, times quadratic top dissipation, fails.
The absolute-valued budget on the left is at least as permissive as the
corresponding unsigned quadratic quantities. -/
theorem lowNormalQuarter_exists_amplitude_exceeding_subcritical_energy_weight
    (C θ : ℝ) (hC : 0 ≤ C) (hθ0 : 0 ≤ θ) (hθhalf : θ < 1 / 2) :
    ∃ ρ : ℝ, ∃ hρ : 0 < ρ, ∃ a : ℝ, 0 < a ∧
      C * (1 + |lowNormalRealSchwartzH3EnergyQuadratic
          (fun j : A3 => a • lowNormalQuarterOppositeSchwartzVelocity ρ hρ j)|) ^ θ *
        |lowNormalRealSchwartzH3TopDissipation
          (fun j : A3 => a • lowNormalQuarterOppositeSchwartzVelocity ρ hρ j)| <
      lowNormalRealSchwartzPoint3Monomial
        (fun j : A3 => a • lowNormalQuarterOppositeSchwartzVelocity ρ hρ j) := by
  obtain ⟨ρ, hρ, _, hM⟩ := lowNormalQuarterPoint3_exists_both_firstMonomial_signs
  let f : A3 → SchwartzMap V3 ℝ := lowNormalQuarterOppositeSchwartzVelocity ρ hρ
  let M : ℝ := lowNormalRealSchwartzPoint3Monomial f
  let E : ℝ := lowNormalRealSchwartzH3EnergyQuadratic f
  let D : ℝ := lowNormalRealSchwartzH3TopDissipation f
  have hMpos : 0 < M := hM
  obtain ⟨a, ha, hExceed⟩ :=
    exists_amplitude_exceeding_subcritical_power M E D C θ hMpos hC hθ0 hθhalf
  have ha_pos : 0 < a := lt_of_lt_of_le zero_lt_one ha
  refine ⟨ρ, hρ, a, ha_pos, ?_⟩
  change C * (1 + |lowNormalRealSchwartzH3EnergyQuadratic
        (fun j : A3 => a • f j)|) ^ θ *
      |lowNormalRealSchwartzH3TopDissipation (fun j : A3 => a • f j)| <
    lowNormalRealSchwartzPoint3Monomial (fun j : A3 => a • f j)
  rw [lowNormalRealSchwartzH3EnergyQuadratic_real_smul,
    lowNormalRealSchwartzH3TopDissipation_real_smul,
    lowNormalRealSchwartzPoint3Monomial_real_smul]
  simp only [abs_mul, abs_of_nonneg (sq_nonneg a)]
  exact hExceed

end
end PrimeTensor.FirstMonomialTriad
