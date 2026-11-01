import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessGradientEnergyGapSpike
import Mathlib.Tactic

/-!
# Exact endpoint H³ energy imposes a calibrated quartic source-window gate

On a genuinely positive source-excess window, the accepted signed-energy
competition gives a Riccati energy observation or an actual endpoint loss
`E(end) + H * δ ≤ E(start)`. Since `E(end) ≥ 1`, a drain window has only
`E(start)-1` available. Combining this with the *original* lower calibrated
width `min(w,R⁻⁴) ≤ δ` gives a forced alternative: the original geometric
window compresses, or the actual PDE-calibrated radius grows at least as the
fourth root of `H/(E(start)-1)`.

The cofinal result reuses the original source witnesses, including their
selected local PDE coefficients A and B. Neither a uniform energy ceiling,
a non-collapsing window, nor a divergent source charge is inserted.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- A positive actual endpoint loss exhausts at most the available physical
energy above its normalized floor 1. The calibrated quartic window cannot
be both long and low-frequency without violating this energy accounting.
Unlike the earlier physical viscous-charge gate, no time integral of D is
assumed finite. -/
theorem h3Critical_scalar_endpointEnergy_forces_calibratedQuarticGate
    (Einitial Eend H δ w R : ℝ)
    (hH : 0 < H) (hδ : 0 < δ) (hR : 0 < R)
    (hWidth : min w (1 / R ^ 4) ≤ δ)
    (hDrain : Eend + H * δ ≤ Einitial)
    (hEndEnergy : 1 ≤ Eend) :
    1 < Einitial ∧
      (w ≤ (Einitial - 1) / H ∨
        H / (Einitial - 1) ≤ R ^ 4) := by
  have hSpent : 0 < H * δ := mul_pos hH hδ
  have hHead : 1 < Einitial := by
    linarith only [hSpent, hDrain, hEndEnergy]
  have hCharge : H * min w (1 / R ^ 4) ≤ Einitial - 1 := by
    calc
      H * min w (1 / R ^ 4) ≤ H * δ :=
        mul_le_mul_of_nonneg_left hWidth hH.le
      _ ≤ Einitial - 1 := by
        linarith only [hDrain, hEndEnergy]
  exact ⟨hHead,
    h3Critical_calibratedQuarticWidth_finiteCharge_forces_compression
      w R H (Einitial - 1) hR hH (sub_pos.mpr hHead) hCharge⟩

/-- If an external energy ceiling U is available and the original geometric
window is too wide to account for the deficit, the calibrated radius must
carry the remaining source height. All ceiling/noncompression assumptions
are explicit. -/
theorem h3Critical_scalar_noncompressedEnergy_forces_quarticRadius
    (Einitial U H w R : ℝ)
    (hH : 0 < H) (hR : 0 < R)
    (hCeiling : Einitial ≤ U)
    (hNoCompression : U - 1 < H * w)
    (hGate : 1 < Einitial ∧
      (w ≤ (Einitial - 1) / H ∨
        H / (Einitial - 1) ≤ R ^ 4)) :
    H ≤ (U - 1) * R ^ 4 := by
  rcases hGate with ⟨hHead, hBranch⟩
  rcases hBranch with hShort | hRadius
  · have hShortCharge : H * w ≤ Einitial - 1 := by
      calc
        H * w = w * H := mul_comm H w
        _ ≤ Einitial - 1 := (le_div_iff₀ hH).mp hShort
    linarith only [hShortCharge, hCeiling, hNoCompression]
  · have hNecessary : H ≤ (Einitial - 1) * R ^ 4 := by
      calc
        H ≤ R ^ 4 * (Einitial - 1) :=
          (div_le_iff₀ (sub_pos.mpr hHead)).mp hRadius
        _ = (Einitial - 1) * R ^ 4 := mul_comm _ _
    have hScaled : (Einitial - 1) * R ^ 4 ≤ (U - 1) * R ^ 4 :=
      mul_le_mul_of_nonneg_right (sub_le_sub_right hCeiling 1)
        (pow_nonneg hR.le 4)
    exact hNecessary.trans hScaled

/-- On exactly the same cofinal quintic-source windows, a genuine
Riccati-energy observation occurs, or the physical initial H³ energy at
that window strictly exceeds 1 and pays either geometric clock compression
or a *fourth-power calibrated physical frequency demand*.

The A and B coefficients are the same actual local PDE/spectral coefficients
selected by the previous physical quintic source theorem, not new free
parameters. The statement does not assert any endpoint energy ceiling. -/
theorem h3Critical_noL2Trace_cofinalQuintic_endpointEnergyQuarticGate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (c ρ σ M q : ℕ → ℝ)
    (hc : ∀ n, c n ∈ Set.Ioo b T)
    (hcLimit : Tendsto c atTop (𝓝 T))
    (hρ : ∀ n, 0 ≤ ρ n)
    (hσ : ∀ n, 0 ≤ σ n)
    (hM : ∀ n, 0 ≤ M n)
    (hq : ∀ n, 0 < q n) :
    ∃ t w : ℕ → ℝ, ∃ v : ℕ → ℕ,
    ∃ A B δ : ℕ → ℝ,
      StrictMono v ∧
      Tendsto (fun k : ℕ => t (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → t (v k) + δ k < t (v l)) ∧
      (∀ k : ℕ,
        0 < δ k ∧
        min (w (v k))
          (1 / (h3CriticalSourcePeakSquareRootRadius
            (σ (v k)) (4 * q (v k)) (A k) (B k)) ^ 4) ≤ δ k ∧
        ((∃ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + δ k) ∧
            h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) <
              h3PathSqrtEnergyRiccatiCoefficient *
                Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s) ∨
          (1 < velocityH3EnergyAt u (t (v k)) ∧
            (w (v k) ≤
                (velocityH3EnergyAt u (t (v k)) - 1) /
                  h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) ∨
              h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) /
                (velocityH3EnergyAt u (t (v k)) - 1) ≤
                  (h3CriticalSourcePeakSquareRootRadius
                    (σ (v k)) (4 * q (v k)) (A k) (B k)) ^ 4)))) := by
  obtain ⟨t, w, v, A, B, _R, δ, hv, hLimit,
      hSeparated, hWindows, _hReplenish, _hCosts, _hCostGate⟩ :=
    h3Critical_noL2Trace_cofinalQuintic_endpointDrain_or_gapTransport
      hH3 hClass b hb hNoTrace c ρ σ M q hc hcLimit hρ hσ hM hq
  refine ⟨t, w, v, A, B, δ, hv, hLimit, hSeparated, ?_⟩
  intro k
  obtain ⟨_hStart, _hw, _hEnd, _hR, hδ, _hδw,
      hWidth, hAlt⟩ := hWindows k
  have hκ : 0 < 3 * (3 + h3AuditInitialLerayEnergyCoefficient) := by
    have hCoeff := h3AuditInitialLerayEnergyCoefficient_nonneg
    positivity
  have hHeight : 0 < h3CriticalSourceExcessEnhancedFloor
      (M (v k)) (q (v k)) := by
    dsimp only [h3CriticalSourceExcessEnhancedFloor]
    exact add_pos_of_nonneg_of_pos (hM (v k))
      (div_pos (hq (v k)) hκ)
  have hP : 0 < 4 * q (v k) :=
    mul_pos (by norm_num) (hq (v k))
  have hRad : 0 < h3CriticalSourcePeakSquareRootRadius
      (σ (v k)) (4 * q (v k)) (A k) (B k) := by
    have hS : 0 ≤ Real.sqrt ((A k) ^ 2 * B k) :=
      Real.sqrt_nonneg _
    have hDiv : 0 ≤ Real.sqrt ((A k) ^ 2 * B k) / (4 * q (v k)) :=
      div_nonneg hS hP.le
    have hMax : (1 : ℝ) ≤ max 1 (σ (v k)) := le_max_left _ _
    dsimp only [h3CriticalSourcePeakSquareRootRadius]
    linarith only [hDiv, hMax]
  refine ⟨hδ, hWidth, ?_⟩
  rcases hAlt with hLarge | hDrain
  · exact Or.inl hLarge
  · right
    exact h3Critical_scalar_endpointEnergy_forces_calibratedQuarticGate
      (velocityH3EnergyAt u (t (v k)))
      (velocityH3EnergyAt u (t (v k) + δ k))
      (h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)))
      (δ k) (w (v k))
      (h3CriticalSourcePeakSquareRootRadius
        (σ (v k)) (4 * q (v k)) (A k) (B k))
      hHeight hδ hRad hWidth hDrain
      (one_le_velocityH3EnergyAt u (t (v k) + δ k))

end
end PrimeTensor.Bridge.Euclidean
