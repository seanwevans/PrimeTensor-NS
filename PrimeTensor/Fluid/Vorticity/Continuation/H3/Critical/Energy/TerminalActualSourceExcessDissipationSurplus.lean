import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourcePeakSquareRootQuarticCalibration
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualHighpassSourceDrivenWindows
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualHighpassSourceDrivenExtendedWidthBudget
import Mathlib.Tactic

/-!
# Actual source excess pays physical high-radial H³ dissipation surplus

The kinetic-anchored projected Fourier-source estimate is affine in the
ACTUAL high-radial viscous H³ dissipation. Subtracting the EXACT source-driven
kinetic barrier (not a generic terminal norm ceiling) yields a quantitative
coercivity estimate: every unit of source excess above the barrier requires
at least 1/(3*(3+C_L)) units of simultaneous physical high-radial
H³ dissipation in excess of the specified threshold.

Unlike the previous qualitative source-driven windows, these cofinal windows
retain an arbitrarily chosen additional source-excess profile Q(n). At every
actual time on each selected separated window, the physical dissipation is
strictly greater than M(n)+Q(n)/(3*(3+C_L)), and extended Lebesgue full-H³
costs pay the stronger floor. Widths and resulting global costs are not
asserted to be terminal-uniform or divergent.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeSourceExcessSurplus
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceSourceExcessSurplus :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Quantitative same-time physical coercivity: the TRUE projected highpass
source norm above its kinetic-anchored threshold is at most a fixed linear
multiple of the TRUE high-radial H³ dissipation surplus. No positivity of
the excess, and no terminal temporal or spatial bound, is needed. -/
theorem h3Critical_actualHighpassSourceExcess_le_highRadialDissipationSurplus
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ σ : ℝ) (hσ : 0 ≤ σ) (i : Fin 3)
    (t : ℝ) (ht : t ∈ Set.Ioo b T) (M : ℝ) :
    ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖ -
        h3CriticalSourceDrivenHighDissipationBarrier
          (velocityH3Energy0At u b) σ M ≤
      (3 * (3 + h3AuditInitialLerayEnergyCoefficient)) *
        (h3PathActualHighRadialDissipation244 σ
          (h3AuditActualSpectralVelocityTotal hH3 t) - M) := by
  let K : ℝ := 3 + h3AuditInitialLerayEnergyCoefficient
  let L : ℝ := σ ^ 2 *
    (h3TerminalRadialSobolevWeightSquareCeiling σ * velocityH3Energy0At u b)
  let D : ℝ := h3PathActualHighRadialDissipation244 σ
    (h3AuditActualSpectralVelocityTotal hH3 t)
  let N : ℝ := ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖
  let B : ℝ := h3CriticalSourceDrivenHighDissipationBarrier
    (velocityH3Energy0At u b) σ M
  have hSource : N ≤ K * (1 + 6 * velocityH3Energy0At u b + 3 * (L + D)) := by
    dsimp only [N, K, L, D]
    exact h3Critical_actualHighpassFourierSource_norm_le_highRadialDissipation
      hH3 hClass b hb ρ σ hσ i t ht
  have hBarrier :
      K * (1 + 6 * velocityH3Energy0At u b + 3 * (L + M)) ≤ B := by
    dsimp only [B, h3CriticalSourceDrivenHighDissipationBarrier, K, L]
    exact le_max_left _ _
  have hDifference :
      N - B ≤
        K * (1 + 6 * velocityH3Energy0At u b + 3 * (L + D)) -
        K * (1 + 6 * velocityH3Energy0At u b + 3 * (L + M)) := by
    linarith only [hSource, hBarrier]
  calc
    N - B ≤ K * (1 + 6 * velocityH3Energy0At u b + 3 * (L + D)) -
        K * (1 + 6 * velocityH3Energy0At u b + 3 * (L + M)) := hDifference
    _ = (3 * K) * (D - M) := by ring

/-- Every prescribed genuine highpass source excess Q at a strict time
forces an explicit strictly larger actual physical dissipation floor.
The coefficient is universal for the fixed H³ commutator/physical source
majorant; it does not depend on either Fourier cutoff. -/
theorem h3Critical_strictSourceExcess_forces_quantitativeHighRadialSurplus
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ σ : ℝ) (hσ : 0 ≤ σ) (i : Fin 3)
    (t : ℝ) (ht : t ∈ Set.Ioo b T) (M Q : ℝ)
    (hExcess :
      h3CriticalSourceDrivenHighDissipationBarrier
        (velocityH3Energy0At u b) σ M + Q <
      ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖) :
    M + Q / (3 * (3 + h3AuditInitialLerayEnergyCoefficient)) <
      h3PathActualHighRadialDissipation244 σ
        (h3AuditActualSpectralVelocityTotal hH3 t) := by
  let κ : ℝ := 3 * (3 + h3AuditInitialLerayEnergyCoefficient)
  have hκ : 0 < κ := by
    dsimp only [κ]
    have hCL := h3AuditInitialLerayEnergyCoefficient_nonneg
    positivity
  have hBound := h3Critical_actualHighpassSourceExcess_le_highRadialDissipationSurplus
    hH3 hClass b hb ρ σ hσ i t ht M
  have hStrict : Q < κ *
      (h3PathActualHighRadialDissipation244 σ
        (h3AuditActualSpectralVelocityTotal hH3 t) - M) := by
    dsimp only [κ]
    linarith only [hBound, hExcess]
  have hDiv : Q / κ <
      h3PathActualHighRadialDissipation244 σ
        (h3AuditActualSpectralVelocityTotal hH3 t) - M := by
    apply (div_lt_iff₀ hκ).2
    simpa only [mul_comm] using hStrict
  dsimp only [κ] at hDiv
  linarith only [hDiv]

/-- On a source-driven selected window, a squared source-mass floor
(B+Q)² quantitatively enforces the EXTRA high-H³ dissipation floor
M+Q/κ at EVERY physical time, not just at the initial source peak. -/
theorem h3Critical_sourceMassExcess_forces_quantitativeHighRadialSurplus
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ σ : ℝ) (hσ : 0 ≤ σ) (i : Fin 3)
    (t : ℝ) (ht : t ∈ Set.Ioo b T) (M Q : ℝ) (hQ : 0 ≤ Q)
    (hMass :
      (h3CriticalSourceDrivenHighDissipationBarrier
        (velocityH3Energy0At u b) σ M + Q) ^ 2 <
      ∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
        ‖h3CriticalActualProjectedFourierSource hH3 i t ξ‖ ^ 2 ∂volume) :
    M + Q / (3 * (3 + h3AuditInitialLerayEnergyCoefficient)) <
      h3PathActualHighRadialDissipation244 σ
        (h3AuditActualSpectralVelocityTotal hH3 t) := by
  let F : H3FourierComplexL2 :=
    h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t
  let B : ℝ :=
    h3CriticalSourceDrivenHighDissipationBarrier
      (velocityH3Energy0At u b) σ M
  have hB : 0 ≤ B := le_max_right _ _
  have hBQ : 0 ≤ B + Q := add_nonneg hB hQ
  have hNormSq : ‖F‖ ^ 2 =
      ∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
        ‖h3CriticalActualProjectedFourierSource hH3 i t ξ‖ ^ 2 ∂volume := by
    dsimp only [F, h3CriticalActualProjectedHighpassFourierSource]
    exact h3Critical_fourierSharpHighpass_norm_sq_eq_integral
      ρ (h3CriticalActualProjectedFourierSource hH3 i t)
  have hSq : (B + Q) ^ 2 < ‖F‖ ^ 2 := by
    rw [hNormSq]
    exact hMass
  have hNorm : 0 ≤ ‖F‖ := norm_nonneg _
  have hExcess : B + Q < ‖F‖ := by
    nlinarith only [hSq, hBQ, hNorm]
  exact h3Critical_strictSourceExcess_forces_quantitativeHighRadialSurplus
    hH3 hClass b hb ρ σ hσ i t ht M Q hExcess

/-- Arbitrarily prescribed additional source-excess heights Q(n) yield
cofinal, separated ACTUAL Fourier-source windows with explicit enhanced
physical high-radial H³ dissipation floors. Every full physical H³
extended cost pays the stronger (M+Q/κ)-times-width charge.

This requires the explicitly stated no-physical-L²-terminal-trace branch,
but neither a source ceiling nor a uniform terminal lower window width.
In particular no divergence of the weighted width sum is inferred. -/
theorem h3Critical_noL2Trace_sourceExcess_disjointEnhancedFullDissipationCosts
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (c ρ σ M Q : ℕ → ℝ)
    (hc : ∀ n, c n ∈ Set.Ioo b T)
    (hcLimit : Tendsto c atTop (𝓝 T))
    (hρ : ∀ n, 0 ≤ ρ n)
    (hσ : ∀ n, 0 ≤ σ n)
    (hM : ∀ n, 0 ≤ M n)
    (hQ : ∀ n, 0 ≤ Q n) :
    ∃ i : Fin 3, ∃ t δ : ℕ → ℝ, ∃ v : ℕ → ℕ,
      StrictMono v ∧
      Tendsto (fun k : ℕ => t (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → t (v k) + δ (v k) < t (v l)) ∧
      (∀ k : ℕ,
        t (v k) ∈ Set.Ioo (c (v k)) T ∧
        0 < δ (v k) ∧ t (v k) + δ (v k) < T ∧
        (∀ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + δ (v k)) →
          h3CriticalSourceDrivenHighDissipationBarrier
            (velocityH3Energy0At u b) (σ (v k)) (M (v k)) + Q (v k) <
            ‖h3CriticalActualProjectedHighpassFourierSource hH3
              (ρ (v k)) i s‖ ∧
          M (v k) + Q (v k) /
            (3 * (3 + h3AuditInitialLerayEnergyCoefficient)) <
            h3PathActualHighRadialDissipation244 (σ (v k))
              (h3AuditActualSpectralVelocityTotal hH3 s))) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m,
          ENNReal.ofReal (M (v k) + Q (v k) /
            (3 * (3 + h3AuditInitialLerayEnergyCoefficient))) *
            ENNReal.ofReal (δ (v k))) ≤
        ∑ k ∈ Finset.range m,
          ∫⁻ s in Set.Ioc (t (v k)) (t (v k) + δ (v k)),
            ENNReal.ofReal (velocityH3DissipationAt u s) ∂volume) := by
  let B : ℕ → ℝ := fun n =>
    h3CriticalSourceDrivenHighDissipationBarrier
      (velocityH3Energy0At u b) (σ n) (M n)
  let Ksource : ℕ → ℝ := fun n => (B n + Q n) ^ 2
  obtain ⟨i, t, δ, v, hv, hLimit, hSeparated, hWindows, _, _⟩ :=
    h3Critical_noL2Trace_sourceDriven_profileDisjointWindows
      hH3 hClass b hb hNoTrace c ρ σ Ksource M hc hcLimit hρ hσ
  have hTime (k : ℕ) (s : ℝ)
      (hs : s ∈ Set.Icc (t (v k)) (t (v k) + δ (v k))) :
      s ∈ Set.Ioo b T := by
    exact ⟨lt_of_lt_of_le
        (lt_trans (hc (v k)).1 (hWindows k).1.1) hs.1,
      lt_of_le_of_lt hs.2 (hWindows k).2.2.1⟩
  have hEnhanced (k : ℕ) (s : ℝ)
      (hs : s ∈ Set.Icc (t (v k)) (t (v k) + δ (v k))) :
      B (v k) + Q (v k) <
        ‖h3CriticalActualProjectedHighpassFourierSource hH3
          (ρ (v k)) i s‖ ∧
      M (v k) + Q (v k) /
        (3 * (3 + h3AuditInitialLerayEnergyCoefficient)) <
        h3PathActualHighRadialDissipation244 (σ (v k))
          (h3AuditActualSpectralVelocityTotal hH3 s) := by
    let F : H3FourierComplexL2 :=
      h3CriticalActualProjectedHighpassFourierSource hH3 (ρ (v k)) i s
    have hB : 0 ≤ B (v k) := le_max_right _ _
    have hBQ : 0 ≤ B (v k) + Q (v k) :=
      add_nonneg hB (hQ (v k))
    have hMass := ((hWindows k).2.2.2.1 s hs).1
    have hNormSq : ‖F‖ ^ 2 =
        ∫ ξ in (h3TerminalRadialFrequencyBelow (ρ (v k)))ᶜ,
          ‖h3CriticalActualProjectedFourierSource hH3 i s ξ‖ ^ 2 ∂volume := by
      dsimp only [F, h3CriticalActualProjectedHighpassFourierSource]
      exact h3Critical_fourierSharpHighpass_norm_sq_eq_integral
        (ρ (v k)) (h3CriticalActualProjectedFourierSource hH3 i s)
    have hSq : (B (v k) + Q (v k)) ^ 2 < ‖F‖ ^ 2 := by
      rw [hNormSq]
      exact hMass
    have hNorm : 0 ≤ ‖F‖ := norm_nonneg _
    have hExcess : B (v k) + Q (v k) < ‖F‖ := by
      nlinarith only [hSq, hBQ, hNorm]
    have hD := h3Critical_strictSourceExcess_forces_quantitativeHighRadialSurplus
      hH3 hClass b hb (ρ (v k)) (σ (v k)) (hσ (v k)) i
      s (hTime k s hs) (M (v k)) (Q (v k)) hExcess
    exact ⟨hExcess, hD⟩
  refine ⟨i, t, δ, v, hv, hLimit, hSeparated, ?_, ?_⟩
  · intro k
    exact ⟨(hWindows k).1, (hWindows k).2.1,
      (hWindows k).2.2.1, fun s hs => hEnhanced k s hs⟩
  · intro m
    apply Finset.sum_le_sum
    intro k _hk
    have hLower :
        (∫⁻ _s in Set.Ioc (t (v k)) (t (v k) + δ (v k)),
          ENNReal.ofReal (M (v k) + Q (v k) /
            (3 * (3 + h3AuditInitialLerayEnergyCoefficient))) ∂volume) ≤
        ∫⁻ s in Set.Ioc (t (v k)) (t (v k) + δ (v k)),
          ENNReal.ofReal (velocityH3DissipationAt u s) ∂volume := by
      apply h3Critical_extendedWindowCost_of_pointwiseFloor
      intro s hs
      have hsClass : s ∈ Set.Ioo a T := by
        have hsTime := hTime k s hs
        exact ⟨lt_trans hb.1 hsTime.1, hsTime.2⟩
      exact (hEnhanced k s hs).2.le.trans
        (h3Critical_actualHighRadialDissipation_le_full
          hH3 hClass s hsClass (σ (v k)))
    calc
      ENNReal.ofReal (M (v k) + Q (v k) /
          (3 * (3 + h3AuditInitialLerayEnergyCoefficient))) *
          ENNReal.ofReal (δ (v k)) =
          (∫⁻ _s in Set.Ioc (t (v k)) (t (v k) + δ (v k)),
            ENNReal.ofReal (M (v k) + Q (v k) /
              (3 * (3 + h3AuditInitialLerayEnergyCoefficient))) ∂volume) :=
        (h3Critical_extendedConstantWindow_eq_heightWidth
          (t (v k)) (δ (v k))
          (M (v k) + Q (v k) /
            (3 * (3 + h3AuditInitialLerayEnergyCoefficient)))
          (hWindows k).2.1.le).symm
      _ ≤ ∫⁻ s in Set.Ioc (t (v k)) (t (v k) + δ (v k)),
          ENNReal.ofReal (velocityH3DissipationAt u s) ∂volume := hLower

end
end PrimeTensor.Bridge.Euclidean
