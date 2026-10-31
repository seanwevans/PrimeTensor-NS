import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualHighpassSourceDrivenFullExtendedCosts
import Mathlib.Tactic

/-!
# Exact extended window costs and local width-budget compression

The previously committed full-physical-H³ source-driven windows have lower
bounds expressed as extended integrals of a *constant* height. Here the
constant integral is evaluated exactly as height times physical width in
`ENNReal` (no measurability of the dissipation density is required).

A separate elementary budget theorem converts a finite upper bound on the
extended H³ integral of one window to the explicit necessary upper bound
`δ ≤ C/M` for a positive floor M. This is a quantitative compression
*necessity* under a local budget, not a lower bound on persistence widths.
No terminal finiteness or full-dissipation continuity is assumed.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- The extended integral of a constant height over a physical Ioc window
is exactly the positive part of the height times its positive width. -/
theorem h3Critical_extendedConstantWindow_eq_heightWidth
    (t δ M : ℝ) (hδ : 0 ≤ δ) :
    (∫⁻ _s in Set.Ioc t (t + δ), ENNReal.ofReal M ∂volume) =
      ENNReal.ofReal M * ENNReal.ofReal δ := by
  rw [setLIntegral_const, Real.volume_Ioc]
  congr 1
  congr 1
  ring

/-- A local finite extended H³ cost budget forces an *upper* bound on the
width of a window where the nonnegative physical density exceeds M > 0.
No measurability or ordinary interval-integrability premise is needed. -/
theorem h3Critical_extendedWindowBudget_width_le
    (f : ℝ → ℝ) (t δ M C : ℝ)
    (hδ : 0 ≤ δ) (hM : 0 < M) (hC : 0 ≤ C)
    (hFloor : ∀ s : ℝ, s ∈ Set.Icc t (t + δ) → M ≤ f s)
    (hBudget :
      (∫⁻ s in Set.Ioc t (t + δ), ENNReal.ofReal (f s) ∂volume) ≤
        ENNReal.ofReal C) :
    δ ≤ C / M := by
  have hCost :
      ENNReal.ofReal M * ENNReal.ofReal δ ≤ ENNReal.ofReal C := by
    calc
      ENNReal.ofReal M * ENNReal.ofReal δ =
          (∫⁻ _s in Set.Ioc t (t + δ), ENNReal.ofReal M ∂volume) :=
        (h3Critical_extendedConstantWindow_eq_heightWidth t δ M hδ).symm
      _ ≤ (∫⁻ s in Set.Ioc t (t + δ), ENNReal.ofReal (f s) ∂volume) :=
        h3Critical_extendedWindowCost_of_pointwiseFloor f t δ M hFloor
      _ ≤ ENNReal.ofReal C := hBudget
  have hReal : M * δ ≤ C := by
    apply (ENNReal.ofReal_le_ofReal_iff hC).mp
    rw [ENNReal.ofReal_mul hM.le]
    exact hCost
  apply (le_div_iff₀ hM).2
  nlinarith only [hReal]

/-- On the pre-existing source-driven, separated physical windows, the
full-physical-H³ extended costs dominate the **explicit** ENNReal
height-times-width costs, with no additional dissipation regularity
premise. If an individual selected window has a finite extended-cost
budget, its width must obey the quantitative upper bound C/M. -/
theorem h3Critical_noL2Trace_sourceDriven_explicitFullWidthCosts
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (c ρ σ K M : ℕ → ℝ)
    (hc : ∀ n, c n ∈ Set.Ioo b T)
    (hcLimit : Tendsto c atTop (𝓝 T))
    (hρ : ∀ n, 0 ≤ ρ n)
    (hσ : ∀ n, 0 ≤ σ n) :
    ∃ i : Fin 3, ∃ t δ : ℕ → ℝ, ∃ v : ℕ → ℕ,
      StrictMono v ∧
      Tendsto (fun k : ℕ => t (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → t (v k) + δ (v k) < t (v l)) ∧
      (∀ k : ℕ, 0 < δ (v k) ∧ t (v k) + δ (v k) < T ∧
        ∀ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + δ (v k)) →
          M (v k) < velocityH3DissipationAt u s) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m,
          ENNReal.ofReal (M (v k)) * ENNReal.ofReal (δ (v k))) ≤
        ∑ k ∈ Finset.range m,
          ∫⁻ s in Set.Ioc (t (v k)) (t (v k) + δ (v k)),
            ENNReal.ofReal (velocityH3DissipationAt u s) ∂volume) ∧
      (∀ k : ℕ, 0 < M (v k) →
        ∀ C : ℝ, 0 ≤ C →
          (∫⁻ s in Set.Ioc (t (v k)) (t (v k) + δ (v k)),
            ENNReal.ofReal (velocityH3DissipationAt u s) ∂volume) ≤
              ENNReal.ofReal C →
          δ (v k) ≤ C / M (v k)) := by
  obtain ⟨i, t, δ, v, hMono, hLimit, hSeparate, hWindows,
      hHighCosts, hFullCosts⟩ :=
    h3Critical_noL2Trace_sourceDriven_disjointExtendedFullDissipationCosts
      hH3 hClass b hb hNoTrace c ρ σ K M hc hcLimit hρ hσ
  refine ⟨i, t, δ, v, hMono, hLimit, hSeparate, ?_, ?_, ?_⟩
  · intro k
    exact ⟨(hWindows k).2.1, (hWindows k).2.2.1,
      (hWindows k).2.2.2⟩
  · intro m
    calc
      (∑ k ∈ Finset.range m,
          ENNReal.ofReal (M (v k)) * ENNReal.ofReal (δ (v k))) =
          ∑ k ∈ Finset.range m,
            ∫⁻ _s in Set.Ioc (t (v k)) (t (v k) + δ (v k)),
              ENNReal.ofReal (M (v k)) ∂volume := by
                apply Finset.sum_congr rfl
                intro k _hk
                exact (h3Critical_extendedConstantWindow_eq_heightWidth
                  (t (v k)) (δ (v k)) (M (v k))
                  (hWindows k).2.1.le).symm
      _ ≤ ∑ k ∈ Finset.range m,
          ∫⁻ s in Set.Ioc (t (v k)) (t (v k) + δ (v k)),
            ENNReal.ofReal
              (h3PathActualHighRadialDissipation244 (σ (v k))
                (h3AuditActualSpectralVelocityTotal hH3 s)) ∂volume :=
        hHighCosts m
      _ ≤ ∑ k ∈ Finset.range m,
          ∫⁻ s in Set.Ioc (t (v k)) (t (v k) + δ (v k)),
            ENNReal.ofReal (velocityH3DissipationAt u s) ∂volume :=
        hFullCosts m
  · intro k hM C hC hBudget
    exact h3Critical_extendedWindowBudget_width_le
      (velocityH3DissipationAt u) (t (v k)) (δ (v k)) (M (v k)) C
      (hWindows k).2.1.le hM hC
      (fun s hs => ((hWindows k).2.2.2 s hs).le)
      hBudget

end
end PrimeTensor.Bridge.Euclidean
