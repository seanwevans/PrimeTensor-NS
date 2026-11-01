import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourcePeakAutomaticQuarticPersistence
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualHighpassSourceDrivenExtendedWidthBudget
import Mathlib.Tactic

/-!
# Cofinal actual source peaks: constructive quartic persistence and physical cost

At each strict physical source peak, the projected momentum source and the
actual weighted H³ Fourier state have finite upper bounds on every chosen
closed interval inside (0,T). We obtain these bounds from the already proved
physical projected-momentum continuity and actual H³ spectral continuity,
not from any assumed terminal-uniform ceiling.

The automatic quartic source-drop obstruction then supplies a genuine
positive time width and a frequency radius at every selected cofinal source
peak. The new smaller windows inherit disjointness of the original cofinal
source-driven windows, and their *actual physical H³ dissipation* pays the
explicit ENNReal threshold-times-width cost.

Neither the Fourier radii nor the resulting persistence widths are asserted
to have terminal-uniform bounds. Summability or divergence of the concrete
weighted widths remains the next analytic obstruction.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeCofinalQuarticCosts
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceCofinalQuarticCosts :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The two compact-window ceilings in the automatic quartic persistence
lemma are consequences of the physical H³ path. In particular, they can be
eliminated from the interface for every fixed strict interval. -/
theorem h3Critical_strictSourcePeak_automaticPersistence_withoutLocalCeilingAssumptions
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ σ : ℝ) (hσ : 0 ≤ σ) (i : Fin 3)
    (t : ℝ) (ht : t ∈ Set.Ioo b T)
    (M δ₀ : ℝ) (hM : 0 ≤ M)
    (hδ₀ : 0 < δ₀) (hEnd : t + δ₀ < T)
    (hPeak : h3CriticalSourceDrivenHighDissipationBarrier
        (velocityH3Energy0At u b) σ M <
        ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖) :
    ∃ C E R δ : ℝ, 0 ≤ C ∧ 0 ≤ E ∧
      1 ≤ R ∧ σ ≤ R ∧ 0 < δ ∧ δ ≤ δ₀ ∧ R ^ 4 * δ ≤ 1 ∧
      (∀ s : ℝ, s ∈ Set.Icc t (t + δ₀) →
        ‖h3PathActualProjectedMomentumSource244 hH3 s‖ ≤ C ∧
        ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ≤ E) ∧
      (∀ s : ℝ, s ∈ Set.Icc t (t + δ) →
        M < h3PathActualHighRadialDissipation244 σ
          (h3AuditActualSpectralVelocityTotal hH3 s)) := by
  have htZero : 0 < t :=
    lt_trans hClass.terminal_start.1 (lt_trans hb.1 ht.1)
  have htPlus : t < t + δ₀ := by linarith only [hδ₀]
  obtain ⟨C, hC0, hC⟩ :=
    h3Path_actualProjectedMomentumSource_uniformL2OnStrict244
      hH3 htZero htPlus hEnd
  have hSub : Set.Icc t (t + δ₀) ⊆ Set.Ioo (0 : ℝ) T := by
    intro s hs
    exact ⟨lt_of_lt_of_le htZero hs.1, lt_of_le_of_lt hs.2 hEnd⟩
  have hContinuous : ContinuousOn
      (h3AuditActualSpectralVelocityTotal hH3)
      (Set.Icc t (t + δ₀)) :=
    (h3Audit_initialActualSpectralVelocity_continuousOn hH3).mono hSub
  obtain ⟨E₀, hE₀⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc t (t + δ₀))).exists_bound_of_continuousOn
      hContinuous
  let E : ℝ := max E₀ 0
  have hE0 : 0 ≤ E := le_max_right E₀ 0
  have hE : ∀ s : ℝ, s ∈ Set.Icc t (t + δ₀) →
      ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ≤ E := by
    intro s hs
    exact (hE₀ s hs).trans (le_max_left E₀ 0)
  obtain ⟨R, δ, hR, hσR, hδ, hδBase, hClock, hPersistent⟩ :=
    h3Critical_strictSourcePeak_automaticLocalHighDissipationPersistence
      hH3 hClass b hb ρ σ hσ i t ht M C E δ₀ hM
      hδ₀ hEnd hC hE hPeak
  refine ⟨C, E, R, δ, hC0, hE0, hR, hσR,
    hδ, hδBase, hClock, ?_, hPersistent⟩
  intro s hs
  exact ⟨hC s hs, hE s hs⟩

/-- A no-terminal-physical-L²-trace path possesses a FIXED actual Fourier
source coordinate and cofinal, separated source peaks. At every selected peak
the physical PDE itself produces local source/spectral ceilings, a radius,
and a strictly positive quartic persistence width. By shrinking inside the
old disjoint windows, the new physical windows remain disjoint.

Their real high-radial H³ dissipation floors are paid by the FULL physical
H³ viscous dissipation in extended Lebesgue integrals, without any
measurability assumption on an abstract endpoint spectral multiplier. -/
theorem h3Critical_noL2Trace_cofinalAutomaticQuarticWidths_and_fullDissipationCosts
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (c ρ σ M : ℕ → ℝ)
    (hc : ∀ n, c n ∈ Set.Ioo b T)
    (hcLimit : Tendsto c atTop (𝓝 T))
    (hρ : ∀ n, 0 ≤ ρ n)
    (hσ : ∀ n, 0 ≤ σ n)
    (hM : ∀ n, 0 ≤ M n) :
    ∃ i : Fin 3, ∃ t w : ℕ → ℝ, ∃ v : ℕ → ℕ,
    ∃ C E R δ : ℕ → ℝ,
      StrictMono v ∧
      Tendsto (fun k : ℕ => t (v k)) atTop (𝓝 T) ∧
      (∀ k : ℕ,
        t (v k) ∈ Set.Ioo (c (v k)) T ∧
        0 < w (v k) ∧ t (v k) + w (v k) < T ∧
        h3CriticalSourceDrivenHighDissipationBarrier
          (velocityH3Energy0At u b) (σ (v k)) (M (v k)) <
            ‖h3CriticalActualProjectedHighpassFourierSource hH3
              (ρ (v k)) i (t (v k))‖ ∧
        0 ≤ C k ∧ 0 ≤ E k ∧
        1 ≤ R k ∧ σ (v k) ≤ R k ∧
        0 < δ k ∧ δ k ≤ w (v k) ∧ R k ^ 4 * δ k ≤ 1 ∧
        (∀ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + w (v k)) →
          ‖h3PathActualProjectedMomentumSource244 hH3 s‖ ≤ C k ∧
          ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ≤ E k) ∧
        (∀ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + δ k) →
          M (v k) < h3PathActualHighRadialDissipation244 (σ (v k))
            (h3AuditActualSpectralVelocityTotal hH3 s))) ∧
      (∀ k l : ℕ, k < l → t (v k) + δ k < t (v l)) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m,
          ENNReal.ofReal (M (v k)) * ENNReal.ofReal (δ k)) ≤
        ∑ k ∈ Finset.range m,
          ∫⁻ s in Set.Ioc (t (v k)) (t (v k) + δ k),
            ENNReal.ofReal (velocityH3DissipationAt u s) ∂volume) := by
  obtain ⟨i, t, w, v, hv, hLimit, hSeparated, hWindows, _hGate⟩ :=
    h3Critical_noL2Trace_cofinalSourceWindows_postDropGradientGate
      hH3 hClass b hb hNoTrace c ρ σ M hc hcLimit hρ hσ
  have hSelected (k : ℕ) :
      ∃ C E R δ : ℝ, 0 ≤ C ∧ 0 ≤ E ∧
        1 ≤ R ∧ σ (v k) ≤ R ∧ 0 < δ ∧ δ ≤ w (v k) ∧
        R ^ 4 * δ ≤ 1 ∧
        (∀ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + w (v k)) →
          ‖h3PathActualProjectedMomentumSource244 hH3 s‖ ≤ C ∧
          ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ≤ E) ∧
        (∀ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + δ) →
          M (v k) < h3PathActualHighRadialDissipation244 (σ (v k))
            (h3AuditActualSpectralVelocityTotal hH3 s)) := by
    have ht : t (v k) ∈ Set.Ioo b T :=
      ⟨lt_trans (hc (v k)).1 (hWindows k).1.1, (hWindows k).1.2⟩
    exact h3Critical_strictSourcePeak_automaticPersistence_withoutLocalCeilingAssumptions
      hH3 hClass b hb (ρ (v k)) (σ (v k)) (hσ (v k)) i
      (t (v k)) ht (M (v k)) (w (v k)) (hM (v k))
      (hWindows k).2.1 (hWindows k).2.2.1 (hWindows k).2.2.2.1
  choose C E R δ hC0 hE0 hR hσR hδ hδw hClock hCeils hFloor
    using hSelected
  refine ⟨i, t, w, v, C, E, R, δ, hv, hLimit, ?_, ?_, ?_⟩
  · intro k
    exact ⟨(hWindows k).1, (hWindows k).2.1,
      (hWindows k).2.2.1, (hWindows k).2.2.2.1,
      hC0 k, hE0 k, hR k, hσR k, hδ k, hδw k,
      hClock k, hCeils k, hFloor k⟩
  · intro k l hkl
    have hEndSmall : t (v k) + δ k ≤ t (v k) + w (v k) :=
      add_le_add_right (hδw k) (t (v k))
    exact lt_of_le_of_lt hEndSmall (hSeparated k l hkl)
  · intro m
    apply Finset.sum_le_sum
    intro k _hk
    have hLower :
        (∫⁻ _s in Set.Ioc (t (v k)) (t (v k) + δ k),
          ENNReal.ofReal (M (v k)) ∂volume) ≤
        ∫⁻ s in Set.Ioc (t (v k)) (t (v k) + δ k),
          ENNReal.ofReal (velocityH3DissipationAt u s) ∂volume := by
      apply h3Critical_extendedWindowCost_of_pointwiseFloor
      intro s hs
      have hTime : s ∈ Set.Ioo a T := by
        have hStart : a < t (v k) :=
          lt_trans hb.1 (lt_trans (hc (v k)).1 (hWindows k).1.1)
        have hSmall : t (v k) + δ k ≤ t (v k) + w (v k) :=
          add_le_add_right (hδw k) (t (v k))
        exact ⟨lt_of_lt_of_le hStart hs.1,
          lt_of_le_of_lt (le_trans hs.2 hSmall) (hWindows k).2.2.1⟩
      exact (hFloor k s hs).le.trans
        (h3Critical_actualHighRadialDissipation_le_full
          hH3 hClass s hTime (σ (v k)))
    calc
      ENNReal.ofReal (M (v k)) * ENNReal.ofReal (δ k) =
          (∫⁻ _s in Set.Ioc (t (v k)) (t (v k) + δ k),
            ENNReal.ofReal (M (v k)) ∂volume) :=
        (h3Critical_extendedConstantWindow_eq_heightWidth
          (t (v k)) (δ k) (M (v k)) (hδ k).le).symm
      _ ≤ ∫⁻ s in Set.Ioc (t (v k)) (t (v k) + δ k),
          ENNReal.ofReal (velocityH3DissipationAt u s) ∂volume := hLower

/-- Exact finite-cost necessity on the selected explicit quartic widths:
any physical upper budget for the first m disjoint windows also bounds the
sum of their positive prescribed dissipation-height times duration. This
makes the remaining terminal question a quantitative rate-vs-width question,
not a high-band temporal-continuity assumption. -/
theorem h3Critical_quarticCofinalCost_finiteBudget_forces_weightedWidthCap
    (L U : ℕ → ENNReal)
    (hCost : ∀ m : ℕ,
      (∑ k ∈ Finset.range m, L k) ≤
        ∑ k ∈ Finset.range m, U k)
    (m : ℕ) (C : ENNReal)
    (hBudget : (∑ k ∈ Finset.range m, U k) ≤ C) :
    (∑ k ∈ Finset.range m, L k) ≤ C :=
  (hCost m).trans hBudget

end
end PrimeTensor.Bridge.Euclidean
