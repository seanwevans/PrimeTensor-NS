import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualHighpassSourceDissipationArbitraryProfiles
import Mathlib.Tactic

/-!
# Source-driven joint highpass/H³ windows without full-dissipation continuity

The actual projected Fourier source highpass square mass is continuous on the
open physical time interval. The previously closed kinetic-anchored estimate
bounds its L² norm above by an explicit affine function of high-H³ dissipation.
A sufficiently large SOURCE mass therefore forces high-H³ dissipation above
any prescribed threshold at that SAME time, without invoking continuity of
full H³ dissipation.

We select source spikes beyond this explicit budget and use source continuity
alone to persist the budget on common right-hand intervals. The whole interval
then has both the prescribed source and dissipation lower bounds. The source
has a corresponding integrated cost, and the dissipation has its cost when
local interval integrability is supplied. This does not assert automatic
local time integrability of the high-H³ dissipation or any width lower bound.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeH3SourceDrivenWindows
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3SourceDrivenWindows :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Exact conservative source-mass budget that enforces an independent
high-radial physical H³ dissipation threshold. -/
noncomputable def h3CriticalSourceDrivenHighDissipationBarrier
    (E σ M : ℝ) : ℝ :=
  max ((3 + h3AuditInitialLerayEnergyCoefficient) *
    (1 + 6 * E +
      3 * (σ ^ 2 * (h3TerminalRadialSobolevWeightSquareCeiling σ * E) + M))) 0

/-- A source mass beyond the squared kinetic-anchored source budget implies
high-H³ dissipation exceeding M at the same actual time, with no temporal
continuity hypothesis on dissipation. -/
theorem h3Critical_sourceMass_above_barrier_forces_highDissipation
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ σ : ℝ) (hσ : 0 ≤ σ) (i : Fin 3)
    (t : ℝ) (ht : t ∈ Set.Ioo b T) (M : ℝ)
    (hMass :
      (h3CriticalSourceDrivenHighDissipationBarrier
        (velocityH3Energy0At u b) σ M) ^ 2 <
        ∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
          ‖h3CriticalActualProjectedFourierSource hH3 i t ξ‖ ^ 2 ∂volume) :
    M < h3PathActualHighRadialDissipation244 σ
      (h3AuditActualSpectralVelocityTotal hH3 t) := by
  let C : ℝ := σ ^ 2 *
    (h3TerminalRadialSobolevWeightSquareCeiling σ * velocityH3Energy0At u b)
  let Q : ℝ := (3 + h3AuditInitialLerayEnergyCoefficient) *
    (1 + 6 * velocityH3Energy0At u b + 3 * (C + M))
  let B : ℝ := max Q 0
  have hBig : B ^ 2 <
      ∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
        ‖h3CriticalActualProjectedFourierSource hH3 i t ξ‖ ^ 2 ∂volume := by
    exact hMass
  by_contra hNot
  have hDle :
      h3PathActualHighRadialDissipation244 σ
        (h3AuditActualSpectralVelocityTotal hH3 t) ≤ M :=
    le_of_not_gt hNot
  have hCoeff : 0 ≤ 3 + h3AuditInitialLerayEnergyCoefficient := by
    have h := h3AuditInitialLerayEnergyCoefficient_nonneg
    linarith only [h]
  have hPoint :=
    h3Critical_actualHighpassFourierSource_norm_le_highRadialDissipation
      hH3 hClass b hb ρ σ hσ i t ht
  have hInner :
      1 + 6 * velocityH3Energy0At u b +
        3 * (C + h3PathActualHighRadialDissipation244 σ
          (h3AuditActualSpectralVelocityTotal hH3 t)) ≤
      1 + 6 * velocityH3Energy0At u b + 3 * (C + M) := by
    linarith only [hDle]
  have hNormUpper :
      ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖ ≤ Q := by
    exact hPoint.trans
      (mul_le_mul_of_nonneg_left hInner hCoeff)
  let H : H3FourierComplexL2 :=
    h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t
  have hBound : ‖H‖ ≤ B :=
    hNormUpper.trans (le_max_left Q 0)
  have hBNonneg : 0 ≤ B := le_max_right Q 0
  have hSquareBound : ‖H‖ ^ 2 ≤ B ^ 2 :=
    (sq_le_sq₀ (norm_nonneg H) hBNonneg).2 hBound
  have hMassEq : ‖H‖ ^ 2 =
      ∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
        ‖h3CriticalActualProjectedFourierSource hH3 i t ξ‖ ^ 2 ∂volume :=
    h3Critical_fourierSharpHighpass_norm_sq_eq_integral ρ _
  have hAbove : B ^ 2 < ‖H‖ ^ 2 := by
    rw [hMassEq]
    exact hBig
  exact (not_lt_of_ge hSquareBound) hAbove

/-- The source-only continuity theorem constructs simultaneous moving-cutoff
source and physical H³ dissipation windows. Unlike the preceding profile
window theorem, this theorem needs NO `hDCont` hypothesis. For the high-H³
integrated cost, only integrability on the particular compact window is
requested, as an implication rather than a global premise. -/
theorem h3Critical_noL2Trace_sourceDriven_profileWindows
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
    ∃ i : Fin 3, ∃ t δ : ℕ → ℝ,
      Tendsto t atTop (𝓝 T) ∧
      ∀ n : ℕ,
        t n ∈ Set.Ioo (c n) T ∧
        0 < δ n ∧ t n + δ n < T ∧
        (∀ s : ℝ, s ∈ Set.Icc (t n) (t n + δ n) →
          K n < ∫ ξ in (h3TerminalRadialFrequencyBelow (ρ n))ᶜ,
            ‖h3CriticalActualProjectedFourierSource hH3 i s ξ‖ ^ 2 ∂volume ∧
          M n < h3PathActualHighRadialDissipation244 (σ n)
            (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
        δ n * K n ≤ ∫ s in t n..(t n + δ n),
          (∫ ξ in (h3TerminalRadialFrequencyBelow (ρ n))ᶜ,
            ‖h3CriticalActualProjectedFourierSource hH3 i s ξ‖ ^ 2 ∂volume) ∧
        (IntervalIntegrable (fun s : ℝ =>
          h3PathActualHighRadialDissipation244 (σ n)
            (h3AuditActualSpectralVelocityTotal hH3 s))
            volume (t n) (t n + δ n) →
          δ n * M n ≤ ∫ s in t n..(t n + δ n),
            h3PathActualHighRadialDissipation244 (σ n)
              (h3AuditActualSpectralVelocityTotal hH3 s)) := by
  let B : ℕ → ℝ := fun n =>
    h3CriticalSourceDrivenHighDissipationBarrier
      (velocityH3Energy0At u b) (σ n) (M n)
  obtain ⟨i, hi⟩ :=
    h3Critical_noL2Trace_actualHighpassFourierMass_escape
      hH3 hClass b hb hNoTrace
  have hWitness (n : ℕ) : ∃ t : ℝ,
      t ∈ Set.Ioo (c n) T ∧
      max (K n) ((B n) ^ 2) <
        ∫ ξ in (h3TerminalRadialFrequencyBelow (ρ n))ᶜ,
          ‖h3CriticalActualProjectedFourierSource hH3 i t ξ‖ ^ 2 ∂volume :=
    hi (ρ n) (hρ n) (c n) (hc n) (max (K n) ((B n) ^ 2))
  choose t ht hLarge using hWitness
  have htLimit : Tendsto t atTop (𝓝 T) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      hcLimit tendsto_const_nhds
      (fun n => (ht n).1.le)
      (fun n => (ht n).2.le)
  have hSub : Set.Ioo a T ⊆ Set.Ioo (0 : ℝ) T := by
    intro s hs
    exact ⟨lt_trans hClass.terminal_start.1 hs.1, hs.2⟩
  have hWindow (n : ℕ) : ∃ δ : ℝ, 0 < δ ∧ t n + δ < T ∧
      (∀ s : ℝ, s ∈ Set.Icc (t n) (t n + δ) →
        K n < ∫ ξ in (h3TerminalRadialFrequencyBelow (ρ n))ᶜ,
          ‖h3CriticalActualProjectedFourierSource hH3 i s ξ‖ ^ 2 ∂volume ∧
        M n < h3PathActualHighRadialDissipation244 (σ n)
          (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
      δ * K n ≤ ∫ s in t n..(t n + δ),
        (∫ ξ in (h3TerminalRadialFrequencyBelow (ρ n))ᶜ,
          ‖h3CriticalActualProjectedFourierSource hH3 i s ξ‖ ^ 2 ∂volume) ∧
      (IntervalIntegrable (fun s : ℝ =>
        h3PathActualHighRadialDissipation244 (σ n)
          (h3AuditActualSpectralVelocityTotal hH3 s)) volume (t n) (t n + δ) →
        δ * M n ≤ ∫ s in t n..(t n + δ),
          h3PathActualHighRadialDissipation244 (σ n)
            (h3AuditActualSpectralVelocityTotal hH3 s)) := by
    let F : ℝ → ℝ := fun s =>
      ∫ ξ in (h3TerminalRadialFrequencyBelow (ρ n))ᶜ,
        ‖h3CriticalActualProjectedFourierSource hH3 i s ξ‖ ^ 2 ∂volume
    let G : ℝ → ℝ := fun s =>
      h3PathActualHighRadialDissipation244 (σ n)
        (h3AuditActualSpectralVelocityTotal hH3 s)
    have hCont : ContinuousOn F (Set.Ioo a T) :=
      (h3Critical_actualHighpassSourceMass_continuousOn
        hH3 (ρ n) i).mono hSub
    have htClass : t n ∈ Set.Ioo a T :=
      ⟨lt_trans hb.1 (lt_trans (hc n).1 (ht n).1), (ht n).2⟩
    have hK : K n < F (t n) :=
      (le_max_left (K n) ((B n) ^ 2)).trans_lt (hLarge n)
    have hB : (B n) ^ 2 < F (t n) :=
      (le_max_right (K n) ((B n) ^ 2)).trans_lt (hLarge n)
    obtain ⟨δ, hδ, hEnd, hSourceFloor, hCost, _hCostB⟩ :=
      h3Critical_twoContinuousSpikes_integratedWindow F F
        htClass hCont hCont hK hB
    have hBoth : ∀ s : ℝ, s ∈ Set.Icc (t n) (t n + δ) →
        K n < F s ∧ M n < G s := by
      intro s hs
      have hAfterB : s ∈ Set.Ioo b T :=
        ⟨lt_of_lt_of_le (lt_trans (hc n).1 (ht n).1) hs.1,
          lt_of_le_of_lt hs.2 hEnd⟩
      have hBarrier :
          (h3CriticalSourceDrivenHighDissipationBarrier
            (velocityH3Energy0At u b) (σ n) (M n)) ^ 2 < F s :=
        (hSourceFloor s hs).2
      exact ⟨(hSourceFloor s hs).1,
        h3Critical_sourceMass_above_barrier_forces_highDissipation
          hH3 hClass b hb (ρ n) (σ n) (hσ n) i s hAfterB (M n)
          hBarrier⟩
    have hConditional : IntervalIntegrable G volume (t n) (t n + δ) →
        δ * M n ≤ ∫ s in t n..(t n + δ), G s := by
      intro hGInt
      have hCostG : ((t n + δ) - t n) * M n ≤
          ∫ s in t n..(t n + δ), G s :=
        h3Path_localPositiveHeight_forces_integratedCost244
          G (t n) (t n + δ) (M n) (by linarith only [hδ]) hGInt
          (fun s hs => (hBoth s hs).2.le)
      calc
        δ * M n = ((t n + δ) - t n) * M n := by ring
        _ ≤ ∫ s in t n..(t n + δ), G s := hCostG
    exact ⟨δ, hδ, hEnd, hBoth, hCost, hConditional⟩
  choose δ hδ using hWindow
  refine ⟨i, t, δ, htLimit, ?_⟩
  intro n
  exact ⟨ht n, (hδ n).1, (hδ n).2.1,
    (hδ n).2.2.1, (hδ n).2.2.2.1, (hδ n).2.2.2.2⟩

/-- Source-driven common windows can be separated without requiring full
H³ dissipation continuity. The high-H³ finite-sum cost is available under
local interval integrability on the selected compact windows; source costs
need no additional regularity premise. -/
theorem h3Critical_noL2Trace_sourceDriven_profileDisjointWindows
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
      (∀ k : ℕ,
        t (v k) ∈ Set.Ioo (c (v k)) T ∧
        0 < δ (v k) ∧ t (v k) + δ (v k) < T ∧
        (∀ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + δ (v k)) →
          K (v k) < ∫ ξ in (h3TerminalRadialFrequencyBelow (ρ (v k)))ᶜ,
            ‖h3CriticalActualProjectedFourierSource hH3 i s ξ‖ ^ 2 ∂volume ∧
          M (v k) < h3PathActualHighRadialDissipation244 (σ (v k))
            (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
        δ (v k) * K (v k) ≤
          ∫ s in t (v k)..(t (v k) + δ (v k)),
            (∫ ξ in (h3TerminalRadialFrequencyBelow (ρ (v k)))ᶜ,
              ‖h3CriticalActualProjectedFourierSource hH3 i s ξ‖ ^ 2 ∂volume) ∧
        (IntervalIntegrable (fun s : ℝ =>
          h3PathActualHighRadialDissipation244 (σ (v k))
            (h3AuditActualSpectralVelocityTotal hH3 s))
            volume (t (v k)) (t (v k) + δ (v k)) →
          δ (v k) * M (v k) ≤
            ∫ s in t (v k)..(t (v k) + δ (v k)),
              h3PathActualHighRadialDissipation244 (σ (v k))
                (h3AuditActualSpectralVelocityTotal hH3 s))) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m, δ (v k) * K (v k)) ≤
          ∑ k ∈ Finset.range m,
            ∫ s in t (v k)..(t (v k) + δ (v k)),
              (∫ ξ in (h3TerminalRadialFrequencyBelow (ρ (v k)))ᶜ,
                ‖h3CriticalActualProjectedFourierSource hH3 i s ξ‖ ^ 2 ∂volume)) ∧
      (∀ m : ℕ,
        (∀ k : ℕ, k < m →
          IntervalIntegrable (fun s : ℝ =>
            h3PathActualHighRadialDissipation244 (σ (v k))
              (h3AuditActualSpectralVelocityTotal hH3 s))
            volume (t (v k)) (t (v k) + δ (v k))) →
        (∑ k ∈ Finset.range m, δ (v k) * M (v k)) ≤
          ∑ k ∈ Finset.range m,
            ∫ s in t (v k)..(t (v k) + δ (v k)),
              h3PathActualHighRadialDissipation244 (σ (v k))
                (h3AuditActualSpectralVelocityTotal hH3 s)) := by
  obtain ⟨i, t, δ, htLimit, hWindow⟩ :=
    h3Critical_noL2Trace_sourceDriven_profileWindows
      hH3 hClass b hb hNoTrace c ρ σ K M hc hcLimit hρ hσ
  have hWidth (n : ℕ) : 0 < δ n := (hWindow n).2.1
  have hEnd (n : ℕ) : t n + δ n < T := (hWindow n).2.2.1
  obtain ⟨v, hMono, hCofinal, hSeparated⟩ :=
    h3Path_exists_strictMono_pairwiseSeparatedTerminalWindows244
      t δ T htLimit hWidth hEnd
  refine ⟨i, t, δ, v, hMono, hCofinal, hSeparated, ?_, ?_, ?_⟩
  · intro k
    exact hWindow (v k)
  · intro m
    exact Finset.sum_le_sum (fun k _ => (hWindow (v k)).2.2.2.2.1)
  · intro m hInt
    exact Finset.sum_le_sum (fun k hk =>
      (hWindow (v k)).2.2.2.2.2 (hInt k (Finset.mem_range.mp hk)))

end
end PrimeTensor.Bridge.Euclidean
