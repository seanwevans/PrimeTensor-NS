import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticDisjointAnnularExtendedCosts
import Mathlib.Tactic

/-!
# Globally charge the same disjoint kinetic annular windows

Previously, every kinetic-only annular physical PDE clock paid an honest
extended full-H³ viscous cost, and the cofinal selected clocks were separated.
This file performs the missing *global* comparison. The key integration step
is `lintegral_biUnion_finset`: for pairwise disjoint measurable temporal
intervals, the sum of their (extended) integrals equals the integral on
their finite union, even when the dissipation integrand is not measurable.
The finite union is included in the physical preterminal interval, hence
its integral is at most the single global extended physical dissipation.

If the selected kinetic height-times-width partial sums diverge in ENNReal,
the actual full physical H³ dissipation has infinite extended integral.
This divergence premise is NOT established for an arbitrary prescribed
height profile: the outer Fourier cutoffs can increase and thereby shorten
the kinetic PDE clocks. No finite terminal L¹ or full-H³ continuity premise
is smuggled into the comparison.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- A purely measure-theoretic global packing lemma. The extended integral
is additive on disjoint measurable physical time windows even for a real
input f whose time measurability has not been established. Each window's
floor is paid exactly by its ENNReal height-times-width charge. -/
theorem thirdFull_scalar_disjointWindows_le_globalExtendedBudget244
    (f : ℝ → ℝ) (a T : ℝ) (p w H : ℕ → ℝ)
    (hStart : ∀ k : ℕ, a < p k)
    (hWidth : ∀ k : ℕ, 0 ≤ w k)
    (hEnd : ∀ k : ℕ, p k + w k < T)
    (hSeparated : ∀ k l : ℕ, k < l → p k + w k < p l)
    (hFloor : ∀ (k : ℕ) (r : ℝ),
      r ∈ Set.Icc (p k) (p k + w k) → H k ≤ f r)
    (m : ℕ) :
    (∑ k ∈ Finset.range m,
      ENNReal.ofReal (H k) * ENNReal.ofReal (w k)) ≤
      ∫⁻ r in Set.Ioo a T, ENNReal.ofReal (f r) ∂volume := by
  let W : ℕ → Set ℝ := fun k => Set.Ioc (p k) (p k + w k)
  have hDisjoint : (↑(Finset.range m) : Set ℕ).PairwiseDisjoint W := by
    intro i _hi j _hj hij
    apply Set.disjoint_left.mpr
    intro r hri hrj
    change p i < r ∧ r ≤ p i + w i at hri
    change p j < r ∧ r ≤ p j + w j at hrj
    have hOrder : i < j ∨ j < i := by omega
    rcases hOrder with hij' | hji'
    · have hBefore := hSeparated i j hij'
      linarith only [hri.2, hrj.1, hBefore]
    · have hBefore := hSeparated j i hji'
      linarith only [hrj.2, hri.1, hBefore]
  have hMeasurable (k : ℕ) (hk : k ∈ Finset.range m) :
      MeasurableSet (W k) := measurableSet_Ioc
  have hSubset : (⋃ k ∈ Finset.range m, W k) ⊆ Set.Ioo a T := by
    intro r hr
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hr
    obtain ⟨_hkRange, hkr⟩ := Set.mem_iUnion.mp hk
    change p k < r ∧ r ≤ p k + w k at hkr
    exact ⟨lt_trans (hStart k) hkr.1,
      lt_of_le_of_lt hkr.2 (hEnd k)⟩
  have hOne (k : ℕ) :
      ENNReal.ofReal (H k) * ENNReal.ofReal (w k) ≤
        ∫⁻ r in W k, ENNReal.ofReal (f r) ∂volume := by
    calc
      ENNReal.ofReal (H k) * ENNReal.ofReal (w k) =
          (∫⁻ _r in W k, ENNReal.ofReal (H k) ∂volume) :=
        (h3Critical_extendedConstantWindow_eq_heightWidth
          (p k) (w k) (H k) (hWidth k)).symm
      _ ≤ ∫⁻ r in W k, ENNReal.ofReal (f r) ∂volume :=
        h3Critical_extendedWindowCost_of_pointwiseFloor
          f (p k) (w k) (H k) (hFloor k)
  calc
    (∑ k ∈ Finset.range m,
        ENNReal.ofReal (H k) * ENNReal.ofReal (w k)) ≤
        ∑ k ∈ Finset.range m,
          ∫⁻ r in W k, ENNReal.ofReal (f r) ∂volume :=
      Finset.sum_le_sum (fun k _ => hOne k)
    _ = ∫⁻ r in ⋃ k ∈ Finset.range m, W k,
          ENNReal.ofReal (f r) ∂volume := by
      symm
      exact lintegral_biUnion_finset hDisjoint hMeasurable
        (fun r : ℝ => ENNReal.ofReal (f r))
    _ ≤ ∫⁻ r in Set.Ioo a T,
          ENNReal.ofReal (f r) ∂volume :=
      lintegral_mono_set hSubset

/-- Divergent disjoint height-width costs force infinite global extended
viscous cost. No converse and no automatic divergence is claimed. -/
theorem thirdFull_scalar_disjointWindows_divergence_forces_infinite244
    (f : ℝ → ℝ) (a T : ℝ) (p w H : ℕ → ℝ)
    (hStart : ∀ k : ℕ, a < p k)
    (hWidth : ∀ k : ℕ, 0 ≤ w k)
    (hEnd : ∀ k : ℕ, p k + w k < T)
    (hSeparated : ∀ k l : ℕ, k < l → p k + w k < p l)
    (hFloor : ∀ (k : ℕ) (r : ℝ),
      r ∈ Set.Icc (p k) (p k + w k) → H k ≤ f r)
    (hDiverge :
      (⨆ m : ℕ, ∑ k ∈ Finset.range m,
        ENNReal.ofReal (H k) * ENNReal.ofReal (w k)) = ⊤) :
    (∫⁻ r in Set.Ioo a T, ENNReal.ofReal (f r) ∂volume) = ⊤ := by
  have hUpper (m : ℕ) :
      (∑ k ∈ Finset.range m,
        ENNReal.ofReal (H k) * ENNReal.ofReal (w k)) ≤
      ∫⁻ r in Set.Ioo a T, ENNReal.ofReal (f r) ∂volume :=
    thirdFull_scalar_disjointWindows_le_globalExtendedBudget244
      f a T p w H hStart hWidth hEnd hSeparated hFloor m
  have hTop : (⊤ : ENNReal) ≤
      (∫⁻ r in Set.Ioo a T, ENNReal.ofReal (f r) ∂volume) := by
    rw [← hDiverge]
    exact iSup_le hUpper
  exact le_antisymm le_top hTop

/-- The actual no-terminal-H³-trace kinetic witnesses now pay a SINGLE
extended global physical dissipation budget. The *same* disjoint time
subsequence, same frequency cutoffs and exact kinetic-selected widths are
retained. This result does not assume terminal interval-integrability. -/
theorem thirdFullPhysical_noH3Trace_kineticDisjointGlobalExtendedBudget244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L))
    (M : ℕ → ℝ) (hM : ∀ n : ℕ, 0 < M n) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (δ : ℕ → ℝ)
        (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k : ℕ => τ (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      (∀ k : ℕ, k ≤ v k) ∧
      (∀ k : ℕ,
        ThirdFullKineticNaturalAnnularLocalWitness244
          hH3 b (τ (v k)) (v k) (N (v k))
          (M (v k)) (δ (v k))) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m,
          ENNReal.ofReal (M (v k) / 4) *
            ENNReal.ofReal (δ (v k))) ≤
        ∫⁻ r in Set.Ioo a T,
          ENNReal.ofReal (velocityH3DissipationAt u r) ∂volume) ∧
      ((⨆ m : ℕ, ∑ k ∈ Finset.range m,
          ENNReal.ofReal (M (v k) / 4) *
            ENNReal.ofReal (δ (v k))) = ⊤ →
        (∫⁻ r in Set.Ioo a T,
          ENNReal.ofReal (velocityH3DissipationAt u r) ∂volume) = ⊤) := by
  obtain ⟨τ, N, δ, v, hv, hCofinal, hSeparated,
    hIndex, hTimes⟩ :=
    thirdFullPhysical_noH3Trace_kineticDisjointAnnularWindows244
      hH3 hClass b hb hNoTrace M hM
  let p : ℕ → ℝ := fun k => τ (v k)
  let w : ℕ → ℝ := fun k => δ (v k)
  let H : ℕ → ℝ := fun k => M (v k) / 4
  have hStart (k : ℕ) : a < p k :=
    lt_trans hb.1 (hTimes k).1.1
  have hWidth (k : ℕ) : 0 ≤ w k := by
    rcases (hTimes k).2 with ⟨_, hPos, _, _, _, _⟩
    exact hPos.le
  have hEnd (k : ℕ) : p k + w k < T := by
    rcases (hTimes k).2 with ⟨_, _, _, hEnd, _, _⟩
    exact hEnd
  have hFloor (k : ℕ) (r : ℝ)
      (hr : r ∈ Set.Icc (p k) (p k + w k)) :
      H k ≤ velocityH3DissipationAt u r := by
    rcases (hTimes k).2 with ⟨_, _, _, _, hWitnessFloor, _⟩
    exact ((hWitnessFloor r hr).1.le).trans (hWitnessFloor r hr).2
  have hSep : ∀ k l : ℕ, k < l → p k + w k < p l :=
    hSeparated
  have hBound (m : ℕ) :
      (∑ k ∈ Finset.range m,
        ENNReal.ofReal (H k) * ENNReal.ofReal (w k)) ≤
        ∫⁻ r in Set.Ioo a T,
          ENNReal.ofReal (velocityH3DissipationAt u r) ∂volume :=
    thirdFull_scalar_disjointWindows_le_globalExtendedBudget244
      (velocityH3DissipationAt u) a T p w H
      hStart hWidth hEnd hSep hFloor m
  refine ⟨τ, N, δ, v, hv, hCofinal, hSeparated,
    hIndex, (fun k => (hTimes k).2), ?_, ?_⟩
  · intro m
    exact hBound m
  · intro hDiverge
    exact thirdFull_scalar_disjointWindows_divergence_forces_infinite244
      (velocityH3DissipationAt u) a T p w H
      hStart hWidth hEnd hSep hFloor hDiverge

end
end PrimeTensor.FirstMonomialTriad
