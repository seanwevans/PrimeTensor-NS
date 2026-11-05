import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalCubicAnnularWindows
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEDisjointCostSum244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEDisjointWindows244
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-!
# Terminal H³-nontrace cubic viscous charges and the exact width obstruction

The unconditional H³-nontrace annular windows have positive widths and
strictly cofinal left endpoints, but may overlap. The verified geometric
selection theorem gives disjoint genuine time intervals without changing
the selected widths or spectral annuli.

If full physical H³ dissipation is integrable, the real sum of all selected
cubic height-width charges is finite. In particular those charges tend to
zero, an explicit o(radius^{-3}) endpoint width compression. This does not
contradict the original PDE hypotheses: a PDE-based LOWER persistence bound
is still needed to exclude such compression.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal Interval

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeTerminalCubicDisjoint244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- With full endpoint H³ dissipation in L¹, failure of the strong terminal
H³ trace forces genuine cofinal pairwise-disjoint positive-width annular
windows whose cubic viscous charges have a UNIFORM total-integral bound.
No positive terminal kinetic energy or physical L² nontrace assumption. -/
theorem thirdFullPhysical_noH3Trace_disjointCubicViscousCharges244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (δ : ℕ → ℝ) (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ k l, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      (∀ k, τ (v k) ∈ Set.Ioo b T ∧
        v k ≤ N (v k) ∧ 0 < δ (v k) ∧
        τ (v k) + δ (v k) < T) ∧
      (∀ k, ∀ s : ℝ,
        s ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k)) →
        ((v k : ℝ) + 1) ^ 3 / 2 <
          h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s) -
          h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m,
          δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ≤
            ∫ r in a..T, velocityH3DissipationAt u r) := by
  obtain ⟨τ, N, δ, hTime, hLimit, hWindows, hFloor, _hCost⟩ :=
    thirdFullPhysical_noH3Trace_cubicFiniteAnnularWindows244
      hH3 hClass b hb hNoTrace
  have hδ (n : ℕ) : 0 < δ n := (hWindows n).2.1
  have hEnd (n : ℕ) : τ n + δ n < T := (hWindows n).2.2
  obtain ⟨v, hMono, hCofinal, hSeparated⟩ :=
    h3Path_exists_strictMono_pairwiseSeparatedTerminalWindows244
      τ δ T hLimit hδ hEnd
  have hFloorFull (k : ℕ) (r : ℝ)
      (hr : r ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k))) :
      ((v k : ℝ) + 1) ^ 3 / 2 ≤ velocityH3DissipationAt u r := by
    have hrClass : r ∈ Set.Ioo a T :=
      ⟨lt_of_lt_of_le (lt_trans hb.1 (hTime (v k)).1) hr.1,
        lt_of_le_of_lt hr.2 (hEnd (v k))⟩
    exact ((hFloor (v k) r hr).1.le).trans
      (h3Path_actualFiniteAnnulusDissipation_le_fullAt244
        hH3 hClass r hrClass ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1))
  have hSum := h3Path_disjointNonnegativeWindows_finiteHeightCost_le244
    (velocityH3DissipationAt u) a T
    (fun k => τ (v k)) (fun k => δ (v k))
    (fun k => ((v k : ℝ) + 1) ^ 3 / 2)
    hClass.terminal_start.2.le
    (fun r => velocityH3DissipationAt_nonneg u r)
    hDInt
    (fun k => (lt_trans hb.1 (hTime (v k)).1).le)
    (fun k => (hδ (v k)).le)
    (fun k => (hEnd (v k)).le)
    (fun k => (hSeparated k (k + 1) (Nat.lt_succ_self k)).le)
    hFloorFull
  refine ⟨τ, N, δ, v, hMono, hCofinal, hSeparated, ?_, ?_, hSum⟩
  · intro k
    exact ⟨hTime (v k), (hWindows (v k)).1,
      hδ (v k), hEnd (v k)⟩
  · intro k r hr
    exact (hFloor (v k) r hr).1

/-- In the finite-dissipation branch, those exact DISJOINT cubic charges form
a nonnegative summable real sequence. Therefore the weighted widths tend to
zero along the same selected terminal subsequence, even though the initial
instantaneous dissipation heights grow cubically. -/
theorem thirdFullPhysical_noH3Trace_cubicChargeSummable_and_widthCompression244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T) :
    ∃ (τ δ : ℕ → ℝ) (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ k l, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      (∀ k, 0 < δ (v k)) ∧
      Summable (fun k : ℕ =>
        δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ∧
      Tendsto (fun k : ℕ =>
        δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) atTop (𝓝 0) := by
  obtain ⟨τ, _N, δ, v, hMono, hLimit, hSeparate,
    hWindows, _hFloor, hSum⟩ :=
    thirdFullPhysical_noH3Trace_disjointCubicViscousCharges244
      hH3 hClass b hb hNoTrace hDInt
  have hNonneg (k : ℕ) :
      0 ≤ δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2) := by
    have hδ : 0 ≤ δ (v k) := (hWindows k).2.2.1.le
    have hRadius : 0 ≤ (v k : ℝ) + 1 := by positivity
    positivity
  have hSummable : Summable (fun k : ℕ =>
      δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) :=
    summable_of_sum_range_le hNonneg hSum
  exact ⟨τ, δ, v, hMono, hLimit, hSeparate,
    (fun k => (hWindows k).2.2.1), hSummable,
    hSummable.tendsto_atTop_zero⟩

end
end PrimeTensor.FirstMonomialTriad
