import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticAnnularLocalCofinal
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEDisjointWindows244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualHighpassSourceDrivenExtendedWidthBudget
import Mathlib.Tactic

/-!
# Disjoint kinetic annular clocks, with honest extended physical H3 costs

The preceding no-H3-terminal-trace diagonal certifies a finite natural
annular PDE window at every cofinal sample time. Each window has a positive,
explicit kinetic-only width; nothing previously guaranteed that different
windows did not overlap.

A pre-existing terminal-window selection lemma extracts strictly separated
closed windows, without shortening their widths or reselecting the outer
frequencies. We transfer their actual low-band PDE certificates unchanged.
The *extended* physical H3 dissipation on each half-open window dominates
its explicit height times width, even without measurability or terminal L1
integrability of the full dissipation. This extends to finite sums of these
separate window charges. No summability of the widths or total dissipation
is asserted; no no-physical-L2-trace premise is introduced.

The final rate test transports the previous kinetic outer-frequency escape
criterion along precisely the same disjoint windows, with every conditional
clock and finite-rate-budget premise visible.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- Extract strictly separated windows from the original arbitrary-height
no-H3-trace physical kinetic annular sequence. The original radii and the
exact kinetic PDE-selected widths are preserved at each retained index. -/
theorem thirdFullPhysical_noH3Trace_kineticDisjointAnnularWindows244
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
      (∀ k : ℕ, τ (v k) ∈ Set.Ioo b T ∧
        ThirdFullKineticNaturalAnnularLocalWitness244
          hH3 b (τ (v k)) (v k) (N (v k))
          (M (v k)) (δ (v k))) := by
  obtain ⟨τ, N, δ, hTimes, hLimit, hWindows⟩ :=
    thirdFullPhysical_noH3Trace_kineticLocalAnnularCofinal244
      hH3 hClass b hb hNoTrace M hM
  have hPositive (n : ℕ) : 0 < δ n := by
    rcases hWindows n with ⟨_hnN, hp, _heq, _hend, _hfloor, _hcost⟩
    exact hp
  have hBefore (n : ℕ) : τ n + δ n < T := by
    rcases hWindows n with ⟨_hnN, _hp, _heq, he, _hfloor, _hcost⟩
    exact he
  obtain ⟨v, hv, hCofinal, hSeparated⟩ :=
    h3Path_exists_strictMono_pairwiseSeparatedTerminalWindows244
      τ δ T hLimit hPositive hBefore
  have hIndex (k : ℕ) : k ≤ v k := by
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
        exact Nat.succ_le_of_lt
          (lt_of_le_of_lt ih (hv (Nat.lt_succ_self k)))
  exact ⟨τ, N, δ, v, hv, hCofinal, hSeparated,
    hIndex, fun k => ⟨hTimes (v k), hWindows (v k)⟩⟩

/-- Extended full physical H3 dissipation dominates the explicit kinetic
annular height-width on a previously selected positive-width window.
This uses a pointwise inequality, not interval-integrability of full D. -/
theorem thirdFullPhysical_kineticAnnularWindow_extendedPhysicalCost244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b x : ℝ) (n N : ℕ) (M δ : ℝ)
    (hWindow : ThirdFullKineticNaturalAnnularLocalWitness244
      hH3 b x n N M δ) :
    ENNReal.ofReal (M / 4) * ENNReal.ofReal δ ≤
      ∫⁻ r in Set.Ioc x (x + δ),
        ENNReal.ofReal (velocityH3DissipationAt u r) ∂volume := by
  rcases hWindow with ⟨_hnN, hδ, _heq, _hend, hFloor, _hCost⟩
  have hFull (r : ℝ) (hr : r ∈ Set.Icc x (x + δ)) :
      M / 4 ≤ velocityH3DissipationAt u r :=
    (hFloor r hr).1.le.trans (hFloor r hr).2
  calc
    ENNReal.ofReal (M / 4) * ENNReal.ofReal δ =
        (∫⁻ _r in Set.Ioc x (x + δ),
          ENNReal.ofReal (M / 4) ∂volume) :=
      (h3Critical_extendedConstantWindow_eq_heightWidth
        x δ (M / 4) hδ.le).symm
    _ ≤ ∫⁻ r in Set.Ioc x (x + δ),
          ENNReal.ofReal (velocityH3DissipationAt u r) ∂volume :=
      h3Critical_extendedWindowCost_of_pointwiseFloor
        (velocityH3DissipationAt u) x δ (M / 4) hFull

/-- This is the first finite-sum EXTENDED physical dissipation charge for
the new kinetic PDE clocks on truly separated cofinal windows, with no
terminal H3 dissipation L1 hypothesis. Every individual annular integral
and all original radii and exact widths are retained, rather than replaced
by a free-standing height lower bound. -/
theorem thirdFullPhysical_noH3Trace_kineticDisjointAnnularExtendedCosts244
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
      (∀ k : ℕ,
        ENNReal.ofReal (M (v k) / 4) * ENNReal.ofReal (δ (v k)) ≤
        ∫⁻ r in Set.Ioc (τ (v k)) (τ (v k) + δ (v k)),
          ENNReal.ofReal (velocityH3DissipationAt u r) ∂volume) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m, δ (v k) * (M (v k) / 4)) ≤
        ∑ k ∈ Finset.range m,
          ∫ r in τ (v k)..(τ (v k) + δ (v k)),
            h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 r) -
            h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 r)) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m,
          ENNReal.ofReal (M (v k) / 4) * ENNReal.ofReal (δ (v k))) ≤
        ∑ k ∈ Finset.range m,
          ∫⁻ r in Set.Ioc (τ (v k)) (τ (v k) + δ (v k)),
            ENNReal.ofReal (velocityH3DissipationAt u r) ∂volume) := by
  obtain ⟨τ, N, δ, v, hv, hCofinal, hSeparated,
    hIndex, hTimes⟩ :=
    thirdFullPhysical_noH3Trace_kineticDisjointAnnularWindows244
      hH3 hClass b hb hNoTrace M hM
  have hWindows (k : ℕ) :
      ThirdFullKineticNaturalAnnularLocalWitness244
        hH3 b (τ (v k)) (v k) (N (v k))
        (M (v k)) (δ (v k)) := (hTimes k).2
  have hOne (k : ℕ) :
      ENNReal.ofReal (M (v k) / 4) * ENNReal.ofReal (δ (v k)) ≤
      ∫⁻ r in Set.Ioc (τ (v k)) (τ (v k) + δ (v k)),
        ENNReal.ofReal (velocityH3DissipationAt u r) ∂volume :=
    thirdFullPhysical_kineticAnnularWindow_extendedPhysicalCost244
      hH3 b (τ (v k)) (v k) (N (v k))
      (M (v k)) (δ (v k)) (hWindows k)
  have hRealOne (k : ℕ) :
      δ (v k) * (M (v k) / 4) ≤
      ∫ r in τ (v k)..(τ (v k) + δ (v k)),
        h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 r) -
        h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 r) := by
    rcases hWindows k with ⟨_, _, _, _, _, hCharge⟩
    exact hCharge.1
  refine ⟨τ, N, δ, v, hv, hCofinal, hSeparated,
    hIndex, hWindows, hOne, ?_, ?_⟩
  · intro m
    exact Finset.sum_le_sum (fun k _ => hRealOne k)
  · intro m
    exact Finset.sum_le_sum (fun k _ => hOne k)


/-- A FINITE EXTENDED physical-dissipation budget for one locally certified
kinetic annular window forces the same exact clock/rate dichotomy as the
ordinary annular integral. No finite full-H3 terminal integral is assumed;
the external upper bound is on this one half-open physical window alone. -/
theorem thirdFullPhysical_kineticAnnularExtendedBudget_clockOrRate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b x : ℝ) (n N : ℕ) (M δ C : ℝ)
    (hM : 0 < M) (hC : 0 ≤ C)
    (hWindow : ThirdFullKineticNaturalAnnularLocalWitness244
      hH3 b x n N M δ)
    (hBudget :
      (∫⁻ r in Set.Ioc x (x + δ),
        ENNReal.ofReal (velocityH3DissipationAt u r) ∂volume) ≤
        ENNReal.ofReal C) :
    (T - x) * (M / 2) ≤ 16 * C ∨
      (M / 2) ^ 2 ≤ 8 *
        (thirdFullPhysicalKineticLowBandDissipationRate244 N
            (velocityH3Energy0At u b) +
         thirdFullPhysicalKineticLowBandDissipationRate244 n
            (velocityH3Energy0At u b) + 1) * C := by
  have hENN : ENNReal.ofReal (M / 4) * ENNReal.ofReal δ ≤
      ENNReal.ofReal C :=
    (thirdFullPhysical_kineticAnnularWindow_extendedPhysicalCost244
      hH3 b x n N M δ hWindow).trans hBudget
  rcases hWindow with ⟨_hnN, hδ, hEq, hEnd, _hFloor, _hLocalCost⟩
  have hCost : δ * (M / 4) ≤ C := by
    apply (ENNReal.ofReal_le_ofReal_iff hC).mp
    rw [ENNReal.ofReal_mul hδ.le]
    simpa only [mul_comm] using hENN
  let Λ : ℝ :=
    thirdFullPhysicalKineticLowBandDissipationRate244 N
      (velocityH3Energy0At u b) +
    thirdFullPhysicalKineticLowBandDissipationRate244 n
      (velocityH3Energy0At u b)
  have hΛ : 0 ≤ Λ := add_nonneg
    (thirdFullPhysicalKineticLowBandDissipationRate_nonneg244 N _)
    (thirdFullPhysicalKineticLowBandDissipationRate_nonneg244 n _)
  have hxT : x < T := by linarith only [hδ, hEnd]
  have hxMid : x ∈ Set.Icc x (x + (T - x) / 2) := by
    constructor
    · exact le_rfl
    · linarith only [hxT]
  have hWidth : δ = min (((T - x) / 2) / 2)
      (((M / 2) / 2) / (2 * (Λ + 1))) := by
    simpa only [Λ,
      show ((T - x) / 2) / 2 = (T - x) / 4 by ring,
      show (M / 2) / 2 = M / 4 by ring] using hEq
  have hFork := thirdFull_scalar_secondaryAnnularClockOrRate244
    T x x (M / 2) Λ δ C
    (by linarith only [hM]) hΛ hxMid hWidth
    (by simpa only [show (M / 2) / 2 = M / 4 by ring] using hCost)
  simpa only [Λ] using hFork

/-- A finite extended physical-cost budget that is too small for both the
actual time clock and every kinetic PDE rate up to a proposed natural
frequency cutoff forces the annulus outer cutoff beyond that proposal.
The conclusion does not depend on a terminal L1 assumption or on attained
full-H3 source/state maxima. -/
theorem thirdFullPhysical_kineticAnnularExtendedBudget_outerEscape244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b x : ℝ) (n N n0 : ℕ) (M δ C : ℝ)
    (hM : 0 < M) (hC : 0 ≤ C)
    (hWindow : ThirdFullKineticNaturalAnnularLocalWitness244
      hH3 b x n N M δ)
    (hBudget :
      (∫⁻ r in Set.Ioc x (x + δ),
        ENNReal.ofReal (velocityH3DissipationAt u r) ∂volume) ≤
        ENNReal.ofReal C)
    (hClock : 16 * C < (T - x) * (M / 2))
    (hSmall : 8 *
      ((∑ j ∈ Finset.range (n0 + 1),
          thirdFullPhysicalKineticLowBandDissipationRate244 j
            (velocityH3Energy0At u b)) +
        thirdFullPhysicalKineticLowBandDissipationRate244 n
          (velocityH3Energy0At u b) + 1) * C < (M / 2) ^ 2) :
    n0 < N := by
  have hFork := thirdFullPhysical_kineticAnnularExtendedBudget_clockOrRate244
    hH3 b x n N M δ C hM hC hWindow hBudget
  rcases hFork with hShort | hFast
  · have hImpossible :
        (T - x) * (M / 2) < (T - x) * (M / 2) :=
      lt_of_le_of_lt hShort hClock
    exact False.elim ((lt_irrefl _) hImpossible)
  · let L : ℕ → ℝ := fun j =>
        thirdFullPhysicalKineticLowBandDissipationRate244 j
          (velocityH3Energy0At u b)
    have hL (j : ℕ) : 0 ≤ L j :=
      thirdFullPhysicalKineticLowBandDissipationRate_nonneg244 j _
    exact thirdFull_scalar_kineticAnnularRate_forces_outerCutoffEscape244
      L n N n0 (M / 2) C hL hC
      (by simpa only [L] using hFast)
      (by simpa only [L] using hSmall)

end
end PrimeTensor.FirstMonomialTriad
