import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticAngularTerminalTrace244
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Tactic

/-!
# Cofinal angular Gram bursts from failure of the physical terminal trace

The previous checkpoint proved that uniform vanishing of the normalized
angular Gram action on later strict-time intervals produces a strong physical
L² terminal trace with precisely the canonical kinetic mass L>0.

Here we isolate a necessary obstruction to the *failure* of such a trace.
If no terminal Hilbert trace exists and L>0, there is a fixed epsilon>0 such
that every terminal tail (b,T) contains two ordered times s≤t carrying at
least epsilon of the scalar angular action

     ∫_s^t sqrt(Delta(r))/E0(r) dr.

The equality with integrated angular Hilbert speed gives the same fixed lower
bound for ∫_s^t ||N'(r)|| dr. This is a quantitative cofinal *length* result;
it does not assert that ||N(t)-N(s)|| is bounded below, since cancellation
can make the net chord small even when total angular variation is large.

The final alternative also covers L=0, where terminal L² convergence to zero
is already established. No high-frequency-to-angular coercivity is asserted.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- A fixed positive normalized Gram action persists on intervals contained
in every terminal subtail. Both sampled times lie strictly above the cutoff. -/
def H3PhysicalAngularGramCofinalBursts244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∀ b : ℝ, b ∈ Set.Ioo a T →
      ∃ s t : ℝ,
        s ∈ Set.Ioo b T ∧ t ∈ Set.Ioo b T ∧ s ≤ t ∧
          ε ≤ (∫ r in s..t,
            Real.sqrt (h3PathPhysicalSourceGramDefect244 hH3 r) /
              velocityH3Energy0At u r)

/-- If fixed positive angular Gram bursts cannot be found on every later
subtail, then the normalized Gram action vanishes uniformly at the endpoint.
The argument extracts a neighborhood cutoff from the negation of the cofinal
burst property; it uses no analytic bound on the Gram integrand. -/
theorem h3Path_physicalAngularGramTailVanishing_of_noCofinalBursts244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hNoBursts : ¬ H3PhysicalAngularGramCofinalBursts244 (a := a) hH3) :
    H3PhysicalAngularGramTerminalTailVanishing244 (a := a) hH3 := by
  classical
  intro ε hε
  have hCutoff :
      ∃ b : ℝ, b ∈ Set.Ioo a T ∧
        ∀ s t : ℝ,
          s ∈ Set.Ioo b T → t ∈ Set.Ioo b T → s ≤ t →
            (∫ r in s..t,
              Real.sqrt (h3PathPhysicalSourceGramDefect244 hH3 r) /
                velocityH3Energy0At u r) < ε := by
    by_contra hNoCutoff
    apply hNoBursts
    refine ⟨ε, hε, ?_⟩
    intro b hb
    by_contra hNoInterval
    apply hNoCutoff
    refine ⟨b, hb, ?_⟩
    intro s t hs ht hst
    by_contra hNotSmall
    exact hNoInterval ⟨s, t, hs, ht, hst, le_of_not_gt hNotSmall⟩
  obtain ⟨b, hb, hSmall⟩ := hCutoff
  have hAfter : ∀ᶠ s : ℝ in 𝓝 T, b < s := Ioi_mem_nhds hb.2
  filter_upwards [hAfter.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with s hbs hsT
  have hsTail : s ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hbs, hsT⟩
  refine ⟨hsTail, ?_⟩
  intro t ht hst
  exact hSmall s t ⟨hbs, hsT⟩
    ⟨lt_of_lt_of_le hbs hst, ht.2⟩ hst

/-- Failure of a terminal unit-direction limit forces cofinal positive
normalized Gram action in the positive terminal kinetic-mass branch. -/
theorem h3Path_physicalAngularGram_cofinalBursts_of_noUnitTrace244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ N : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3PathPhysicalUnitVelocity244 hH3) (𝓝[<] T) (𝓝 N)) :
    H3PhysicalAngularGramCofinalBursts244 (a := a) hH3 := by
  by_contra hNoBursts
  have hTail : H3PhysicalAngularGramTerminalTailVanishing244 (a := a) hH3 :=
    h3Path_physicalAngularGramTailVanishing_of_noCofinalBursts244
      hH3 hClass hNoBursts
  exact hNoTrace
    (h3Path_physicalUnitVelocity_existsTerminalTrace_of_angularGram244
      hH3 hClass hL hTail)

/-- No strong terminal physical L² velocity trace at positive kinetic mass
implies a fixed scalar angular Gram burst on every strict terminal tail. -/
theorem h3Path_physicalAngularGram_cofinalBursts_of_noVelocityTrace244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3) (𝓝[<] T) (𝓝 U)) :
    H3PhysicalAngularGramCofinalBursts244 (a := a) hH3 := by
  have hNoUnit : ¬ ∃ N : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3PathPhysicalUnitVelocity244 hH3) (𝓝[<] T) (𝓝 N) := by
    rintro ⟨N, hN⟩
    exact hNoTrace ⟨_,
      h3Path_physicalVelocity_terminalTrace_of_unitDirection244
        hH3 hClass hL N hN⟩
  exact h3Path_physicalAngularGram_cofinalBursts_of_noUnitTrace244
    hH3 hClass hL hNoUnit

/-- Equivalently, terminal failure forces a fixed lower bound for the
*integral* of physical unit-velocity speed on arbitrarily late intervals.
This statement concerns path length, not a lower bound on a terminal chord. -/
theorem h3Path_physicalAngularGram_cofinalUnitSpeedAction_of_noVelocityTrace244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3) (𝓝[<] T) (𝓝 U)) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ b : ℝ, b ∈ Set.Ioo a T →
        ∃ s t : ℝ,
          s ∈ Set.Ioo b T ∧ t ∈ Set.Ioo b T ∧ s ≤ t ∧
            ε ≤ (∫ r in s..t,
              ‖deriv (h3PathPhysicalUnitVelocity244 hH3) r‖) := by
  obtain ⟨ε, hε, hBursts⟩ :=
    h3Path_physicalAngularGram_cofinalBursts_of_noVelocityTrace244
      hH3 hClass hL hNoTrace
  refine ⟨ε, hε, ?_⟩
  intro b hb
  obtain ⟨s, t, hs, ht, hst, hLower⟩ := hBursts b hb
  have hsTail : s ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hs.1, hs.2⟩
  have htTail : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 ht.1, ht.2⟩
  have hEq := h3Path_physicalAngularGramAction_integral_eq_unitSpeed244
    hH3 hClass hL s t hsTail htTail hst
  rw [hEq] at hLower
  exact ⟨s, t, hs, ht, hst, hLower⟩

/-- A fixed cofinal angular burst can be placed on an arbitrarily
short strict-time interval. This is stronger than merely finding large angular
length on an unbounded sequence of intervals: their durations tend to zero. -/
theorem h3Path_physicalAngularGram_arbitrarilyShortBursts_of_cofinal244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hBurst : H3PhysicalAngularGramCofinalBursts244 (a := a) hH3) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ δ : ℝ, 0 < δ →
        ∃ s t : ℝ,
          s ∈ Set.Ioo a T ∧ t ∈ Set.Ioo a T ∧
            s ≤ t ∧ t - s < δ ∧
              ε ≤ (∫ r in s..t,
                Real.sqrt (h3PathPhysicalSourceGramDefect244 hH3 r) /
                  velocityH3Energy0At u r) := by
  obtain ⟨ε, hε, hIntervals⟩ := hBurst
  refine ⟨ε, hε, ?_⟩
  intro δ hδ
  have hTδ : T - δ < T := by linarith only [hδ]
  have hUpper : max a (T - δ) < T :=
    max_lt hClass.terminal_start.2 hTδ
  let b : ℝ := (max a (T - δ) + T) / 2
  have hbRange : max a (T - δ) < b ∧ b < T := by
    dsimp [b]
    constructor <;> linarith only [hUpper]
  have hb : b ∈ Set.Ioo a T :=
    ⟨lt_of_le_of_lt (le_max_left a (T - δ)) hbRange.1, hbRange.2⟩
  obtain ⟨s, t, hs, ht, hst, hAction⟩ := hIntervals b hb
  have hsTail : s ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hs.1, hs.2⟩
  have htTail : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 ht.1, ht.2⟩
  have hLower : T - δ ≤ max a (T - δ) := le_max_right a (T - δ)
  have hLength : t - s < δ := by
    linarith only [hLower, hbRange.1, hs.1, ht.2]
  exact ⟨s, t, hsTail, htTail, hst, hLength, hAction⟩

/-- If a positive-mass terminal physical L² trace does not exist, intervals
of arbitrarily short duration retain a fixed positive angular Gram action.
This identifies concentration of angular *length*, not of net displacement. -/
theorem h3Path_physicalAngularGram_arbitrarilyShortBursts_of_noVelocityTrace244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3) (𝓝[<] T) (𝓝 U)) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ δ : ℝ, 0 < δ →
        ∃ s t : ℝ,
          s ∈ Set.Ioo a T ∧ t ∈ Set.Ioo a T ∧
            s ≤ t ∧ t - s < δ ∧
              ε ≤ (∫ r in s..t,
                Real.sqrt (h3PathPhysicalSourceGramDefect244 hH3 r) /
                  velocityH3Energy0At u r) := by
  exact h3Path_physicalAngularGram_arbitrarilyShortBursts_of_cofinal244
    hH3 hClass
      (h3Path_physicalAngularGram_cofinalBursts_of_noVelocityTrace244
        hH3 hClass hL hNoTrace)

/-- With positive terminal kinetic mass, either the physical velocity has
its exact-mass strong terminal trace, or positive angular Gram length persists
cofinally. This is not a claim that the trace itself forces finite length. -/
theorem h3Path_physicalAngularGram_exactMassTrace_or_cofinalBursts244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T) :
    (∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3) (𝓝[<] T) (𝓝 U) ∧
        ‖U‖ ^ 2 = h3PathCanonicalTerminalKineticEnergyAt u a T) ∨
      H3PhysicalAngularGramCofinalBursts244 (a := a) hH3 := by
  by_cases hTrace : ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3) (𝓝[<] T) (𝓝 U)
  · obtain ⟨U, hU⟩ := hTrace
    exact Or.inl ⟨U, hU,
      h3Path_physicalVelocity_terminalTrace_norm_sq_eq_kineticLimit244
        hH3 hClass U hU⟩
  · exact Or.inr
      (h3Path_physicalAngularGram_cofinalBursts_of_noVelocityTrace244
        hH3 hClass hL hTrace)

/-- On any terminal energy class (including zero kinetic mass), either the
actual physical velocity has an exact-mass L² trace, or the normalized angular
Gram length admits fixed positive cofinal bursts. The second branch is possible
only when the terminal kinetic mass is positive. -/
theorem h3Path_physicalAngularGram_allKineticTrace_or_cofinalBursts244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3) (𝓝[<] T) (𝓝 U) ∧
        ‖U‖ ^ 2 = h3PathCanonicalTerminalKineticEnergyAt u a T) ∨
      (0 < h3PathCanonicalTerminalKineticEnergyAt u a T ∧
        H3PhysicalAngularGramCofinalBursts244 (a := a) hH3) := by
  let L : ℝ := h3PathCanonicalTerminalKineticEnergyAt u a T
  by_cases hZero : L = 0
  · left
    refine ⟨0, h3Path_physicalVelocity_tendsto_zero_of_zeroTerminalKinetic244
      hH3 hClass hZero, ?_⟩
    simpa using hZero.symm
  · have hNonneg : 0 ≤ L :=
      h3PathCanonical_terminalKineticEnergy_nonneg hClass
    have hL : 0 < L := lt_of_le_of_ne hNonneg (Ne.symm hZero)
    rcases h3Path_physicalAngularGram_exactMassTrace_or_cofinalBursts244
        hH3 hClass hL with hTrace | hBurst
    · exact Or.inl hTrace
    · exact Or.inr ⟨hL, hBurst⟩

end
end PrimeTensor.FirstMonomialTriad
