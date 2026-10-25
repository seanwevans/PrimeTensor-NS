import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralSignedTransportClock244
import Mathlib.Tactic

/-!
# A fixed cofinal physical H³ signed channel

The moving-radial normalized physical dissipation witness yields, at every
terminal subtail and every prescribed real rate B, a strict-time snapshot
where E' < -B E or B E < -Transport. The disjunction alone does not select
one sign channel uniformly as the threshold and terminal subtail vary.

The finite-channel cofinal principle below closes that logical gap. If the
fast negative energy-slope channel does NOT occur arbitrarily late at every
rate, there is a fixed terminal subtail and a fixed slope floor on that
subtail. Increasing the mixed threshold then forces arbitrarily large
adverse signed transport on *all* terminal subtails.

The result is conditional on positive terminal kinetic mass and failure of
the strong physical kinetic L² trace. It neither derives trace failure from
H³ nonextension nor eliminates either signed branch. It makes the remaining
first-monomial PDE obstruction a fixed cofinal channel.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- An exhaustive cofinal two-channel alternative has ONE cofinal channel
independent of the terminal subtail and of the requested real rate.
Positive E is essential when enlarging the normalized threshold. -/
theorem h3Path_cofinalSignedChannel_fixedBranch244
    {a T : ℝ}
    (E F W : ℝ → ℝ)
    (hPositive : ∀ t : ℝ, t ∈ Set.Ioo a T → 0 < E t)
    (hMixed : ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ B : ℝ,
      ∃ t : ℝ, t ∈ Set.Ioo b T ∧
        (F t < -(B * E t) ∨ B * E t < -W t)) :
    (∀ b : ℝ, b ∈ Set.Ioo a T → ∀ B : ℝ,
      ∃ t : ℝ, t ∈ Set.Ioo b T ∧ F t < -(B * E t)) ∨
    (∀ b : ℝ, b ∈ Set.Ioo a T → ∀ B : ℝ,
      ∃ t : ℝ, t ∈ Set.Ioo b T ∧ B * E t < -W t) := by
  classical
  by_cases hFast :
      ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ B : ℝ,
        ∃ t : ℝ, t ∈ Set.Ioo b T ∧ F t < -(B * E t)
  · exact Or.inl hFast
  · right
    push_neg at hFast
    obtain ⟨b, hb, B, hNoFast⟩ := hFast
    intro c hc C
    let d : ℝ := max b c
    have hd : d ∈ Set.Ioo a T := by
      dsimp only [d]
      exact ⟨lt_of_lt_of_le hb.1 (le_max_left b c),
        max_lt hb.2 hc.2⟩
    obtain ⟨t, ht, hAlternative⟩ := hMixed d hd (max B C)
    have htB : t ∈ Set.Ioo b T :=
      ⟨lt_of_le_of_lt (le_max_left b c) ht.1, ht.2⟩
    have htC : t ∈ Set.Ioo c T :=
      ⟨lt_of_le_of_lt (le_max_right b c) ht.1, ht.2⟩
    have htClass : t ∈ Set.Ioo a T :=
      ⟨lt_trans hd.1 ht.1, ht.2⟩
    have hE : 0 ≤ E t := (hPositive t htClass).le
    have hB : B * E t ≤ max B C * E t :=
      mul_le_mul_of_nonneg_right (le_max_left B C) hE
    have hC : C * E t ≤ max B C * E t :=
      mul_le_mul_of_nonneg_right (le_max_right B C) hE
    rcases hAlternative with hDecay | hTransport
    · exfalso
      have hFloor := hNoFast t htB
      linarith only [hFloor, hB, hDecay]
    · exact ⟨t, htC, lt_of_le_of_lt hC hTransport⟩

/-- The no-kinetic-trace obstruction has a fixed cofinal signed physical
channel, not merely a sign choice which may alternate with n. -/
theorem h3Path_physicalNoL2Trace_forces_fixedCofinalSignedChannel244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    (∀ b : ℝ, b ∈ Set.Ioo a T → ∀ B : ℝ,
      ∃ t : ℝ, t ∈ Set.Ioo b T ∧
        deriv (velocityH3EnergyAt u) t <
          -(B * velocityH3EnergyAt u t)) ∨
    (∀ b : ℝ, b ∈ Set.Ioo a T → ∀ B : ℝ,
      ∃ t : ℝ, t ∈ Set.Ioo b T ∧
        B * velocityH3EnergyAt u t <
          -velocityH3TransportDerivativeAt u t) := by
  have hPositive (t : ℝ) (_ht : t ∈ Set.Ioo a T) :
      0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (one_le_velocityH3EnergyAt u t)
  exact h3Path_cofinalSignedChannel_fixedBranch244
    (velocityH3EnergyAt u)
    (fun t => deriv (velocityH3EnergyAt u) t)
    (velocityH3TransportDerivativeAt u)
    hPositive
    (h3Path_physicalNoL2Trace_forces_cofinalSignedTransport_or_fastDecay244
      hH3 hClass hL hNoTrace)

/-- If physical H³ energy does not decay faster than a fixed exponential
rate on a terminal subtail, kinetic trace failure forces the adverse signed
H³ transport channel to be cofinally unbounded relative to H³ energy. -/
theorem h3Path_physicalSlopeFloor_forces_cofinalAdverseTransport244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (B : ℝ)
    (hSlope : ∀ t : ℝ, t ∈ Set.Ioo b T →
      -(B * velocityH3EnergyAt u t) ≤
        deriv (velocityH3EnergyAt u) t) :
    ∀ c : ℝ, c ∈ Set.Ioo b T → ∀ C : ℝ,
      ∃ t : ℝ, t ∈ Set.Ioo c T ∧
        C * velocityH3EnergyAt u t <
          -velocityH3TransportDerivativeAt u t := by
  intro c hc C
  have hcClass : c ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hc.1, hc.2⟩
  obtain ⟨t, ht, hAlternative⟩ :=
    h3Path_physicalNoL2Trace_forces_cofinalSignedTransport_or_fastDecay244
      hH3 hClass hL hNoTrace c hcClass (max B C)
  have htB : t ∈ Set.Ioo b T :=
    ⟨lt_trans hc.1 ht.1, ht.2⟩
  have hE : 0 ≤ velocityH3EnergyAt u t :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1)
      (one_le_velocityH3EnergyAt u t)
  rcases hAlternative with hDecay | hTransport
  · have hScaled : B * velocityH3EnergyAt u t ≤
        max B C * velocityH3EnergyAt u t :=
      mul_le_mul_of_nonneg_right (le_max_left B C) hE
    have hFloor := hSlope t htB
    exfalso
    linarith only [hScaled, hFloor, hDecay]
  · have hScaled : C * velocityH3EnergyAt u t ≤
        max B C * velocityH3EnergyAt u t :=
      mul_le_mul_of_nonneg_right (le_max_right B C) hE
    exact ⟨t, ht, lt_of_le_of_lt hScaled hTransport⟩

/-- Dually, a fixed ceiling on the adverse signed transport forces cofinal
arbitrarily rapid *negative* physical H³ logarithmic energy slopes on the
no-L²-trace branch. This is not asserted to contradict finite-time smoothness. -/
theorem h3Path_physicalTransportCeiling_forces_cofinalFastEnergyDecay244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (B : ℝ)
    (hTransport : ∀ t : ℝ, t ∈ Set.Ioo b T →
      -velocityH3TransportDerivativeAt u t ≤
        B * velocityH3EnergyAt u t) :
    ∀ c : ℝ, c ∈ Set.Ioo b T → ∀ C : ℝ,
      ∃ t : ℝ, t ∈ Set.Ioo c T ∧
        deriv (velocityH3EnergyAt u) t <
          -(C * velocityH3EnergyAt u t) := by
  intro c hc C
  have hcClass : c ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hc.1, hc.2⟩
  obtain ⟨t, ht, hAlternative⟩ :=
    h3Path_physicalNoL2Trace_forces_cofinalSignedTransport_or_fastDecay244
      hH3 hClass hL hNoTrace c hcClass (max B C)
  have htB : t ∈ Set.Ioo b T :=
    ⟨lt_trans hc.1 ht.1, ht.2⟩
  have hE : 0 ≤ velocityH3EnergyAt u t :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1)
      (one_le_velocityH3EnergyAt u t)
  rcases hAlternative with hDecay | hAdverse
  · have hScaled : C * velocityH3EnergyAt u t ≤
        max B C * velocityH3EnergyAt u t :=
      mul_le_mul_of_nonneg_right (le_max_right B C) hE
    refine ⟨t, ht, ?_⟩
    linarith only [hScaled, hDecay]
  · have hScaled : B * velocityH3EnergyAt u t ≤
        max B C * velocityH3EnergyAt u t :=
      mul_le_mul_of_nonneg_right (le_max_left B C) hE
    have hCeiling := hTransport t htB
    exfalso
    linarith only [hScaled, hCeiling, hAdverse]

end
end PrimeTensor.FirstMonomialTriad
