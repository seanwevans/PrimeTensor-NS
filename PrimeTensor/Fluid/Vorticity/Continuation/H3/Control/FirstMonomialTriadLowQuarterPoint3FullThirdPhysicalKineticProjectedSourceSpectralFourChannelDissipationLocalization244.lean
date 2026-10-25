import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFastDecayDissipationLocalization244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralSignedCubicRadialSynchronization244
import Mathlib.Tactic

/-!
# A four-channel moving-radial H³ dissipation-localization alternative

The fixed cofinal no-kinetic-L²-trace corridor consists of rapidly negative
physical H³ energy slopes, high H³ energy, negative canonical 972-gradient
transport, or negative signed first-monomial transport (factor three).
Each of these fixed channels now has a terminal sequence on which genuine
physical H³ dissipation above radius n+1 dominates lower-radius dissipation
by a factor n+1. For the last three arms this follows from simultaneous
high-radial spectral H³ energy dominance; the first uses the independently
proved direct-viscous localization and does not assert energy-mass dominance.

The high/low dissipation partition implies the high share tends to one.
This is a common *existential* terminal mechanism, not intersection of four
separately selected witnesses, and is conditional on strong kinetic L² trace
failure with positive terminal kinetic mass. The last theorem retains the
alternative of a strong terminal kinetic trace with its exact canonical mass.
No smooth continuation or Navier--Stokes regularity conclusion is asserted.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- A purely algebraic moving-cutoff fact. Dominance of the high radial
part of a positive partition at factor n+1 forces its share to approach one. -/
theorem h3Path_highLowDissipationSequence_highShare_tendsto_one244
    (L H : ℕ → ℝ)
    (hL : ∀ n : ℕ, 0 ≤ L n)
    (hDom : ∀ n : ℕ, ((n : ℝ) + 1) * L n < H n) :
    Tendsto (fun n : ℕ => H n / (L n + H n)) atTop (𝓝 1) := by
  let D : ℕ → ℝ := fun n => L n + H n
  have hPositive (n : ℕ) : 0 < D n := by
    dsimp only [D]
    exact (h3Path_highDissipationDominance_lowShare_bound244
      ((n : ℝ) + 1) (L n) (H n) (by positivity) (hL n) (hDom n)).1
  have hLowShare (n : ℕ) :
      0 ≤ L n / D n ∧ L n / D n < 1 / ((n : ℝ) + 2) := by
    have hShare := (h3Path_highDissipationDominance_lowShare_bound244
      ((n : ℝ) + 1) (L n) (H n) (by positivity) (hL n) (hDom n)).2
    simpa only [D, show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring]
      using hShare
  have hNorm (n : ℕ) :
      ‖L n / D n‖ ≤ 1 / ((n : ℝ) + 1) := by
    have hR : 0 < (n : ℝ) + 1 := by positivity
    have hDen : (n : ℝ) + 1 ≤ (n : ℝ) + 2 := by linarith
    have hInv : (1 : ℝ) / ((n : ℝ) + 2) ≤
        1 / ((n : ℝ) + 1) := one_div_le_one_div_of_le hR hDen
    rw [Real.norm_eq_abs, abs_of_nonneg (hLowShare n).1]
    exact le_trans (le_of_lt (hLowShare n).2) hInv
  have hInv : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
      atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hLowLimit : Tendsto (fun n : ℕ => L n / D n)
      atTop (𝓝 0) :=
    (tendsto_iff_norm_sub_tendsto_zero).2
      (by simpa only [sub_zero] using
        (squeeze_zero'
          (Filter.Eventually.of_forall (fun n => norm_nonneg (L n / D n)))
          (Filter.Eventually.of_forall hNorm) hInv))
  have hHighRatio (n : ℕ) : H n / D n = 1 - L n / D n := by
    have hD : D n ≠ 0 := ne_of_gt (hPositive n)
    have hDH : H n = D n - L n := by
      dsimp only [D]
      ring
    rw [hDH]
    field_simp [hD]
    <;> ring
  have hLimit : Tendsto (fun n : ℕ => 1 - L n / D n)
      atTop (𝓝 (1 - 0)) := tendsto_const_nhds.sub hLowLimit
  simpa only [sub_zero, ← hHighRatio] using hLimit

/-- Any *single* moving-cutoff sequence with radial H³ spectral-energy
mass dominance also localizes its physical H³ viscous dissipation. -/
theorem h3Path_radialMassSequence_forces_highDissipationLocalization244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hDom : ∀ n : ℕ,
      ((n : ℝ) + 2) *
        h3PathActualSpectralHighRadialRemainder244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 (τ n)) >
      ((n : ℝ) + 1) *
        h3SpectralVelocitySquareEnergy
          (h3AuditActualSpectralVelocityTotal hH3 (τ n))) :
    (∀ n : ℕ,
      ((n : ℝ) + 1) *
        h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 (τ n)) <
      h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 (τ n))) ∧
    Tendsto (fun n : ℕ =>
      h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 (τ n)) /
      velocityH3DissipationAt u (τ n)) atTop (𝓝 1) := by
  let L : ℕ → ℝ := fun n =>
    h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
      (h3AuditActualSpectralVelocityTotal hH3 (τ n))
  let H : ℕ → ℝ := fun n =>
    h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
      (h3AuditActualSpectralVelocityTotal hH3 (τ n))
  have hShare (n : ℕ) : ((n : ℝ) + 1) * L n < H n := by
    have h := h3Path_radialMassDominance_forces_dissipationDominance244
      hH3 hClass (τ n) (hτ n) ((n : ℝ) + 1) (by positivity)
      (by
        simpa only [show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring]
          using hDom n)
    exact h
  have hLNonneg (n : ℕ) : 0 ≤ L n := by
    dsimp only [L, h3PathActualLowRadialDissipation244]
    apply integral_nonneg
    intro ξ
    exact h3TerminalSpectralDissipationSingleDensity_nonneg
      (h3AuditActualSpectralVelocityTotal hH3 (τ n)) ξ
  have hPartition (n : ℕ) :
      L n + H n = velocityH3DissipationAt u (τ n) := by
    dsimp only [L, H]
    exact h3Path_actualRadialDissipation_partition244
      hH3 hClass (τ n) (hτ n) ((n : ℝ) + 1)
  have hRatio :=
    h3Path_highLowDissipationSequence_highShare_tendsto_one244
      L H hLNonneg hShare
  have hEqual : (fun n : ℕ => H n / (L n + H n)) =
      (fun n : ℕ => H n / velocityH3DissipationAt u (τ n)) := by
    funext n
    rw [hPartition n]
  rw [hEqual] at hRatio
  exact ⟨hShare, by simpa only [H] using hRatio⟩

/-- Consolidated four-channel conclusion. Failure of strong physical
kinetic L² endpoint convergence and positive terminal kinetic mass force
ONE moving-cutoff sequence whose high-radial physical H³ dissipation
occupies asymptotically all of the total dissipation. The cofinal branch
is fixed before selecting the sequence. -/
theorem h3Path_physicalNoL2Trace_forces_highRadialDissipationLocalization244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ τ : ℕ → ℝ,
      (∀ n : ℕ, τ n ∈ Set.Ioo a T) ∧
      (∀ n : ℕ, dist (τ n) T < (1 : ℝ) / ((n : ℝ) + 1)) ∧
      Tendsto τ atTop (𝓝 T) ∧
      (∀ n : ℕ,
        ((n : ℝ) + 1) *
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n)) <
          h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n))) ∧
      Tendsto (fun n : ℕ =>
        h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 (τ n)) /
        velocityH3DissipationAt u (τ n)) atTop (𝓝 1) := by
  rcases h3Path_physicalNoL2Trace_fixedFourChannelCofinality244
      hH3 hClass hL hNoTrace with hFast | hHigh | hGradient | hInterpolation
  · obtain ⟨τ, hτ, hNear, hLimit, _hSlope, hShare, hRatio⟩ :=
      h3Path_cofinalFastDecay_forces_highRadialDissipationLocalization244
        hH3 hClass hFast
    exact ⟨τ, hτ, hNear, hLimit, hShare, hRatio⟩
  · obtain ⟨τ, hτ, hNear, hLimit, hDom, _hClock, _hDiverges⟩ :=
      h3Path_cofinalHighEnergy_forces_jointRadialSequence244
        hH3 hClass hHigh
    obtain ⟨hShare, hRatio⟩ :=
      h3Path_radialMassSequence_forces_highDissipationLocalization244
        hH3 hClass τ hτ hDom
    exact ⟨τ, hτ, hNear, hLimit, hShare, hRatio⟩
  · obtain ⟨τ, hτ, hNear, hLimit, _hSigned, hDom, _hClock⟩ :=
      h3Path_cofinalNegativeGradient_forces_jointRadialSequence244
        hH3 hClass hGradient
    obtain ⟨hShare, hRatio⟩ :=
      h3Path_radialMassSequence_forces_highDissipationLocalization244
        hH3 hClass τ hτ hDom
    exact ⟨τ, hτ, hNear, hLimit, hShare, hRatio⟩
  · obtain ⟨τ, hτ, hNear, hLimit, _hSigned, hDom, _hClock⟩ :=
      h3Path_cofinalNegativeInterpolation_forces_jointRadialSequence244
        hH3 hClass hInterpolation
    obtain ⟨hShare, hRatio⟩ :=
      h3Path_radialMassSequence_forces_highDissipationLocalization244
        hH3 hClass τ hτ hDom
    exact ⟨τ, hτ, hNear, hLimit, hShare, hRatio⟩

/-- Neutral kinetic endpoint alternative: either the actual physical
velocity has a strong L² terminal trace with exactly the canonical kinetic
mass, or one sequence approaching T has asymptotically all full H³
physical dissipation beyond frequency radius n+1. This is an alternative,
not a proof that smooth continuation exists or fails. -/
theorem h3Path_physicalL2Trace_or_highRadialDissipationLocalization244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U) ∧
      ‖U‖ ^ 2 = h3PathCanonicalTerminalKineticEnergyAt u a T) ∨
    (∃ τ : ℕ → ℝ,
      (∀ n : ℕ, τ n ∈ Set.Ioo a T) ∧
      (∀ n : ℕ, dist (τ n) T < (1 : ℝ) / ((n : ℝ) + 1)) ∧
      Tendsto τ atTop (𝓝 T) ∧
      (∀ n : ℕ,
        ((n : ℝ) + 1) *
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n)) <
          h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n))) ∧
      Tendsto (fun n : ℕ =>
        h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 (τ n)) /
        velocityH3DissipationAt u (τ n)) atTop (𝓝 1)) := by
  by_cases hTrace : ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)
  · obtain ⟨U, hU⟩ := hTrace
    exact Or.inl ⟨U, hU,
      h3Path_physicalVelocity_terminalTrace_norm_sq_eq_kineticLimit244
        hH3 hClass U hU⟩
  · right
    have hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T := by
      rcases h3Path_physicalL2Trace_or_allHighRadialRemainderEscape244
          hH3 hClass with hGood | hEscape
      · obtain ⟨U, hU, _⟩ := hGood
        exact False.elim (hTrace ⟨U, hU⟩)
      · exact hEscape.1
    exact h3Path_physicalNoL2Trace_forces_highRadialDissipationLocalization244
      hH3 hClass hL hTrace

end
end PrimeTensor.FirstMonomialTriad
