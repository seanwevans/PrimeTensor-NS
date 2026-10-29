import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorHigherRadialMoment244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Order.Radial.Escape
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Extended.Higher.Radial.Moment.Cascade
import Mathlib.Tactic

/-!
# Exact canonical H³ high-frequency dissipation bridges to physical top-order moments

For gradient magnitude at least one, the physical full H³ Fourier dissipation
is bounded by four times its top-order q^4 Fourier density. The established
higher-radial moment coercivity estimates then give, at each physical slice,

  ofReal ((Q²)^m * H_Q(t) / 4) ≤ M_{4+m}⁺(t),       Q ≥ 1.

This is an inequality between actual physical quantities, not an assumed
identification of the full and top-order H³ dissipation densities. It gives
canonical near-total tail concentration an explicit necessary cost in the
existing extended higher-radial moments, on the original unmodified anchors.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology ENNReal

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeH3CanonicalTopHigherRadial244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3CanonicalTopHigherRadial244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Full physical high-Q dissipation is at most four times the ACTUAL
physical top-order dissipation on that high-frequency set, for Q ≥ 1. -/
theorem h3Path_physicalHighTail_le_fourTopOrderTail244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T)
    (Q : ℝ) (hQ : 1 ≤ Q) :
    h3PathActualHighRadialDissipation244 Q
      (h3AuditActualSpectralVelocityTotal hH3 t) ≤
    4 * h3TerminalPhysicalTopDissipationSetMassAt hH3 hClass t ht
      ((h3TerminalRadialFrequencyBelow Q)ᶜ) := by
  let S : Set H3FourierPoint3 := (h3TerminalRadialFrequencyBelow Q)ᶜ
  have hS : MeasurableSet S :=
    (measurableSet_h3TerminalRadialFrequencyBelow Q).compl
  have hOne : ∀ ξ ∈ S, 1 ≤ h3FourierGradientMagnitude ξ := by
    intro ξ hξ
    have hOutside : ¬ h3FourierGradientMagnitude ξ < Q := by
      simpa only [S, h3TerminalRadialFrequencyBelow, Set.mem_ofPred_eq,
        Set.mem_compl_iff] using hξ
    exact hQ.trans (le_of_not_gt hOutside)
  have hTop :=
    physicalDissipationSetMass_le_four_mul_topDissipationSetMass_of_one_le_gradientMagnitude
      hH3 hClass ht S hS hOne
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  rw [h3Path_actualSpectralVelocity_eq_terminalState244 hH3 t htAbs]
  change h3TerminalPhysicalDissipationSetMassAt hH3 hClass t ht S ≤
    4 * h3TerminalPhysicalTopDissipationSetMassAt hH3 hClass t ht S
  exact hTop

/-- At Q ≥ 1, the existing q^(4+m) physical extended moment pays the
high-frequency share of full H³ dissipation, with the rigorous factor 1/4. -/
theorem h3Path_physicalHighTail_forces_topHigherRadialMoment244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T)
    (m : ℕ) (Q : ℝ) (hQ : 1 ≤ Q) :
    ENNReal.ofReal ((Q ^ 2) ^ m *
      (h3PathActualHighRadialDissipation244 Q
        (h3AuditActualSpectralVelocityTotal hH3 t) / 4)) ≤
      h3TerminalPhysicalExtendedHigherRadialMomentAt hH3 hClass m t ht := by
  let S : Set H3FourierPoint3 := (h3TerminalRadialFrequencyBelow Q)ᶜ
  have hS : MeasurableSet S :=
    (measurableSet_h3TerminalRadialFrequencyBelow Q).compl
  have hFour := h3Path_physicalHighTail_le_fourTopOrderTail244
    hH3 hClass t ht Q hQ
  have hQuarter :
      h3PathActualHighRadialDissipation244 Q
        (h3AuditActualSpectralVelocityTotal hH3 t) / 4 ≤
      h3TerminalPhysicalTopDissipationSetMassAt hH3 hClass t ht S := by
    change _ ≤ 4 * h3TerminalPhysicalTopDissipationSetMassAt hH3 hClass t ht S at hFour
    linarith only [hFour]
  have hScaled :
      (Q ^ 2) ^ m *
        (h3PathActualHighRadialDissipation244 Q
          (h3AuditActualSpectralVelocityTotal hH3 t) / 4) ≤
      (Q ^ 2) ^ m *
        h3TerminalPhysicalTopDissipationSetMassAt hH3 hClass t ht S :=
    mul_le_mul_of_nonneg_left hQuarter (by positivity)
  have hOutside : S ⊆ (h3TerminalRadialFrequencyBelow Q)ᶜ := by
    intro ξ hξ
    exact hξ
  have hCoercive :=
    ofReal_radial_sq_pow_mul_topDissipationSetMass_le_extendedHigherRadialMoment_of_setOutside
      hH3 hClass m ht (by linarith only [hQ] : 0 ≤ Q) S hS hOutside
  exact (ENNReal.ofReal_le_ofReal hScaled).trans hCoercive

/-- A specified actual canonical high-tail fraction transfers to the genuine
physical top-order q^(4+m) radial hierarchy, without assuming finiteness. -/
theorem h3Path_exactAnchor_highTail_forces_topHigherRadialMoment244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ) (N : ℕ → ℕ) (v : ℕ → ℕ)
    (k m : ℕ) (β : ℝ)
    (ht : τ (v k) ∈ Set.Ioo a T)
    (hHigh : β * velocityH3DissipationAt u (τ (v k)) <
      h3PathActualHighRadialDissipation244 ((N (v k) : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))) :
    ENNReal.ofReal ((((N (v k) : ℝ) + 1) ^ 2) ^ m *
      (β * velocityH3DissipationAt u (τ (v k)) / 4)) ≤
      h3TerminalPhysicalExtendedHigherRadialMomentAt
        hH3 hClass m (τ (v k)) ht := by
  let Q : ℝ := (N (v k) : ℝ) + 1
  have hQ : 1 ≤ Q := by
    dsimp only [Q]
    have hN : (0 : ℝ) ≤ (N (v k) : ℝ) := Nat.cast_nonneg _
    linarith only [hN]
  have hQuarter : β * velocityH3DissipationAt u (τ (v k)) / 4 ≤
      h3PathActualHighRadialDissipation244 Q
        (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) / 4 := by
    dsimp only [Q]
    linarith only [hHigh]
  have hScaled := mul_le_mul_of_nonneg_left hQuarter
    (show 0 ≤ (Q ^ 2) ^ m by positivity)
  have hMoment := h3Path_physicalHighTail_forces_topHigherRadialMoment244
    hH3 hClass (τ (v k)) ht m Q hQ
  exact (ENNReal.ofReal_le_ofReal hScaled).trans hMoment

/-- The original canonical exact-anchor disjoint witnesses now control the
EXISTING physical top-order higher moments, not a parallel full-density
surrogate. Both branches retain the original quantified cutoff and clock. -/
theorem h3Path_noL2Trace_exactAnchor_chargeOrTopHigherRadialMoment244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ) (v : ℕ → ℕ),
    ∃ hτ : (∀ n, τ n ∈ Set.Ioo a T),
      StrictMono v ∧
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ k l, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      (∀ k, K (v k) =
        ‖h3AuditActualSpectralVelocityTotal hH3 (τ (v k))‖ ∧
        C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
          (τ (v k)) (τ (v k) + (T - τ (v k)) / 2) ∧
        0 < δ (v k)) ∧
      (∀ m : ℕ, ∀ β ε : ℝ, β < 1 → 0 < ε → ∀ᶠ k : ℕ in atTop,
        δ (v k) * velocityH3DissipationAt u (τ (v k)) ≤ ε ∨
        ENNReal.ofReal ((((N (v k) : ℝ) + 1) ^ 2) ^ m *
          (β * velocityH3DissipationAt u (τ (v k)) / 4)) ≤
          h3TerminalPhysicalExtendedHigherRadialMomentAt
            hH3 hClass m (τ (v k)) (hτ (v k))) ∧
      (∀ η : ℝ, 0 < η →
        (∀ᶠ k : ℕ in atTop,
          η ≤ δ (v k) * velocityH3DissipationAt u (τ (v k))) →
        ∀ m : ℕ, ∀ β : ℝ, β < 1 → ∀ᶠ k : ℕ in atTop,
          ENNReal.ofReal ((((N (v k) : ℝ) + 1) ^ 2) ^ m *
            (β * velocityH3DissipationAt u (τ (v k)) / 4)) ≤
          h3TerminalPhysicalExtendedHigherRadialMomentAt
            hH3 hClass m (τ (v k)) (hτ (v k))) := by
  obtain ⟨τ, N, K, C, δ, v, hv, hCofinal, hTime,
      hSeparate, hCanonical, _hLowCost, _hSummable, hAlt, hPersistent⟩ :=
    h3Path_noL2Trace_exactAnchor_lowChargeOrNearFullHighTail244
      hH3 hClass hMass hNoTrace hDInt
  refine ⟨τ, N, K, C, δ, v, hTime, hv, hCofinal,
    hSeparate, hCanonical, ?_, ?_⟩
  · intro m β ε hβ hε
    have hOld := hAlt β ε hβ hε
    filter_upwards [hOld] with k hk
    rcases hk with hSmall | hHigh
    · exact Or.inl hSmall
    · exact Or.inr (h3Path_exactAnchor_highTail_forces_topHigherRadialMoment244
        hH3 hClass τ N v k m β (hTime (v k)) hHigh)
  · intro η hη hPersist m β hβ
    have hOld := hPersistent η hη hPersist β hβ
    filter_upwards [hOld] with k hk
    exact h3Path_exactAnchor_highTail_forces_topHigherRadialMoment244
      hH3 hClass τ N v k m β (hTime (v k)) hk

end
end PrimeTensor.FirstMonomialTriad
