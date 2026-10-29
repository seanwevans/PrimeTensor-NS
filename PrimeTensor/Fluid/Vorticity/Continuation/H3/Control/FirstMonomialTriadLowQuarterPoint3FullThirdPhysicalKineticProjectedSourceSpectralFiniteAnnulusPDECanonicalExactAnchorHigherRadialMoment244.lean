import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorNearFullHighTail244
import Mathlib.Tactic

/-!
# Canonical high-tail H³ dissipation forces every higher full-dissipation moment

This is the extended radial moment of the ENTIRE physical H³ dissipative
Fourier density, weighted by |D(ξ)|^(2m). It is not silently identified with
the distinct top-only q^(4+m) velocity moment elsewhere in the repository.
The integrals take values in ENNReal, so no extra integrability or false
zero-value convention for nonintegrable higher derivatives is introduced.
The same exact canonical disjoint witnesses are retained throughout.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology ENNReal

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeH3CanonicalHigherRadialMoment244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3CanonicalHigherRadialMoment244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Genuine extended radial moment of the FULL H³ dissipative density.
For m = 0 it is the original total dissipation, as an extended integral;
for m > 0 it contains 2m additional radial derivatives. -/
noncomputable def h3PathActualExtendedFullDissipationMoment244
    (m : ℕ) (G : H3SpectralVelocityState) : ℝ≥0∞ :=
  ∫⁻ ξ : H3FourierPoint3,
    ENNReal.ofReal
      ((h3FourierGradientMagnitude ξ ^ 2) ^ m *
        h3TerminalSpectralDissipationSingleDensity G ξ) ∂volume

/-- A high-frequency dissipation mass necessarily costs Q^(2m) in
its mth additional full-dissipation radial moment. The target is ENNReal;
no finite upper moment or Fourier differentiation hypothesis is assumed. -/
theorem h3Path_extendedFullDissipationMoment_ge_highTailPower244
    (G : H3SpectralVelocityState) (m : ℕ) (Q : ℝ)
    (hQ : 0 ≤ Q)
    (hInt : Integrable (h3TerminalSpectralDissipationSingleDensity G) volume) :
    ENNReal.ofReal ((Q ^ 2) ^ m * h3PathActualHighRadialDissipation244 Q G) ≤
      h3PathActualExtendedFullDissipationMoment244 m G := by
  let S : Set H3FourierPoint3 := (h3TerminalRadialFrequencyBelow Q)ᶜ
  let D : H3FourierPoint3 → ℝ :=
    h3TerminalSpectralDissipationSingleDensity G
  let F : H3FourierPoint3 → ℝ := fun ξ =>
    (h3FourierGradientMagnitude ξ ^ 2) ^ m * D ξ
  have hS : MeasurableSet S :=
    (measurableSet_h3TerminalRadialFrequencyBelow Q).compl
  have hDNonneg : 0 ≤ᵐ[volume.restrict S] D := by
    filter_upwards with ξ
    exact h3TerminalSpectralDissipationSingleDensity_nonneg G ξ
  have hBridge : ENNReal.ofReal (∫ ξ in S, D ξ ∂volume) =
      ∫⁻ ξ in S, ENNReal.ofReal (D ξ) ∂volume := by
    exact ofReal_integral_eq_lintegral_ofReal hInt.integrableOn hDNonneg
  have hPoint (ξ : H3FourierPoint3) (hξ : ξ ∈ S) :
      (Q ^ 2) ^ m * D ξ ≤ F ξ := by
    have hOutside : ¬ h3FourierGradientMagnitude ξ < Q := by
      simpa only [S, h3TerminalRadialFrequencyBelow, Set.mem_ofPred_eq,
        Set.mem_compl_iff] using hξ
    have hGrad : Q ≤ h3FourierGradientMagnitude ξ :=
      le_of_not_gt hOutside
    have hSq : Q ^ 2 ≤ h3FourierGradientMagnitude ξ ^ 2 :=
      pow_le_pow_left₀ hQ hGrad 2
    have hPow : (Q ^ 2) ^ m ≤ (h3FourierGradientMagnitude ξ ^ 2) ^ m :=
      pow_le_pow_left₀ (sq_nonneg Q) hSq m
    dsimp only [F]
    exact mul_le_mul_of_nonneg_right hPow
      (h3TerminalSpectralDissipationSingleDensity_nonneg G ξ)
  have hRestrict :
      (∫⁻ ξ in S, ENNReal.ofReal ((Q ^ 2) ^ m * D ξ) ∂volume) ≤
      (∫⁻ ξ in S, ENNReal.ofReal (F ξ) ∂volume) := by
    apply setLIntegral_mono' hS
    intro ξ hξ
    exact ENNReal.ofReal_le_ofReal (hPoint ξ hξ)
  have hWhole :
      (∫⁻ ξ in S, ENNReal.ofReal (F ξ) ∂volume) ≤
      (∫⁻ ξ : H3FourierPoint3, ENNReal.ofReal (F ξ) ∂volume) := by
    exact lintegral_mono' Measure.restrict_le_self le_rfl
  unfold h3PathActualHighRadialDissipation244
    h3PathActualExtendedFullDissipationMoment244
  change ENNReal.ofReal ((Q ^ 2) ^ m * (∫ ξ in S, D ξ ∂volume)) ≤
    ∫⁻ ξ : H3FourierPoint3, ENNReal.ofReal (F ξ) ∂volume
  calc
    ENNReal.ofReal ((Q ^ 2) ^ m * (∫ ξ in S, D ξ ∂volume)) =
        ENNReal.ofReal ((Q ^ 2) ^ m) *
          ENNReal.ofReal (∫ ξ in S, D ξ ∂volume) := by
            rw [ENNReal.ofReal_mul (pow_nonneg (sq_nonneg Q) m)]
    _ = ENNReal.ofReal ((Q ^ 2) ^ m) *
          (∫⁻ ξ in S, ENNReal.ofReal (D ξ) ∂volume) := by
            rw [hBridge]
    _ = ∫⁻ ξ in S,
          ENNReal.ofReal ((Q ^ 2) ^ m) * ENNReal.ofReal (D ξ) ∂volume := by
            symm
            exact lintegral_const_mul'
              (ENNReal.ofReal ((Q ^ 2) ^ m))
              (fun ξ => ENNReal.ofReal (D ξ)) ENNReal.ofReal_lt_top.ne
    _ = ∫⁻ ξ in S,
          ENNReal.ofReal ((Q ^ 2) ^ m * D ξ) ∂volume := by
            apply setLIntegral_congr_fun hS
            intro ξ hξ
            exact (ENNReal.ofReal_mul (pow_nonneg (sq_nonneg Q) m)).symm
    _ ≤ ∫⁻ ξ in S, ENNReal.ofReal (F ξ) ∂volume := hRestrict
    _ ≤ ∫⁻ ξ : H3FourierPoint3, ENNReal.ofReal (F ξ) ∂volume := hWhole

/-- Physical transfer at a genuine preterminal snapshot. -/
theorem h3Path_actualPhysicalExtendedFullMoment_ge_highTailPower244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T) (m : ℕ)
    (Q : ℝ) (hQ : 0 ≤ Q) :
    ENNReal.ofReal ((Q ^ 2) ^ m *
        h3PathActualHighRadialDissipation244 Q
          (h3AuditActualSpectralVelocityTotal hH3 t)) ≤
      h3PathActualExtendedFullDissipationMoment244 m
        (h3AuditActualSpectralVelocityTotal hH3 t) := by
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  have hInt : Integrable
      (h3TerminalSpectralDissipationSingleDensity
        (h3AuditActualSpectralVelocityTotal hH3 t)) volume := by
    rw [h3Path_actualSpectralVelocity_eq_terminalState244 hH3 t htAbs]
    exact h3TerminalSpectralDissipationSingleDensity_integrable hH3 hClass ht
  exact h3Path_extendedFullDissipationMoment_ge_highTailPower244
    (h3AuditActualSpectralVelocityTotal hH3 t) m Q hQ hInt

/-- On the identical canonical time and outer cutoff, a large high tail
forces the full extended moment to carry its exact polynomial frequency cost. -/
theorem h3Path_exactAnchor_highTail_forces_extendedMoment244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ) (N : ℕ → ℕ) (v : ℕ → ℕ)
    (k m : ℕ) (β : ℝ)
    (ht : τ (v k) ∈ Set.Ioo a T)
    (hβ : β * velocityH3DissipationAt u (τ (v k)) <
      h3PathActualHighRadialDissipation244 ((N (v k) : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))) :
    ENNReal.ofReal ((((N (v k) : ℝ) + 1) ^ 2) ^ m *
      (β * velocityH3DissipationAt u (τ (v k)))) ≤
      h3PathActualExtendedFullDissipationMoment244 m
        (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) := by
  have hQ : 0 ≤ (N (v k) : ℝ) + 1 := by positivity
  have hPower : 0 ≤ (((N (v k) : ℝ) + 1) ^ 2) ^ m :=
    pow_nonneg (sq_nonneg _) m
  have hMul := mul_le_mul_of_nonneg_left hβ.le hPower
  have hMoment := h3Path_actualPhysicalExtendedFullMoment_ge_highTailPower244
    hH3 hClass (τ (v k)) ht m ((N (v k) : ℝ) + 1) hQ
  exact (ENNReal.ofReal_le_ofReal hMul).trans hMoment

/-- Co-final original disjoint clocks: for every additional radial order m,
either the instantaneous physical peak charge collapses, or the full
higher dissipation moment bears a polynomially amplified high-tail charge.
No finiteness of this new moment is assumed. -/
theorem h3Path_noL2Trace_exactAnchor_chargeOrHigherRadialMoment244
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
      StrictMono v ∧
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ n, τ n ∈ Set.Ioo a T) ∧
      (∀ k l, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      (∀ k, K (v k) =
        ‖h3AuditActualSpectralVelocityTotal hH3 (τ (v k))‖ ∧
        C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
          (τ (v k)) (τ (v k) + (T - τ (v k)) / 2) ∧
        0 < δ (v k)) ∧
      (∀ m : ℕ, ∀ β ε : ℝ, β < 1 → 0 < ε → ∀ᶠ k : ℕ in atTop,
        δ (v k) * velocityH3DissipationAt u (τ (v k)) ≤ ε ∨
        ENNReal.ofReal ((((N (v k) : ℝ) + 1) ^ 2) ^ m *
          (β * velocityH3DissipationAt u (τ (v k)))) ≤
          h3PathActualExtendedFullDissipationMoment244 m
            (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))) ∧
      (∀ η : ℝ, 0 < η →
        (∀ᶠ k : ℕ in atTop,
          η ≤ δ (v k) * velocityH3DissipationAt u (τ (v k))) →
        ∀ m : ℕ, ∀ β : ℝ, β < 1 → ∀ᶠ k : ℕ in atTop,
          ENNReal.ofReal ((((N (v k) : ℝ) + 1) ^ 2) ^ m *
            (β * velocityH3DissipationAt u (τ (v k)))) ≤
          h3PathActualExtendedFullDissipationMoment244 m
            (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))) := by
  obtain ⟨τ, N, K, C, δ, v, hv, hCofinal, hTime,
      hSeparate, hCanonical, _hLowCost, _hSummable, hAlt, hPersistent⟩ :=
    h3Path_noL2Trace_exactAnchor_lowChargeOrNearFullHighTail244
      hH3 hClass hMass hNoTrace hDInt
  refine ⟨τ, N, K, C, δ, v, hv, hCofinal, hTime,
    hSeparate, hCanonical, ?_, ?_⟩
  · intro m β ε hβ hε
    have hOld := hAlt β ε hβ hε
    filter_upwards [hOld] with k hk
    rcases hk with hSmall | hHigh
    · exact Or.inl hSmall
    · exact Or.inr (h3Path_exactAnchor_highTail_forces_extendedMoment244
        hH3 hClass τ N v k m β (hTime (v k)) hHigh)
  · intro η hη hPersist m β hβ
    have hOld := hPersistent η hη hPersist β hβ
    filter_upwards [hOld] with k hk
    exact h3Path_exactAnchor_highTail_forces_extendedMoment244
      hH3 hClass τ N v k m β (hTime (v k)) hk

end
end PrimeTensor.FirstMonomialTriad
