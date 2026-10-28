import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalPeakFrequencyCoercivity244
import Mathlib.Tactic

/-!
# Actual canonical H³ spectral peaks: unbounded dissipation-to-energy ratio

The previous fixed-radius theorem says that for every real cutoff rho >= 0,

  (rho^2/2) * ‖U₃(s_k)‖² <= D₃(s_k)

eventually along an actual spectral peak sequence with diverging weighted H³
norm. Because rho can be FIXED arbitrarily large after specifying the
requested amplification coefficient, this yields

  forall M, eventually M * ‖U₃(s_k)‖² <= D₃(s_k),
  D₃(s_k) / ‖U₃(s_k)‖² -> +infinity.

This is stronger than divergence of D alone: the physical dissipation-to-H³
amplitude-square ratio diverges on the ORIGINAL peak sequence, without
choosing an additional subsequence or claiming a power-law rate in amplitude.

The actual physical kinetic anchor also bounds low-frequency H³ dissipation
for any fixed radial ball. Thus full dissipation divergence implies eventual
arbitrarily strong high-to-low radial dissipation dominance at those peaks.

These are POINTWISE time statements. A finite time-integral can accommodate
arbitrarily tall but narrow peaks; no persistence-width bound follows.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Choose a constant Fourier cutoff large enough to make its squared
coercivity coefficient exceed any requested real amplification M. -/
theorem h3Path_exists_fixedRadius_for_amplification244
    (M : ℝ) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ M ≤ ρ ^ 2 / 2 := by
  let ρ : ℝ := max (2 * M + 2) 1
  have hR : 1 ≤ ρ := le_max_right _ _
  have hLarge : 2 * M + 2 ≤ ρ := le_max_left _ _
  have hρSq : ρ ≤ ρ ^ 2 := by
    have hMul : 0 ≤ ρ * (ρ - 1) :=
      mul_nonneg (by linarith only [hR]) (by linarith only [hR])
    nlinarith only [hMul]
  refine ⟨ρ, (by linarith only [hR]), ?_⟩
  linarith only [hLarge, hρSq]

/-- The existing fixed-radius physical estimate actually allows an
arbitrarily large coefficient in front of the full SPECTRAL SUP norm square.
No new physical times or Fourier pointwise values are selected. -/
theorem h3Path_cofinalSpectralPeaks_eventualArbitraryDissipationGain244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (s : ℕ → ℝ)
    (hs : ∀ᶠ k : ℕ in atTop, s k ∈ Set.Ioo b T)
    (hEscape : Tendsto (fun k =>
      ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖) atTop atTop)
    (M : ℝ) :
    ∀ᶠ k : ℕ in atTop,
      M * ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ ^ 2 ≤
        velocityH3DissipationAt u (s k) := by
  obtain ⟨ρ, hρ, hM⟩ := h3Path_exists_fixedRadius_for_amplification244 M
  have hRadial := h3Path_cofinalSpectralPeaks_eventualRadiusDissipation244
    hH3 hClass b hb s hs hEscape ρ hρ
  filter_upwards [hRadial] with k hk
  have hProduct := mul_le_mul_of_nonneg_right hM
    (sq_nonneg ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖)
  exact hProduct.trans hk

/-- The physical H³ dissipation-to-weighted-spectral-square ratio tends to
+infinity at precisely the original spectral peaks. This is stronger than
D₃(s_k) -> +infinity and needs no dynamic Fourier cutoff selection. -/
theorem h3Path_cofinalSpectralPeaks_dissipationOverSquare_escape244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (s : ℕ → ℝ)
    (hs : ∀ᶠ k : ℕ in atTop, s k ∈ Set.Ioo b T)
    (hEscape : Tendsto (fun k =>
      ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖) atTop atTop) :
    Tendsto (fun k : ℕ =>
      velocityH3DissipationAt u (s k) /
        ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ ^ 2)
      atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro M
  have hAmpl := h3Path_cofinalSpectralPeaks_eventualArbitraryDissipationGain244
    hH3 hClass b hb s hs hEscape M
  have hNorm : ∀ᶠ k : ℕ in atTop,
      1 ≤ ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ :=
    hEscape.eventually (eventually_ge_atTop 1)
  filter_upwards [hAmpl, hNorm] with k hD hN
  have hPositive : 0 <
      ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ ^ 2 :=
    pow_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hN) 2
  exact (le_div_iff₀ hPositive).2 hD

/-- The same peak sequence has unbounded genuine physical H³ dissipation.
This conclusion follows from the stronger arbitrary-amplification estimate. -/
theorem h3Path_cofinalSpectralPeaks_fullDissipation_escape244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (s : ℕ → ℝ)
    (hs : ∀ᶠ k : ℕ in atTop, s k ∈ Set.Ioo b T)
    (hEscape : Tendsto (fun k =>
      ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖) atTop atTop) :
    Tendsto (fun k : ℕ => velocityH3DissipationAt u (s k))
      atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro M
  have hAmpl := h3Path_cofinalSpectralPeaks_eventualArbitraryDissipationGain244
    hH3 hClass b hb s hs hEscape 1
  have hLarge : ∀ᶠ k : ℕ in atTop,
      max M 1 ≤ ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ :=
    hEscape.eventually (eventually_ge_atTop (max M 1))
  filter_upwards [hAmpl, hLarge] with k hD hN
  have hOne : 1 ≤ ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ :=
    (le_max_right _ _).trans hN
  have hM : M ≤ ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ :=
    (le_max_left _ _).trans hN
  have hSq : ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ ≤
      ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ ^ 2 := by
    have hMul : 0 ≤
        ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ *
          (‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ - 1) :=
      mul_nonneg (norm_nonneg _) (by linarith only [hOne])
    nlinarith only [hMul]
  linarith only [hM, hSq, hD]

/-- A bounded physical kinetic anchor supplies a UNIFORM full physical
low-radial H³ dissipation ceiling on every later strict-time subtail. -/
theorem h3Path_physicalFixedRadialLowDissipation_kineticCeiling244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (t : ℝ) (ht : t ∈ Set.Ioo b T)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    h3PathActualLowRadialDissipation244 ρ
        (h3AuditActualSpectralVelocityTotal hH3 t) ≤
      ρ ^ 2 * (h3TerminalRadialSobolevWeightSquareCeiling ρ *
        velocityH3Energy0At u b) := by
  have htClass : t ∈ Set.Ioo a T := ⟨lt_trans hb.1 ht.1, ht.2⟩
  have hLow := h3Path_actualLowRadialDissipation_le_squareLowMass244
    hH3 hClass t htClass ρ hρ
  have hMass := h3Path_actualSpectralLowRadialSquareMass_le_kineticAnchor244
    hH3 hClass b hb ρ hρ t ht
  have hScaled := mul_le_mul_of_nonneg_left hMass (sq_nonneg ρ)
  exact hLow.trans hScaled

/-- At every fixed radial cutoff, the same original source-peak sequence
has arbitrarily large high-frequency dissipation relative to low-frequency
dissipation. No normalized quotient or unrelated witness sequence is used. -/
theorem h3Path_cofinalSpectralPeaks_eventualHighOverLowDissipation244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (s : ℕ → ℝ)
    (hs : ∀ᶠ k : ℕ in atTop, s k ∈ Set.Ioo b T)
    (hEscape : Tendsto (fun k =>
      ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖) atTop atTop)
    (ρ R : ℝ) (hρ : 0 ≤ ρ) (hR : 0 ≤ R) :
    ∀ᶠ k : ℕ in atTop,
      R * h3PathActualLowRadialDissipation244 ρ
        (h3AuditActualSpectralVelocityTotal hH3 (s k)) ≤
      h3PathActualHighRadialDissipation244 ρ
        (h3AuditActualSpectralVelocityTotal hH3 (s k)) := by
  let C : ℝ := ρ ^ 2 *
    (h3TerminalRadialSobolevWeightSquareCeiling ρ * velocityH3Energy0At u b)
  let B : ℝ := max C 0
  have hD := h3Path_cofinalSpectralPeaks_fullDissipation_escape244
    hH3 hClass b hb s hs hEscape
  have hLate : ∀ᶠ k : ℕ in atTop,
      (R + 1) * B ≤ velocityH3DissipationAt u (s k) :=
    hD.eventually (eventually_ge_atTop ((R + 1) * B))
  filter_upwards [hs, hLate] with k ht hBig
  let G : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 (s k)
  have hLow : h3PathActualLowRadialDissipation244 ρ G ≤ B := by
    have hBase := h3Path_physicalFixedRadialLowDissipation_kineticCeiling244
      hH3 hClass b hb (s k) ht ρ hρ
    exact hBase.trans (le_max_left _ _)
  have hScaled := mul_le_mul_of_nonneg_left hLow hR
  have hPartition := h3Path_actualRadialDissipation_partition244
    hH3 hClass (s k) ⟨lt_trans hb.1 ht.1, ht.2⟩ ρ
  dsimp only [G] at hLow hScaled hPartition ⊢
  linarith only [hBig, hLow, hScaled, hPartition]

/-- The ACTUAL canonical projected-source maximizers enjoy the divergence
of full H³ dissipation divided by their squared spectral amplitude, in the
original explicit conditional critical-width regime. No maximizer or
annulus witness is replaced. -/
theorem h3Path_noL2Trace_canonicalWidth_sourcePeakDissipationRatio244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hTerminalMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ)
        (v : ℕ → ℕ) (s : ℕ → ℝ),
      StrictMono v ∧
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ n, τ n ∈ Set.Ioo a T) ∧
      (∀ k l, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      Summable (fun k => δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ∧
      (∀ k, v k ≤ N (v k) ∧
        C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
          (τ (v k)) (τ (v k) + (T - τ (v k)) / 2)) ∧
      (∀ k, s k ∈ Set.Icc (τ (v k))
          (τ (v k) + (T - τ (v k)) / 2) ∧
        ‖h3PathActualProjectedMomentumSource244 hH3 (s k)‖ = C (v k)) ∧
      (∀ η B D : ℝ, 0 < η → 0 ≤ B → 0 ≤ D →
        (∀ᶠ k : ℕ in atTop,
          η ≤ ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2) ∧
          h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1 ≤
            B * (((v k : ℝ) + 1) ^ 6) ∧
          (((N (v k) - v k : ℕ) : ℝ) + 1) ^ 8 ≤
            D * (((v k : ℝ) + 1) ^ 9)) →
        Tendsto (fun k : ℕ =>
          velocityH3DissipationAt u (s k) /
            ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ ^ 2)
          atTop atTop) := by
  obtain ⟨τ, N, K, C, δ, v, s, hv, hCofinal, hTime,
      hSeparate, hSummable, hCanonical, hPeak, hJoint⟩ :=
    h3Path_noL2Trace_finiteDissipation_canonicalWidth_fixedMaximizerJointEscape244
      hH3 hClass hTerminalMass hNoTrace hDInt
  refine ⟨τ, N, K, C, δ, v, s, hv, hCofinal, hTime,
    hSeparate, hSummable, hCanonical, hPeak, ?_⟩
  have haT : a < T := lt_trans (hTime 0).1 (hTime 0).2
  let b : ℝ := (a + T) / 2
  have hb : b ∈ Set.Ioo a T := by
    dsimp only [b]
    constructor <;> linarith only [haT]
  have hLate : ∀ᶠ k : ℕ in atTop, b < τ (v k) :=
    hCofinal.eventually (Ioi_mem_nhds hb.2)
  have hsEventually : ∀ᶠ k : ℕ in atTop, s k ∈ Set.Ioo b T := by
    filter_upwards [hLate] with k hk
    have hMid : τ (v k) + (T - τ (v k)) / 2 < T := by
      have ht := (hTime (v k)).2
      linarith only [ht]
    exact ⟨lt_of_lt_of_le hk (hPeak k).1.1,
      lt_of_le_of_lt (hPeak k).1.2 hMid⟩
  intro η B D hη hB hD hRegime
  have hEscape : Tendsto (fun k =>
      ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖) atTop atTop :=
    (hJoint η B D hη hB hD hRegime).2
  exact h3Path_cofinalSpectralPeaks_dissipationOverSquare_escape244
    hH3 hClass b hb s hsEventually hEscape

end
end PrimeTensor.FirstMonomialTriad
