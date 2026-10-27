import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEMinimalHighTailNinthEighth244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralKineticAnchoredLowDissipationBudget244
import Mathlib.Tactic

/-!
# Kinetic-energy comparison at the canonical first spectral crossing

The exact physical annular first crossing demands three-quarter cubic
H³ dissipation below the selected outer cutoff. The physical kinetic
energy anchor controls the low-radial H³ dissipation by the *eighth*
power of that cutoff. We derive a quantitative bandwidth/kinetic
necessary condition without claiming it excludes ninth/eighth separation.

Separately, divergence of high-frequency H³ dissipation compared with
uniformly bounded physical L² kinetic energy forces divergence of their
ratio. High H³ concentration need not produce large kinetic L² mass.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Every strict physical three-quarter-cubic annular crossing demands
kinetic energy times an explicit eighth-power outer-frequency budget.
The kinetic anchor precedes the snapshot; no H³ uniform bound is used. -/
theorem h3Path_minimalAnnulus_kineticEighthBandwidthCost244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (t : ℝ) (ht : t ∈ Set.Ioo b T)
    (n N : ℕ)
    (hCross : 3 * (((n : ℝ) + 1) ^ 3) / 4 <
      h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t) -
      h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t)) :
    3 * (((n : ℝ) + 1) ^ 3) <
      16 * (((N : ℝ) + 2) ^ 8) * velocityH3Energy0At u b := by
  let R : ℝ := (n : ℝ) + 1
  let Q : ℝ := (N : ℝ) + 1
  let E : ℝ := velocityH3Energy0At u b
  let G : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hE : 0 ≤ E := velocityH3Energy0At_nonneg u b
  have hLowR : 0 ≤ h3PathActualLowRadialDissipation244 R G := by
    unfold h3PathActualLowRadialDissipation244
    apply integral_nonneg
    intro ξ
    exact h3TerminalSpectralDissipationSingleDensity_nonneg G ξ
  have hBudget : h3PathActualLowRadialDissipation244 Q G ≤
      Q ^ 2 * (h3TerminalRadialSobolevWeightSquareCeiling Q * E) := by
    exact h3Path_actualLowRadialDissipation_le_kineticAnchor244
      hH3 hClass b hb Q hQ t ht
  have hQ2 : Q ^ 2 ≤ (Q + 1) ^ 2 := by
    nlinarith only [hQ]
  have hWeight : h3TerminalRadialSobolevWeightSquareCeiling Q ≤
      4 * (Q + 1) ^ 6 :=
    h3Path_radialSobolevCeiling_le_fourShiftSixth244 Q hQ
  have hProduct : Q ^ 2 * h3TerminalRadialSobolevWeightSquareCeiling Q ≤
      4 * (Q + 1) ^ 8 := by
    calc
      _ ≤ (Q + 1) ^ 2 * h3TerminalRadialSobolevWeightSquareCeiling Q :=
        mul_le_mul_of_nonneg_right hQ2
          (h3TerminalRadialSobolevWeightSquareCeiling_pos Q).le
      _ ≤ (Q + 1) ^ 2 * (4 * (Q + 1) ^ 6) :=
        mul_le_mul_of_nonneg_left hWeight (sq_nonneg _)
      _ = 4 * (Q + 1) ^ 8 := by ring
  have hScaled := mul_le_mul_of_nonneg_right hProduct hE
  have hBudget' : h3PathActualLowRadialDissipation244 Q G ≤
      4 * (Q + 1) ^ 8 * E := by
    calc
      _ ≤ Q ^ 2 * (h3TerminalRadialSobolevWeightSquareCeiling Q * E) := hBudget
      _ = (Q ^ 2 * h3TerminalRadialSobolevWeightSquareCeiling Q) * E := by ring
      _ ≤ (4 * (Q + 1) ^ 8) * E := hScaled
      _ = 4 * (Q + 1) ^ 8 * E := by ring
  have hCross' : 3 * R ^ 3 / 4 <
      h3PathActualLowRadialDissipation244 Q G -
        h3PathActualLowRadialDissipation244 R G := by
    simpa only [R, Q, G] using hCross
  have hCost : 3 * R ^ 3 / 4 < 4 * (Q + 1) ^ 8 * E := by
    linarith only [hCross', hLowR, hBudget']
  dsimp only [R, Q, E] at hCost ⊢
  nlinarith only [hCost]

/-- Any cofinal family of physical annular crossings inherits the
kinetic/eighth-power bandwidth requirement after every fixed anchor. -/
theorem h3Path_cofinalCrossings_kineticEighthBandwidthCost244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ) (N : ℕ → ℕ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hLimit : Tendsto τ atTop (𝓝 T))
    (hCross : ∀ n : ℕ, 3 * (((n : ℝ) + 1) ^ 3) / 4 <
      h3PathActualLowRadialDissipation244 ((N n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 (τ n)) -
      h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 (τ n)))
    (b : ℝ) (hb : b ∈ Set.Ioo a T) :
    ∀ᶠ n : ℕ in atTop,
      3 * (((n : ℝ) + 1) ^ 3) <
        16 * (((N n : ℝ) + 2) ^ 8) * velocityH3Energy0At u b := by
  have hLate : ∀ᶠ n : ℕ in atTop, b < τ n :=
    hLimit.eventually (eventually_gt_nhds hb.2)
  filter_upwards [hLate] with n hbn
  exact h3Path_minimalAnnulus_kineticEighthBandwidthCost244
    hH3 hClass b hb (τ n) ⟨hbn, (hτ n).2⟩ n (N n) (hCross n)

/-- The canonical, physical no-terminal-trace first crossing satisfies
an anchored kinetic eighth-power bandwidth cost for *every* strict anchor.
The first-crossing minimality is preserved on the same selected radii. -/
theorem h3Path_noL2Trace_minimalFirstCrossing_kineticEighthBandwidth244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ),
      Tendsto τ atTop (𝓝 T) ∧
      (∀ n : ℕ, n ≤ N n ∧
        ∀ m : ℕ, n ≤ m → m < N n →
          h3PathActualLowRadialDissipation244 ((m : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (τ n)) -
            h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (τ n)) ≤
              3 * (((n : ℝ) + 1) ^ 3) / 4) ∧
      (∀ b : ℝ, b ∈ Set.Ioo a T → ∀ᶠ n : ℕ in atTop,
        3 * (((n : ℝ) + 1) ^ 3) <
          16 * (((N n : ℝ) + 2) ^ 8) * velocityH3Energy0At u b) := by
  obtain ⟨τ, N, K, C, δ, hτ, hLimit, hAll⟩ :=
    h3Path_noL2Trace_minimalQuadraticSharpClocks_retain_quarterHighTail244
      hH3 hClass hMass hNoTrace
  have hCross (n : ℕ) : 3 * (((n : ℝ) + 1) ^ 3) / 4 <
      h3PathActualLowRadialDissipation244 ((N n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 (τ n)) -
      h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 (τ n)) := by
    rcases hAll n with ⟨_, _, _, _, _, _, _, hg, _, _⟩
    dsimp only [h3PathCubicAnnulusActualGap244] at hg
    linarith only [hg]
  refine ⟨τ, N, hLimit, ?_, ?_⟩
  · intro n
    rcases hAll n with ⟨hn, _, _, _, _, _, _, _, hMinimal, _⟩
    exact ⟨hn, hMinimal⟩
  · intro b hb
    exact h3Path_cofinalCrossings_kineticEighthBandwidthCost244
      hH3 hClass τ N hτ hLimit hCross b hb

/-- A divergent high-order spectral tail cannot remain bounded after
normalization by a nonnegative, uniformly bounded kinetic-energy profile.
This is an energy-scale comparison, not an L² tail-mass lower bound. -/
theorem h3Path_divergentTail_boundedKinetic_normalizedEscape244
    (tail kinetic : ℕ → ℝ) (E : ℝ) (hE : 0 ≤ E)
    (hKinetic : ∀ᶠ k : ℕ in atTop,
      0 ≤ kinetic k ∧ kinetic k ≤ E)
    (hTail : Tendsto tail atTop atTop) :
    Tendsto (fun k : ℕ => tail k / (kinetic k + 1)) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro M
  let H : ℝ := max 0 M + 1
  have hH : 0 ≤ H := by dsimp only [H]; linarith [le_max_left (0 : ℝ) M]
  let A : ℝ := H * (E + 1)
  have hLarge : ∀ᶠ k : ℕ in atTop, A ≤ tail k :=
    hTail.eventually (eventually_ge_atTop A)
  filter_upwards [hLarge, hKinetic] with k hk hkin
  have hDen : 0 < kinetic k + 1 := by linarith only [hkin.1]
  have hDenLe : kinetic k + 1 ≤ E + 1 := by linarith only [hkin.2]
  have hUpper : H * (kinetic k + 1) ≤ A := by
    dsimp only [A]
    exact mul_le_mul_of_nonneg_left hDenLe hH
  have hM : M ≤ H := by
    dsimp only [H]
    have hm : M ≤ max 0 M := le_max_right _ _
    linarith only [hm]
  have hLower : M * (kinetic k + 1) ≤ H * (kinetic k + 1) :=
    mul_le_mul_of_nonneg_right hM hDen.le
  apply (le_div_iff₀ hDen).2
  linarith only [hLower, hUpper, hk]

/-- Physical version of the kinetic normalization: above any strict
physical anchor, divergent high-frequency H³ dissipation outgrows the
actual zeroth-order kinetic energy even though the latter is bounded.
No claim is made that the Fourier L² tail itself diverges. -/
theorem h3Path_physicalMovingHighTail_outpaces_kineticEnergy244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (τ ρ : ℕ → ℝ)
    (hLate : ∀ᶠ k : ℕ in atTop, τ k ∈ Set.Ioo b T)
    (hHigh : Tendsto (fun k : ℕ =>
      h3PathActualHighRadialDissipation244 (ρ k)
        (h3AuditActualSpectralVelocityTotal hH3 (τ k))) atTop atTop) :
    Tendsto (fun k : ℕ =>
      h3PathActualHighRadialDissipation244 (ρ k)
        (h3AuditActualSpectralVelocityTotal hH3 (τ k)) /
      (velocityH3Energy0At u (τ k) + 1)) atTop atTop := by
  have hKinetic : ∀ᶠ k : ℕ in atTop,
      0 ≤ velocityH3Energy0At u (τ k) ∧
        velocityH3Energy0At u (τ k) ≤ velocityH3Energy0At u b := by
    filter_upwards [hLate] with k hk
    have ht : τ k ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 (lt_trans hb.1 hk.1), hk.2⟩
    have hRaw := h3Path_actualRawFourierSquareMass_le_kineticAnchor244
      hH3 hClass b hb (τ k) hk
    rw [h3Path_actualRawFourierSquareMass_eq_kinetic244 hH3 (τ k) ht] at hRaw
    exact ⟨velocityH3Energy0At_nonneg u (τ k), hRaw⟩
  exact h3Path_divergentTail_boundedKinetic_normalizedEscape244
    _ _ (velocityH3Energy0At u b)
    (velocityH3Energy0At_nonneg u b) hKinetic hHigh


/-- On the *same* cofinal disjoint-window physical ninth/eighth witnesses,
divergent high-frequency H³ dissipation outpaces physical kinetic energy.
The strict-after-anchor condition is stated explicitly: the prior exported
witness theorem does not expose its individual strict-time memberships. -/
theorem h3Path_noL2Trace_finiteDissipation_subNinthEighth_relativeKinetic244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ)
        (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k : ℕ => τ (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      Summable (fun k : ℕ =>
        δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ∧
      (∀ b η B S M : ℝ, b ∈ Set.Ioo a T → 0 < η → 0 ≤ B → 0 ≤ M →
        ∀ m : ℕ → ℕ,
        (∀ᶠ k : ℕ in atTop, τ (v k) ∈ Set.Ioo b T) →
        (∀ᶠ k : ℕ in atTop,
          η ≤ ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2) ∧
          h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1 ≤
            B * ((v k : ℝ) + 1) ^ 6 ∧
          C (v k) ^ 2 ≤ S ^ 2 ∧
          v k ≤ m k ∧
          ((m k : ℝ) + 2) ^ 8 ≤ M * ((v k : ℝ) + 1) ^ 9) →
        Tendsto (fun k : ℕ =>
          h3PathActualHighRadialDissipation244 ((m k : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) /
            (velocityH3Energy0At u (τ (v k)) + 1)) atTop atTop) := by
  obtain ⟨τ, N, K, C, δ, v, hv, hCofinal, hSeparate,
      hSummable, hHighDivergence⟩ :=
    h3Path_noL2Trace_finiteDissipation_subNinthEighthHighTailDivergence244
      hH3 hClass hMass hNoTrace hDInt
  refine ⟨τ, N, K, C, δ, v, hv, hCofinal, hSeparate, hSummable, ?_⟩
  intro b η B S M hb hη hB hM m hLate hRegime
  have hHigh := hHighDivergence η B S M hη hB hM m hRegime
  exact h3Path_physicalMovingHighTail_outpaces_kineticEnergy244
    hH3 hClass b hb (fun k => τ (v k))
    (fun k => ((m k : ℝ) + 1)) hLate hHigh

end
end PrimeTensor.FirstMonomialTriad
