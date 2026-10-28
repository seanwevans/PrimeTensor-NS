import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorCofinal244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalCriticalWidthPhysicalSource244
import Mathlib.Tactic

/-!
# Exact H³ anchor energy forced by minimal annulus crossing and critical width

At an actual weighted spectral state G, the finite-radius H4 gradient
quadratic is bounded by 3 (Q+1)^2 ‖G‖².  An annulus exceeding 3 R³ / 4
therefore forces R³ < 4 (Q+1)^2 E₃(t).  An eighth-power outer cutoff
bound (Q+1)^8 ≤ D R^9 turns this into the root-free energy constraint

    R³ < 256 D E₃(t)^4.

At the unmodified exact-anchor canonical disjoint windows, a cap on the
annular width yields D = 256 (V+1), hence

    R_k³ < 65536 (V+1) E₃(τ(v k))^4.

No source/rate cap or geometric noncompression is used. The critical width
cap is a *conditional* premise, not a consequence of finite dissipation.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Actual finite-radius H³ gradient dissipation is bounded by the square
of the weighted H³ spectral sup norm with its literal three-coordinate
multiplicity. The estimate is pointwise in physical time and frequency. -/
theorem h3Path_actualLowRadialDissipation_le_threeSpectralSup244
    (Q : ℝ) (hQ : 0 ≤ Q) (G : H3SpectralVelocityState) :
    h3PathActualLowRadialDissipation244 Q G ≤
      3 * (Q + 1) ^ 2 * ‖G‖ ^ 2 := by
  have hQOne : 0 ≤ Q + 1 := by linarith only [hQ]
  have hEach (j : Fin 3) :
      ‖h3PathLowRadialGradientMultiplierCLM244 Q hQ (G j)‖ ^ 2 ≤
        (Q + 1) ^ 2 * ‖G‖ ^ 2 := by
    have hComponent : ‖G j‖ ≤ ‖G‖ :=
      (pi_norm_le_iff_of_nonneg (norm_nonneg G)).1 le_rfl j
    have hMultiplier :
        ‖h3PathLowRadialGradientMultiplierCLM244 Q hQ (G j)‖ ≤
          (Q + 1) * ‖G j‖ :=
      h3Path_lowRadialGradientMultiplierApply_norm_le244 Q hQ (G j)
    have hUpper :
        ‖h3PathLowRadialGradientMultiplierCLM244 Q hQ (G j)‖ ≤
          (Q + 1) * ‖G‖ :=
      hMultiplier.trans (mul_le_mul_of_nonneg_left hComponent hQOne)
    have hUpperNonneg : 0 ≤ (Q + 1) * ‖G‖ :=
      mul_nonneg hQOne (norm_nonneg G)
    have hSquared :=
      (sq_le_sq₀ (norm_nonneg _) hUpperNonneg).2 hUpper
    nlinarith only [hSquared]
  rw [h3Path_actualLowRadialDissipation_eq_multiplierNormSquares244 Q hQ G]
  simp only [Fin.sum_univ_three]
  have h0 := hEach (0 : Fin 3)
  have h1 := hEach (1 : Fin 3)
  have h2 := hEach (2 : Fin 3)
  linarith only [h0, h1, h2]

/-- A three-quarter-cubic first crossing and a critical outer-frequency cap
force fourth-power H³ energy at the same physical anchor. The constant 256
comes from fourth-power cancellation, with no source coefficient involved. -/
theorem h3Path_scalarCriticalOuter_cubicCrossing_forces_energyFourth244
    (R Q K E D Lr Lq : ℝ)
    (hR : 1 ≤ R) (hRQ : R ≤ Q)
    (hKE : K ^ 2 ≤ E)
    (hLr : 0 ≤ Lr)
    (hCross : 3 * R ^ 3 / 4 < Lq - Lr)
    (hLq : Lq ≤ 3 * (Q + 1) ^ 2 * K ^ 2)
    (hWidth : (Q + 1) ^ 8 ≤ D * R ^ 9) :
    R ^ 3 < 256 * D * E ^ 4 := by
  have hE : 0 ≤ E := (sq_nonneg K).trans hKE
  have hQPos : 0 ≤ Q + 1 := by linarith only [hR, hRQ]
  have hScale :
      3 * (Q + 1) ^ 2 * K ^ 2 ≤ 3 * (Q + 1) ^ 2 * E :=
    mul_le_mul_of_nonneg_left hKE (by positivity)
  have hBase : R ^ 3 < 4 * (Q + 1) ^ 2 * E := by
    linarith only [hCross, hLr, hLq, hScale]
  have hRPos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hR
  have hBaseNonneg : 0 ≤ R ^ 3 := (pow_pos hRPos _).le
  have hFourth := pow_lt_pow_left₀ hBase hBaseNonneg (by norm_num : 4 ≠ 0)
  have hWidthScaled :=
    mul_le_mul_of_nonneg_left hWidth (by positivity : 0 ≤ 256 * E ^ 4)
  have hCombined : R ^ 3 * R ^ 9 <
      (256 * D * E ^ 4) * R ^ 9 := by
    calc
      R ^ 3 * R ^ 9 = (R ^ 3) ^ 4 := by ring
      _ < (4 * (Q + 1) ^ 2 * E) ^ 4 := hFourth
      _ = (256 * E ^ 4) * (Q + 1) ^ 8 := by ring
      _ ≤ (256 * E ^ 4) * (D * R ^ 9) := hWidthScaled
      _ = (256 * D * E ^ 4) * R ^ 9 := by ring
  by_contra hNot
  have hReverse : 256 * D * E ^ 4 ≤ R ^ 3 := le_of_not_gt hNot
  have hMult := mul_le_mul_of_nonneg_right hReverse (pow_pos hRPos 9).le
  exact (not_lt_of_ge hMult) hCombined

/-- Strict physical first-crossing at t forces physical fourth-energy
amplification whenever its actual outer cutoff obeys the critical cap. -/
theorem h3Path_exactAnchorCriticalOuter_forces_physicalEnergyFourth244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (R Q D : ℝ) (hR : 1 ≤ R) (hRQ : R ≤ Q)
    (hCross : 3 * R ^ 3 / 4 <
      h3PathActualLowRadialDissipation244 Q
        (h3AuditActualSpectralVelocityTotal hH3 t) -
      h3PathActualLowRadialDissipation244 R
        (h3AuditActualSpectralVelocityTotal hH3 t))
    (hWidth : (Q + 1) ^ 8 ≤ D * R ^ 9) :
    R ^ 3 < 256 * D * (velocityH3EnergyAt u t) ^ 4 := by
  let G : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  have hR0 : 0 ≤ R := le_trans (by norm_num : (0 : ℝ) ≤ 1) hR
  have hQ0 : 0 ≤ Q := le_trans hR0 hRQ
  have hLr : 0 ≤ h3PathActualLowRadialDissipation244 R G := by
    rw [h3Path_actualLowRadialDissipation_eq_multiplierNormSquares244 R hR0 G]
    positivity
  have hLq := h3Path_actualLowRadialDissipation_le_threeSpectralSup244
    Q hQ0 G
  have hKE : ‖G‖ ^ 2 ≤ velocityH3EnergyAt u t :=
    h3Path_actualSpectralAnchor_sq_le_physicalEnergy244 hH3 t ht
  exact h3Path_scalarCriticalOuter_cubicCrossing_forces_energyFourth244
    R Q ‖G‖ (velocityH3EnergyAt u t) D
    (h3PathActualLowRadialDissipation244 R G)
    (h3PathActualLowRadialDissipation244 Q G)
    hR hRQ hKE hLr (by simpa only [G] using hCross) hLq hWidth

/-- At any preselected cofinal minimal first crossing, an eventual canonical
ninth/eighth annulus-width cap forces actual anchor physical H³ energy to
obey a quantitative fourth-power lower bound. -/
theorem h3Path_exactAnchorCanonicalWidth_forces_eventualEnergyFourth244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ) (N : ℕ → ℕ) (v : ℕ → ℕ)
    (hTime : ∀ n, τ n ∈ Set.Ioo a T)
    (hN : ∀ k, v k ≤ N (v k))
    (hGap : ∀ k, ((v k : ℝ) + 1) ^ 3 / 4 <
      h3PathCubicAnnulusActualGap244 hH3 τ N (v k))
    (V : ℝ) (hV : 0 ≤ V)
    (hWidth : ∀ᶠ k : ℕ in atTop,
      (((N (v k) - v k : ℕ) : ℝ) + 1) ^ 8 ≤
        V * (((v k : ℝ) + 1) ^ 9)) :
    ∀ᶠ k : ℕ in atTop,
      ((v k : ℝ) + 1) ^ 3 <
        65536 * (V + 1) * (velocityH3EnergyAt u (τ (v k))) ^ 4 := by
  filter_upwards [hWidth] with k hk
  let R : ℝ := (v k : ℝ) + 1
  let Q : ℝ := (N (v k) : ℝ) + 1
  let L : ℝ := ((N (v k) - v k : ℕ) : ℝ)
  have hR : 1 ≤ R := by
    dsimp only [R]
    have hNat : (0 : ℝ) ≤ (v k : ℝ) := Nat.cast_nonneg _
    linarith only [hNat]
  have hL : 0 ≤ L := by dsimp only [L]; exact Nat.cast_nonneg _
  have hRQ : R ≤ Q := by
    have hCast : (v k : ℝ) ≤ (N (v k) : ℝ) := by
      exact_mod_cast hN k
    dsimp only [R, Q]
    linarith only [hCast]
  have hOuterEq : R + L + 1 = Q + 1 := by
    dsimp only [R, L, Q]
    rw [Nat.cast_sub (hN k)]
    ring
  have hWidth' : (L + 1) ^ 8 ≤ V * R ^ 9 := by
    simpa only [L, R] using hk
  have hOuter := h3Path_criticalWidthCap_boundsOuter244 R L V hR hL hV hWidth'
  rw [hOuterEq] at hOuter
  have hCross : 3 * R ^ 3 / 4 <
      h3PathActualLowRadialDissipation244 Q
        (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) -
      h3PathActualLowRadialDissipation244 R
        (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) := by
    have hg := hGap k
    dsimp only [h3PathCubicAnnulusActualGap244] at hg
    dsimp only [R, Q]
    linarith only [hg]
  have ht : τ (v k) ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 (hTime (v k)).1,
      (hTime (v k)).2⟩
  have hFourth := h3Path_exactAnchorCriticalOuter_forces_physicalEnergyFourth244
    hH3 (τ (v k)) ht R Q (256 * (V + 1)) hR hRQ hCross hOuter
  have hRearranged : R ^ 3 <
      65536 * (V + 1) * (velocityH3EnergyAt u (τ (v k))) ^ 4 := by
    convert hFourth using 1 <;> ring
  simpa only [R] using hRearranged

/-- The new exact-anchor cofinal witnesses retain the original disjoint
persistence, source attainment and spectral identity. With only a conditional
critical-width cap, their physical H³ energy must exceed the fourth-power
radial cost eventually. No geometric or linear-rate cap is added. -/
theorem h3Path_noL2Trace_exactAnchorCanonicalWidth_energyFourth244
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
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ n, τ n ∈ Set.Ioo a T) ∧
      (∀ k l, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      Summable (fun k => δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ∧
      (∀ k,
        K (v k) = ‖h3AuditActualSpectralVelocityTotal hH3 (τ (v k))‖ ∧
        K (v k) ^ 2 ≤ velocityH3EnergyAt u (τ (v k)) ∧
        v k ≤ N (v k) ∧
        ((v k : ℝ) + 1) ^ 3 / 4 <
          h3PathCubicAnnulusActualGap244 hH3 τ N (v k) ∧
        C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
          (τ (v k)) (τ (v k) + (T - τ (v k)) / 2) ∧
        (∃ s : ℝ, s ∈ Set.Icc (τ (v k))
            (τ (v k) + (T - τ (v k)) / 2) ∧
          ‖h3PathActualProjectedMomentumSource244 hH3 s‖ = C (v k))) ∧
      (∀ V : ℝ, 0 ≤ V →
        (∀ᶠ k : ℕ in atTop,
          (((N (v k) - v k : ℕ) : ℝ) + 1) ^ 8 ≤
            V * (((v k : ℝ) + 1) ^ 9)) →
        ∀ᶠ k : ℕ in atTop,
          ((v k : ℝ) + 1) ^ 3 <
            65536 * (V + 1) *
              (velocityH3EnergyAt u (τ (v k))) ^ 4) := by
  obtain ⟨τ, N, K, C, δ, v, hv, hCofinal, hTime,
      hSeparate, hSummable, hAll, _hBarrier, _hPeaks⟩ :=
    h3Path_noL2Trace_finiteDissipation_exactAnchorCanonicalThreeScale244
      hH3 hClass hMass hNoTrace hDInt
  have hN (k : ℕ) : v k ≤ N (v k) := by
    rcases hAll k with ⟨_, _, _, hn, _, _, _, _, _, _, _, _⟩
    exact hn
  have hGap (k : ℕ) : ((v k : ℝ) + 1) ^ 3 / 4 <
      h3PathCubicAnnulusActualGap244 hH3 τ N (v k) := by
    rcases hAll k with ⟨_, _, _, _, _, _, _, _, _, _, hg, _⟩
    exact hg
  refine ⟨τ, N, K, C, δ, v, hv, hCofinal, hTime,
    hSeparate, hSummable, ?_, ?_⟩
  · intro k
    rcases hAll k with ⟨hK, hKE, _, hn, hc, hp, _, _, _, _, hg, _⟩
    exact ⟨hK, hKE, hn, hg, hc, hp⟩
  · intro V hV hWidth
    exact h3Path_exactAnchorCanonicalWidth_forces_eventualEnergyFourth244
      hH3 hClass τ N v hTime hN hGap V hV hWidth

end
end PrimeTensor.FirstMonomialTriad
