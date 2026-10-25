import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralSignedCubicBarrier244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSignedChannelAlternative244
import Mathlib.Tactic

/-!
# A fixed terminal corridor for the physical signed H³ cubic

On the no-kinetic-trace branch, the preceding theorem isolates a fixed
cofinal physical channel: fast negative logarithmic H³ energy slope or
adverse FULL signed physical transport. In the adverse branch the exact
physical-to-canonical identity produces a three-way pointwise corridor:
large H³ energy, adverse canonical gradient, or adverse canonical first
monomial. The arm may vary with each individual snapshot.

The finite cofinal threshold selection theorem upgrades the latter
pointwise trichotomy to ONE fixed cofinal arm. A diagonalization then
chooses one terminal sequence with increasing thresholds for that arm.
All scalar spectral terms refer to the genuine physical weighted spectral
state. No lower-order absorption, gradient sign, or nonextension-to-trace
implication is silently assumed. This is still conditional on failure of
the strong kinetic L² terminal trace and a positive terminal kinetic mass.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Three monotone threshold channels with cofinal union have a fixed
cofinal member. This is two applications of the already-verified binary
cofinal selection lemma, not a selection of a channel at each time. -/
theorem h3Path_threeChannel_cofinal_threshold_selection244
    {a T : ℝ} (P Q R : ℝ → ℝ → Prop)
    (hP : ∀ t M N : ℝ, M ≤ N → P t N → P t M)
    (hQ : ∀ t M N : ℝ, M ≤ N → Q t N → Q t M)
    (hR : ∀ t M N : ℝ, M ≤ N → R t N → R t M)
    (hCover : ∀ b : ℝ, b ∈ Set.Ioo a T →
      ∀ B : ℝ, 0 ≤ B →
        ∃ t : ℝ, t ∈ Set.Ioo b T ∧ (P t B ∨ Q t B ∨ R t B)) :
    (∀ b : ℝ, b ∈ Set.Ioo a T → ∀ B : ℝ, 0 ≤ B →
      ∃ t : ℝ, t ∈ Set.Ioo b T ∧ P t B) ∨
    (∀ b : ℝ, b ∈ Set.Ioo a T → ∀ B : ℝ, 0 ≤ B →
      ∃ t : ℝ, t ∈ Set.Ioo b T ∧ Q t B) ∨
    (∀ b : ℝ, b ∈ Set.Ioo a T → ∀ B : ℝ, 0 ≤ B →
      ∃ t : ℝ, t ∈ Set.Ioo b T ∧ R t B) := by
  have hQR : ∀ t M N : ℝ, M ≤ N →
      (Q t N ∨ R t N) → (Q t M ∨ R t M) := by
    intro t M N hMN hAlt
    rcases hAlt with h | h
    · exact Or.inl (hQ t M N hMN h)
    · exact Or.inr (hR t M N hMN h)
  rcases h3_twoChannel_cofinal_threshold_selection244
      P (fun t B => Q t B ∨ R t B) hP hQR hCover with
    hFirst | hRest
  · exact Or.inl hFirst
  · rcases h3_twoChannel_cofinal_threshold_selection244
        Q R hQ hR hRest with hSecond | hThird
    · exact Or.inr (Or.inl hSecond)
    · exact Or.inr (Or.inr hThird)

/-- Cofinal adverse FULL physical transport has ONE cofinal canonical
constituent or high-energy corridor. High energy is stated in its
unsquared square-root form so every arm is monotone in the real threshold;
nonnegative-threshold squaring is performed only after selecting an arm. -/
theorem h3Path_cofinalAdverseTransport_fixedCanonicalCorridor244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hAdverse : ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ B : ℝ,
      ∃ t : ℝ, t ∈ Set.Ioo b T ∧
        B * velocityH3EnergyAt u t <
          -velocityH3TransportDerivativeAt u t) :
    (∀ b : ℝ, b ∈ Set.Ioo a T → ∀ B : ℝ, 0 ≤ B →
      ∃ t : ℝ, t ∈ Set.Ioo b T ∧
        B ≤ 48 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) ∨
    (∀ b : ℝ, b ∈ Set.Ioo a T → ∀ B : ℝ, 0 ≤ B →
      ∃ t : ℝ, t ∈ Set.Ioo b T ∧
        4 * weightedH3CanonicalGradientTransport244
          (h3PathWeightedSpectralState244 u T hH3 t) <
          -(B * velocityH3EnergyAt u t)) ∨
    (∀ b : ℝ, b ∈ Set.Ioo a T → ∀ B : ℝ, 0 ≤ B →
      ∃ t : ℝ, t ∈ Set.Ioo b T ∧
        4 * (3 * weightedH3CanonicalSignedFirstMonomial244
          (h3PathWeightedSpectralState244 u T hH3 t)) <
          -(B * velocityH3EnergyAt u t)) := by
  apply h3Path_threeChannel_cofinal_threshold_selection244
    (P := fun t B =>
      B ≤ 48 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t))
    (Q := fun t B =>
      4 * weightedH3CanonicalGradientTransport244
        (h3PathWeightedSpectralState244 u T hH3 t) <
          -(B * velocityH3EnergyAt u t))
    (R := fun t B =>
      4 * (3 * weightedH3CanonicalSignedFirstMonomial244
        (h3PathWeightedSpectralState244 u T hH3 t)) <
          -(B * velocityH3EnergyAt u t))
  · intro t M N hMN hN
    exact le_trans hMN hN
  · intro t M N hMN hN
    have hE : 0 ≤ velocityH3EnergyAt u t :=
      le_trans (by norm_num : (0 : ℝ) ≤ 1)
        (one_le_velocityH3EnergyAt u t)
    have hProduct : M * velocityH3EnergyAt u t ≤
        N * velocityH3EnergyAt u t :=
      mul_le_mul_of_nonneg_right hMN hE
    exact lt_of_lt_of_le hN (neg_le_neg hProduct)
  · intro t M N hMN hN
    have hE : 0 ≤ velocityH3EnergyAt u t :=
      le_trans (by norm_num : (0 : ℝ) ≤ 1)
        (one_le_velocityH3EnergyAt u t)
    have hProduct : M * velocityH3EnergyAt u t ≤
        N * velocityH3EnergyAt u t :=
      mul_le_mul_of_nonneg_right hMN hE
    exact lt_of_lt_of_le hN (neg_le_neg hProduct)
  · intro b hb B _hB
    obtain ⟨t, ht, hTransport⟩ := hAdverse b hb B
    have htClass : t ∈ Set.Ioo a T :=
      ⟨lt_trans hb.1 ht.1, ht.2⟩
    rcases h3Path_adverseFullTransport_highEnergy_or_negativeCanonicalChannel244
        hH3 hClass htClass B hTransport with hHigh | hGradient | hInterpolation
    · exact ⟨t, ht, Or.inl hHigh⟩
    · exact ⟨t, ht, Or.inr (Or.inl hGradient)⟩
    · exact ⟨t, ht, Or.inr (Or.inr hInterpolation)⟩

/-- Diagonal selection for an abstract physical terminal predicate. This
retains the same terminal closeness and convergence estimates as the
previous scalar-rate diagonalization, without introducing any continuity
assumption on the selected spectral channel. -/
theorem h3Path_cofinalThreshold_diagonalPredicate244
    {a T : ℝ} (ha : a < T)
    (P : ℝ → ℝ → Prop)
    (hCofinal : ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ B : ℝ, 0 ≤ B →
      ∃ t : ℝ, t ∈ Set.Ioo b T ∧ P t B) :
    ∃ τ : ℕ → ℝ,
      (∀ n : ℕ, τ n ∈ Set.Ioo a T) ∧
      (∀ n : ℕ, dist (τ n) T < (1 : ℝ) / ((n : ℝ) + 1)) ∧
      Tendsto τ atTop (𝓝 T) ∧
      (∀ n : ℕ, P (τ n) ((n : ℝ) + 1)) := by
  have hChoice (n : ℕ) :
      ∃ t : ℝ, t ∈ Set.Ioo a T ∧
        dist t T < (1 : ℝ) / ((n : ℝ) + 1) ∧
        P t ((n : ℝ) + 1) := by
    let ε : ℝ := (1 : ℝ) / ((n : ℝ) + 1)
    let c : ℝ := max ((a + T) / 2) (T - ε)
    have hε : 0 < ε := by
      dsimp only [ε]
      positivity
    have hMidLower : a < (a + T) / 2 := by
      linarith only [ha]
    have hMidUpper : (a + T) / 2 < T := by
      linarith only [ha]
    have hc : c ∈ Set.Ioo a T := by
      dsimp only [c]
      exact ⟨lt_of_lt_of_le hMidLower (le_max_left _ _),
        (max_lt_iff).2 ⟨hMidUpper, by linarith only [hε]⟩⟩
    obtain ⟨t, ht, hLarge⟩ := hCofinal c hc ((n : ℝ) + 1) (by positivity)
    have htClass : t ∈ Set.Ioo a T :=
      ⟨lt_trans hc.1 ht.1, ht.2⟩
    have hNear : T - ε < t :=
      lt_of_le_of_lt (le_max_right _ _) ht.1
    have hDist : dist t T < (1 : ℝ) / ((n : ℝ) + 1) := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ht.2.le)]
      dsimp only [ε] at hNear
      linarith only [hNear]
    exact ⟨t, htClass, hDist, hLarge⟩
  choose τ hτ using hChoice
  have hInv :
      Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hNormBound : ∀ n : ℕ,
      ‖τ n - T‖ ≤ (1 : ℝ) / ((n : ℝ) + 1) := by
    intro n
    simpa only [Real.norm_eq_abs, Real.dist_eq] using
      (le_of_lt (hτ n).2.1)
  have hTendsto : Tendsto τ atTop (𝓝 T) :=
    (tendsto_iff_norm_sub_tendsto_zero).2
      (squeeze_zero'
        (Filter.Eventually.of_forall (fun n => norm_nonneg (τ n - T)))
        (Filter.Eventually.of_forall hNormBound)
        hInv)
  exact ⟨τ, (fun n => (hτ n).1), (fun n => (hτ n).2.1),
    hTendsto, (fun n => (hτ n).2.2)⟩

/-- Either the fast physical H³ logarithmic decay is cofinal, or ONE
fixed full-third alternative is cofinal: the quadratic physical energy
corridor, a negative canonical gradient, or a negative canonical signed
interpolation. The choice is made BEFORE the subtail and the threshold. -/
theorem h3Path_physicalNoL2Trace_fixedFourChannelCofinality244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    (∀ b : ℝ, b ∈ Set.Ioo a T → ∀ B : ℝ, 0 ≤ B →
      ∃ t : ℝ, t ∈ Set.Ioo b T ∧
        B * velocityH3EnergyAt u t <
          -deriv (velocityH3EnergyAt u) t) ∨
    (∀ b : ℝ, b ∈ Set.Ioo a T → ∀ B : ℝ, 0 ≤ B →
      ∃ t : ℝ, t ∈ Set.Ioo b T ∧
        B ≤ 48 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) ∨
    (∀ b : ℝ, b ∈ Set.Ioo a T → ∀ B : ℝ, 0 ≤ B →
      ∃ t : ℝ, t ∈ Set.Ioo b T ∧
        4 * weightedH3CanonicalGradientTransport244
          (h3PathWeightedSpectralState244 u T hH3 t) <
          -(B * velocityH3EnergyAt u t)) ∨
    (∀ b : ℝ, b ∈ Set.Ioo a T → ∀ B : ℝ, 0 ≤ B →
      ∃ t : ℝ, t ∈ Set.Ioo b T ∧
        4 * (3 * weightedH3CanonicalSignedFirstMonomial244
          (h3PathWeightedSpectralState244 u T hH3 t)) <
          -(B * velocityH3EnergyAt u t)) := by
  rcases h3Path_physicalNoL2Trace_forces_fixedCofinalSignedChannel244
      hH3 hClass hL hNoTrace with hFast | hAdverse
  · left
    intro b hb B _hB
    obtain ⟨t, ht, hNegative⟩ := hFast b hb B
    exact ⟨t, ht, by linarith only [hNegative]⟩
  · right
    exact h3Path_cofinalAdverseTransport_fixedCanonicalCorridor244
      hH3 hClass hAdverse

/-- The four-channel obstruction can be witnessed along ONE terminal
sequence in ONE fixed channel. In the high-energy arm the correct physical
quadratic lower bound is obtained by squaring only nonnegative thresholds.
These are not asserted to be the moving-radial dissipation snapshots. -/
theorem h3Path_physicalNoL2Trace_fixedSignedCubicCorridorSequence244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    (∃ τ : ℕ → ℝ,
      (∀ n : ℕ, τ n ∈ Set.Ioo a T) ∧
      (∀ n : ℕ, dist (τ n) T < (1 : ℝ) / ((n : ℝ) + 1)) ∧
      Tendsto τ atTop (𝓝 T) ∧
      (∀ n : ℕ, ((n : ℝ) + 1) * velocityH3EnergyAt u (τ n) <
        -deriv (velocityH3EnergyAt u) (τ n))) ∨
    (∃ τ : ℕ → ℝ,
      (∀ n : ℕ, τ n ∈ Set.Ioo a T) ∧
      (∀ n : ℕ, dist (τ n) T < (1 : ℝ) / ((n : ℝ) + 1)) ∧
      Tendsto τ atTop (𝓝 T) ∧
      (∀ n : ℕ, ((n : ℝ) + 1) ^ 2 ≤
        (48 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 2 *
          velocityH3EnergyAt u (τ n))) ∨
    (∃ τ : ℕ → ℝ,
      (∀ n : ℕ, τ n ∈ Set.Ioo a T) ∧
      (∀ n : ℕ, dist (τ n) T < (1 : ℝ) / ((n : ℝ) + 1)) ∧
      Tendsto τ atTop (𝓝 T) ∧
      (∀ n : ℕ, 4 * weightedH3CanonicalGradientTransport244
        (h3PathWeightedSpectralState244 u T hH3 (τ n)) <
        -(((n : ℝ) + 1) * velocityH3EnergyAt u (τ n)))) ∨
    (∃ τ : ℕ → ℝ,
      (∀ n : ℕ, τ n ∈ Set.Ioo a T) ∧
      (∀ n : ℕ, dist (τ n) T < (1 : ℝ) / ((n : ℝ) + 1)) ∧
      Tendsto τ atTop (𝓝 T) ∧
      (∀ n : ℕ, 4 * (3 * weightedH3CanonicalSignedFirstMonomial244
        (h3PathWeightedSpectralState244 u T hH3 (τ n))) <
        -(((n : ℝ) + 1) * velocityH3EnergyAt u (τ n)))) := by
  rcases h3Path_physicalNoL2Trace_fixedFourChannelCofinality244
      hH3 hClass hL hNoTrace with hFast | hHigh | hGradient | hInterp
  · obtain ⟨τ, hτ, hNear, hLimit, hRate⟩ :=
      h3Path_cofinalThreshold_diagonalPredicate244
        hClass.terminal_start.2
        (fun t B => B * velocityH3EnergyAt u t <
          -deriv (velocityH3EnergyAt u) t) hFast
    exact Or.inl ⟨τ, hτ, hNear, hLimit, hRate⟩
  · obtain ⟨τ, hτ, hNear, hLimit, hRate⟩ :=
      h3Path_cofinalThreshold_diagonalPredicate244
        hClass.terminal_start.2
        (fun t B => B ≤ 48 *
          h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) hHigh
    refine Or.inr (Or.inl ⟨τ, hτ, hNear, hLimit, ?_⟩)
    intro n
    exact h3Path_highAllowance_forces_quadraticPhysicalEnergy244
      (τ n) ((n : ℝ) + 1) (by positivity) (hRate n)
  · obtain ⟨τ, hτ, hNear, hLimit, hRate⟩ :=
      h3Path_cofinalThreshold_diagonalPredicate244
        hClass.terminal_start.2
        (fun t B => 4 * weightedH3CanonicalGradientTransport244
          (h3PathWeightedSpectralState244 u T hH3 t) <
          -(B * velocityH3EnergyAt u t)) hGradient
    exact Or.inr (Or.inr (Or.inl ⟨τ, hτ, hNear, hLimit, hRate⟩))
  · obtain ⟨τ, hτ, hNear, hLimit, hRate⟩ :=
      h3Path_cofinalThreshold_diagonalPredicate244
        hClass.terminal_start.2
        (fun t B => 4 * (3 * weightedH3CanonicalSignedFirstMonomial244
          (h3PathWeightedSpectralState244 u T hH3 t)) <
          -(B * velocityH3EnergyAt u t)) hInterp
    exact Or.inr (Or.inr (Or.inr ⟨τ, hτ, hNear, hLimit, hRate⟩))

end
end PrimeTensor.FirstMonomialTriad
