import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalPeakForcedHalfAmplitude244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Balance.Exact
import Mathlib.Tactic

/-!
# Canonical source peaks: rapid amplitude loss entails actual signed H³ energy drainage

The fixed, dissipation-budget-determined clock of the preceding module forces
terminal compression or a drop of the actual spectral SUP norm below one half.
There are exactly three weighted Fourier components. Consequently the full
H³ square-energy decreases by at least a quarter of the original peak SUP
norm square during such a drop: the terminal state has at most three quarters
of the original peak square, whereas the original state has at least the
full peak square.

The mean-value theorem and the already-proved exact physical H³ balance
E' + 2D = -Transport then give an intermediate physical time at which

  (r-s) * (2 D(q) + Transport(q)) > ‖U₃(s)‖² / 4.

This is a *signed energy-drain rate* necessary for the rapid-loss branch.
Neither positivity of transport nor a lower persistence width is inferred.
No physical source maxima are moved or selected beyond the previous clocks.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Three spectral components give an exact factor-three comparison between
Hilbert-square energy and the finite-product SUP norm square. -/
theorem h3Path_spectralSquareEnergy_le_threeSupSquare244
    (G : H3SpectralVelocityState) :
    h3SpectralVelocitySquareEnergy G ≤ 3 * ‖G‖ ^ 2 := by
  have h0 := h3SpectralVelocity_coordinate_norm_le G 0
  have h1 := h3SpectralVelocity_coordinate_norm_le G 1
  have h2 := h3SpectralVelocity_coordinate_norm_le G 2
  have hSq0 := pow_le_pow_left₀ (norm_nonneg (G 0)) h0 2
  have hSq1 := pow_le_pow_left₀ (norm_nonneg (G 1)) h1 2
  have hSq2 := pow_le_pow_left₀ (norm_nonneg (G 2)) h2 2
  unfold h3SpectralVelocitySquareEnergy
  simp only [Fin.sum_univ_three]
  linarith only [hSq0, hSq1, hSq2]

/-- A drop below one half of the spectral SUP norm decreases the exact
sum-of-three-squares H³ energy by MORE than one quarter of the old SUP
square. This uses both sides of finite-product norm comparison. -/
theorem h3Path_spectralHalfLoss_forces_squareEnergyDrop244
    (G H : H3SpectralVelocityState)
    (hHalf : ‖H‖ < ‖G‖ / 2) :
    h3SpectralVelocitySquareEnergy H + ‖G‖ ^ 2 / 4 <
      h3SpectralVelocitySquareEnergy G := by
  have hPeak := h3Path_spectralSupNorm_sq_le_squareEnergy244 G
  have hLater := h3Path_spectralSquareEnergy_le_threeSupSquare244 H
  have h2 : 2 * ‖H‖ < ‖G‖ := by linarith only [hHalf]
  have hSq : (2 * ‖H‖) ^ 2 < ‖G‖ ^ 2 :=
    (sq_lt_sq₀ (by positivity : 0 ≤ 2 * ‖H‖) (norm_nonneg G)).2 h2
  nlinarith only [hPeak, hLater, hSq]

/-- A half-amplitude loss of the ACTUAL H³ spectral state forces a genuine
signed physical energy-drain rate at some strict intermediate time. The
exact NS identity gives the true 2D + Transport density, not a formal
spectral temporal derivative or an assumed transport sign. -/
theorem h3Path_physicalHalfLoss_forces_signedDrainSecant244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (s r : ℝ) (hs : s ∈ Set.Ioo a T) (hr : r ∈ Set.Ioo a T)
    (hsr : s < r)
    (hHalf : ‖h3AuditActualSpectralVelocityTotal hH3 r‖ <
      ‖h3AuditActualSpectralVelocityTotal hH3 s‖ / 2) :
    ∃ q : ℝ, q ∈ Set.Ioo s r ∧
      ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 2 / 4 <
        (r - s) *
          (2 * velocityH3DissipationAt u q +
            velocityH3TransportDerivativeAt u q) := by
  have hsAbs : s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 hs.1, hs.2⟩
  have hrAbs : r ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 hr.1, hr.2⟩
  have hEs := h3AuditActualSpectralVelocityTotal_energy_exact hH3 s hsAbs
  have hEr := h3AuditActualSpectralVelocityTotal_energy_exact hH3 r hrAbs
  have hDrop := h3Path_spectralHalfLoss_forces_squareEnergyDrop244
    (h3AuditActualSpectralVelocityTotal hH3 s)
    (h3AuditActualSpectralVelocityTotal hH3 r) hHalf
  have hPhysical :
      ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 2 / 4 <
        velocityH3EnergyAt u s - velocityH3EnergyAt u r := by
    linarith only [hDrop, hEs, hEr]
  have hInside (t : ℝ) (ht : t ∈ Set.Icc s r) :
      t ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le hs.1 ht.1, lt_of_le_of_lt ht.2 hr.2⟩
  have hDiffAt (t : ℝ) (ht : t ∈ Set.Icc s r) :
      DifferentiableAt ℝ (velocityH3EnergyAt u) t := by
    have hD : HasDerivAt (velocityH3EnergyAt u)
        (deriv (velocityH3EnergyAt u) t) t :=
      h3PathEnergyClassProducesCanonicalEnergyDifferentiability_of_orderEnergyDerivativeIdentities
        h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed
        u T hH3 a hClass t (hInside t ht)
    exact hD.differentiableAt
  have hContinuous : ContinuousOn (velocityH3EnergyAt u) (Set.Icc s r) := by
    intro t ht
    exact (hDiffAt t ht).continuousAt.continuousWithinAt
  have hDifferentiable : DifferentiableOn ℝ (velocityH3EnergyAt u)
      (Set.Ioo s r) := by
    intro t ht
    exact (hDiffAt t ⟨ht.1.le, ht.2.le⟩).differentiableWithinAt
  obtain ⟨q, hq, hSlope⟩ :=
    exists_deriv_eq_slope (velocityH3EnergyAt u) hsr
      hContinuous hDifferentiable
  have hqClass : q ∈ Set.Ioo a T :=
    hInside q ⟨hq.1.le, hq.2.le⟩
  have hBalance :=
    deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3 hClass hqClass
  have hGap : 0 < r - s := sub_pos.mpr hsr
  have hSecant :
      deriv (velocityH3EnergyAt u) q * (r - s) =
        velocityH3EnergyAt u r - velocityH3EnergyAt u s := by
    rw [hSlope]
    exact div_mul_cancel₀ _ (ne_of_gt hGap)
  have hSigned :
      2 * velocityH3DissipationAt u q +
        velocityH3TransportDerivativeAt u q =
        - deriv (velocityH3EnergyAt u) q := by
    linarith only [hBalance]
  have hScaled := congrArg (fun x : ℝ => (r - s) * x) hSigned
  have hRateEq :
      (r - s) * (2 * velocityH3DissipationAt u q +
        velocityH3TransportDerivativeAt u q) =
      velocityH3EnergyAt u s - velocityH3EnergyAt u r := by
    calc
      _ = (r - s) * (-deriv (velocityH3EnergyAt u) q) := hScaled
      _ = -(deriv (velocityH3EnergyAt u) q * (r - s)) := by ring
      _ = -(velocityH3EnergyAt u r - velocityH3EnergyAt u s) := by
        rw [hSecant]
      _ = velocityH3EnergyAt u s - velocityH3EnergyAt u r := by ring
  refine ⟨q, hq, ?_⟩
  rw [hRateEq]
  exact hPhysical

/-- The budget-determined peak clock forces either terminal compression or
an interior signed-transport-plus-viscosity rate with an explicit positive
lower bound. This upgrades the earlier raw half-amplitude-loss alternative. -/
theorem h3Path_optimizedPeak_terminalCompression_or_signedDrain244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (s : ℝ) (hs : s ∈ Set.Ioo b T)
    (hTwo : 2 ≤ ‖h3AuditActualSpectralVelocityTotal hH3 s‖)
    (hLarge : 32 * (velocityH3Energy0At u b + 1) ≤
      ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 2) :
    ∃ H : ℝ, 0 < H ∧
      ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 8 =
        16384 * (velocityH3Energy0At u b + 1) * H ^ 3 ∧
      let B := ∫ t in a..T, velocityH3DissipationAt u t
      T - s ≤ (B + 1) / H ∨
        ∃ r q : ℝ,
          r ∈ Set.Icc s (s + (B + 1) / H) ∧
          q ∈ Set.Ioo s r ∧
          ‖h3AuditActualSpectralVelocityTotal hH3 r‖ <
            ‖h3AuditActualSpectralVelocityTotal hH3 s‖ / 2 ∧
          ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 2 / 4 <
            (r - s) * (2 * velocityH3DissipationAt u q +
              velocityH3TransportDerivativeAt u q) := by
  obtain ⟨H, hH, hIdentity, hAlternative⟩ :=
    h3Path_optimizedPeak_terminalCompression_or_halfLoss244
      hH3 hClass hDInt b hb s hs hTwo hLarge
  let B : ℝ := ∫ t in a..T, velocityH3DissipationAt u t
  refine ⟨H, hH, hIdentity, ?_⟩
  change T - s ≤ (B + 1) / H ∨
    ∃ r q : ℝ,
      r ∈ Set.Icc s (s + (B + 1) / H) ∧
      q ∈ Set.Ioo s r ∧
      ‖h3AuditActualSpectralVelocityTotal hH3 r‖ <
        ‖h3AuditActualSpectralVelocityTotal hH3 s‖ / 2 ∧
      ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 2 / 4 <
        (r - s) * (2 * velocityH3DissipationAt u q +
          velocityH3TransportDerivativeAt u q)
  change T - s ≤ (B + 1) / H ∨
    ∃ r : ℝ, r ∈ Set.Icc s (s + (B + 1) / H) ∧
      ‖h3AuditActualSpectralVelocityTotal hH3 r‖ <
        ‖h3AuditActualSpectralVelocityTotal hH3 s‖ / 2 at hAlternative
  by_cases hCompressed : T - s ≤ (B + 1) / H
  · exact Or.inl hCompressed
  · right
    rcases hAlternative with hShort | ⟨r, hr, hHalf⟩
    · exact False.elim (hCompressed hShort)
    · have hEnd : s + (B + 1) / H < T := by
        have hEnd' : (B + 1) / H < T - s := lt_of_not_ge hCompressed
        linarith only [hEnd']
      have hrClass : r ∈ Set.Ioo a T :=
        ⟨lt_of_lt_of_le (lt_trans hb.1 hs.1) hr.1,
          lt_of_le_of_lt hr.2 hEnd⟩
      have hsr : s < r := by
        rcases lt_or_eq_of_le hr.1 with hlt | heq
        · exact hlt
        · subst r
          linarith only [hTwo, hHalf]
      obtain ⟨q, hq, hRate⟩ :=
        h3Path_physicalHalfLoss_forces_signedDrainSecant244
          hH3 hClass s r ⟨lt_trans hb.1 hs.1, hs.2⟩ hrClass hsr hHalf
      exact ⟨r, q, hr, hq, hHalf, hRate⟩

/-- End-to-end canonical source maximizers: on the original critical-width
witness sequence, each late peak either is terminally compressed on the
budget-scale clock or suffers an actual half-amplitude loss with a strict
intermediate signed-energy-drain secant. The source maximizers are unchanged. -/
theorem h3Path_noL2Trace_canonicalWidth_sourcePeakSignedDrain244
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
        ∀ b : ℝ, b ∈ Set.Ioo a T →
        ∀ᶠ k : ℕ in atTop,
          ∃ H : ℝ, 0 < H ∧
            ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ ^ 8 =
              16384 * (velocityH3Energy0At u b + 1) * H ^ 3 ∧
            let Budget := ∫ r in a..T, velocityH3DissipationAt u r
            T - s k ≤ (Budget + 1) / H ∨
              ∃ r q : ℝ,
                r ∈ Set.Icc (s k) (s k + (Budget + 1) / H) ∧
                q ∈ Set.Ioo (s k) r ∧
                ‖h3AuditActualSpectralVelocityTotal hH3 r‖ <
                  ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ / 2 ∧
                ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ ^ 2 / 4 <
                  (r - s k) *
                    (2 * velocityH3DissipationAt u q +
                      velocityH3TransportDerivativeAt u q)) := by
  obtain ⟨τ, N, K, C, δ, v, s, hv, hCofinal, hTime,
      hSeparate, hSummable, hCanonical, hPeak, hJoint⟩ :=
    h3Path_noL2Trace_finiteDissipation_canonicalWidth_fixedMaximizerJointEscape244
      hH3 hClass hTerminalMass hNoTrace hDInt
  refine ⟨τ, N, K, C, δ, v, s, hv, hCofinal, hTime,
    hSeparate, hSummable, hCanonical, hPeak, ?_⟩
  intro η B D hη hB hD hRegime b hb
  have hPeakEscape : Tendsto (fun k =>
      ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖) atTop atTop :=
    (hJoint η B D hη hB hD hRegime).2
  have hLate : ∀ᶠ k : ℕ in atTop, b < τ (v k) :=
    hCofinal.eventually (Ioi_mem_nhds hb.2)
  have hsEventually : ∀ᶠ k : ℕ in atTop, s k ∈ Set.Ioo b T := by
    filter_upwards [hLate] with k hk
    have hMid : τ (v k) + (T - τ (v k)) / 2 < T := by
      have ht := (hTime (v k)).2
      linarith only [ht]
    exact ⟨lt_of_lt_of_le hk (hPeak k).1.1,
      lt_of_le_of_lt (hPeak k).1.2 hMid⟩
  let L : ℝ := 32 * (velocityH3Energy0At u b + 1)
  have hNormLarge : ∀ᶠ k : ℕ in atTop,
      max L 2 ≤ ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ :=
    hPeakEscape.eventually (eventually_ge_atTop (max L 2))
  filter_upwards [hsEventually, hNormLarge] with k ht hk
  let A : ℝ := ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖
  have hTwo : 2 ≤ A := (le_max_right _ _).trans hk
  have hBound : L ≤ A := (le_max_left _ _).trans hk
  have hSq : A ≤ A ^ 2 := by
    have hMul : 0 ≤ A * (A - 1) :=
      mul_nonneg (by dsimp only [A]; exact norm_nonneg _)
        (by linarith only [hTwo])
    nlinarith only [hMul]
  have hLarge : 32 * (velocityH3Energy0At u b + 1) ≤ A ^ 2 :=
    le_trans (by simpa only [L] using hBound) hSq
  exact h3Path_optimizedPeak_terminalCompression_or_signedDrain244
    hH3 hClass hDInt b hb (s k) ht hTwo hLarge


end
end PrimeTensor.FirstMonomialTriad
