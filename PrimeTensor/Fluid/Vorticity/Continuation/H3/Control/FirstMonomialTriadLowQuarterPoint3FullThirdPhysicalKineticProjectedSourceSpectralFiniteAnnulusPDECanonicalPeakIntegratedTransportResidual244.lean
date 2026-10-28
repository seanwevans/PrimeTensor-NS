import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalPeakSignedDrainSplit244
import Mathlib.Tactic

/-!
# Canonical peak half-loss: finite viscous budget forces integrated transport expenditure

The exact physical energy gap, not the pointwise MVT rate, is the object here.
At a half-loss event, with A = ‖U₃(s)‖, the genuine H³ energy drops by more
than A²/4. Nonnegativity and finite total H³ dissipation imply
  ∫_s^r D₃ ≤ B := ∫_a^T D₃.
Therefore the exact residual
  E₃(s) - E₃(r) - 2 ∫_s^r D₃
is strictly above A²/4 - 2B, and is above A²/8 if A² ≥ 16B.

By the exact PDE balance E₃' = -2D₃ - Transport₃, this residual is the
signed integrated transport when the local temporal FTC/integrability has
also been established. We do not silently assume that identity here.

The original canonical source-maximizing times and the preceding
conditional critical-width hypotheses are preserved.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Global physical dissipation bounds every ordered interior subinterval. -/
theorem h3Path_physicalDissipation_subinterval_le_budget244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (_haT : a ≤ T)
    (s r : ℝ) (has : a ≤ s) (hsr : s ≤ r) (hrT : r ≤ T) :
    (∫ t in s..r, velocityH3DissipationAt u t) ≤
      ∫ t in a..T, velocityH3DissipationAt u t := by
  have hPos :
      0 ≤ᵐ[volume.restrict (Set.Ioc a T)]
        (velocityH3DissipationAt u) :=
    Filter.Eventually.of_forall
      (fun t => velocityH3DissipationAt_nonneg u t)
  exact intervalIntegral.integral_mono_interval
    has hsr hrT hPos hDInt

/-- Half-loss exceeds a quarter of the original square amplitude even
after paying the ENTIRE available viscous expenditure twice. No temporal
transport integrability assumption occurs in this inequality. -/
theorem h3Path_physicalHalfLoss_signedTransportResidual_budgetLower244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (s r : ℝ) (hs : s ∈ Set.Ioo a T) (hr : r ∈ Set.Ioo a T)
    (hsr : s < r)
    (hHalf : ‖h3AuditActualSpectralVelocityTotal hH3 r‖ <
      ‖h3AuditActualSpectralVelocityTotal hH3 s‖ / 2) :
    ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 2 / 4 <
      (velocityH3EnergyAt u s - velocityH3EnergyAt u r -
        2 * (∫ t in s..r, velocityH3DissipationAt u t)) +
        2 * (∫ t in a..T, velocityH3DissipationAt u t) := by
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
  have hBudget := h3Path_physicalDissipation_subinterval_le_budget244
    hDInt hClass.terminal_start.2.le s r hs.1.le hsr.le hr.2.le
  linarith only [hPhysical, hBudget]

/-- Once A² ≥ 16B, the net transport residual is strictly greater than
A²/8. This is a lower bound on a genuinely integrated energy residual,
not on the transport evaluated at the MVT point. -/
theorem h3Path_physicalHalfLoss_positiveTransportResidual244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (s r : ℝ) (hs : s ∈ Set.Ioo a T) (hr : r ∈ Set.Ioo a T)
    (hsr : s < r)
    (hHalf : ‖h3AuditActualSpectralVelocityTotal hH3 r‖ <
      ‖h3AuditActualSpectralVelocityTotal hH3 s‖ / 2)
    (hThreshold :
      16 * (∫ t in a..T, velocityH3DissipationAt u t) ≤
        ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 2) :
    ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 2 / 8 <
      velocityH3EnergyAt u s - velocityH3EnergyAt u r -
        2 * (∫ t in s..r, velocityH3DissipationAt u t) := by
  have hLower := h3Path_physicalHalfLoss_signedTransportResidual_budgetLower244
    hH3 hClass hDInt s r hs hr hsr hHalf
  linarith only [hLower, hThreshold]

/-- At an original canonical peak above the finite-budget threshold,
either the existing optimized clock compresses into the terminal time,
or the real H³ energy loses more than A²/8 beyond what viscosity can pay.
The peak time s and the half-loss observation r are not reselected. -/
theorem h3Path_optimizedPeak_terminalCompression_or_integratedTransportResidual244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (s : ℝ) (hs : s ∈ Set.Ioo b T)
    (hTwo : 2 ≤ ‖h3AuditActualSpectralVelocityTotal hH3 s‖)
    (hLarge : 32 * (velocityH3Energy0At u b + 1) ≤
      ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 2)
    (hThreshold : 16 * (∫ t in a..T, velocityH3DissipationAt u t) ≤
      ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 2) :
    ∃ H : ℝ, 0 < H ∧
      ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 8 =
        16384 * (velocityH3Energy0At u b + 1) * H ^ 3 ∧
      let B := ∫ t in a..T, velocityH3DissipationAt u t
      T - s ≤ (B + 1) / H ∨
        ∃ r : ℝ,
          r ∈ Set.Icc s (s + (B + 1) / H) ∧
          ‖h3AuditActualSpectralVelocityTotal hH3 r‖ <
            ‖h3AuditActualSpectralVelocityTotal hH3 s‖ / 2 ∧
          ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 2 / 8 <
            velocityH3EnergyAt u s - velocityH3EnergyAt u r -
              2 * (∫ t in s..r, velocityH3DissipationAt u t) := by
  obtain ⟨H, hH, hIdentity, hAlternative⟩ :=
    h3Path_optimizedPeak_terminalCompression_or_halfLoss244
      hH3 hClass hDInt b hb s hs hTwo hLarge
  let B : ℝ := ∫ t in a..T, velocityH3DissipationAt u t
  refine ⟨H, hH, hIdentity, ?_⟩
  change T - s ≤ (B + 1) / H ∨
    ∃ r : ℝ,
      r ∈ Set.Icc s (s + (B + 1) / H) ∧
      ‖h3AuditActualSpectralVelocityTotal hH3 r‖ <
        ‖h3AuditActualSpectralVelocityTotal hH3 s‖ / 2 at hAlternative
  rcases hAlternative with hCompressed | ⟨r, hr, hHalf⟩
  · exact Or.inl hCompressed
  · by_cases hCompressed : T - s ≤ (B + 1) / H
    · exact Or.inl hCompressed
    · right
      have hEnd : s + (B + 1) / H < T := by
        have hShort := lt_of_not_ge hCompressed
        linarith only [hShort]
      have hsr : s < r := by
        rcases lt_or_eq_of_le hr.1 with hlt | heq
        · exact hlt
        · subst r
          linarith only [hTwo, hHalf]
      have hsClass : s ∈ Set.Ioo a T :=
        ⟨lt_trans hb.1 hs.1, hs.2⟩
      have hrClass : r ∈ Set.Ioo a T :=
        ⟨lt_of_lt_of_le hsClass.1 hr.1, lt_of_le_of_lt hr.2 hEnd⟩
      have hResidual := h3Path_physicalHalfLoss_positiveTransportResidual244
        hH3 hClass hDInt s r hsClass hrClass hsr hHalf hThreshold
      exact ⟨r, hr, hHalf, hResidual⟩


/-- The net physical energy residual is exactly the integral of the signed
transport channel when the ACTUAL energy derivative and transport are locally
interval-integrable. Both analytic hypotheses are visible. -/
theorem h3Path_physicalSignedTransportResidual_eq_integral244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (s r : ℝ) (hs : s ∈ Set.Ioo a T) (hr : r ∈ Set.Ioo a T)
    (hsr : s < r)
    (hDerivativeInt : IntervalIntegrable
      (deriv (velocityH3EnergyAt u)) volume s r)
    (hTrInt : IntervalIntegrable
      (velocityH3TransportDerivativeAt u) volume s r) :
    velocityH3EnergyAt u s - velocityH3EnergyAt u r -
        2 * (∫ t in s..r, velocityH3DissipationAt u t) =
      ∫ t in s..r, velocityH3TransportDerivativeAt u t := by
  have hDIntLocal : IntervalIntegrable
      (velocityH3DissipationAt u) volume s r := by
    apply hDInt.mono_set
    rw [Set.uIcc_of_le hsr.le, Set.uIcc_of_le hClass.terminal_start.2.le]
    exact Set.Icc_subset_Icc hs.1.le hr.2.le
  have hInside (t : ℝ) (ht : t ∈ Set.Icc s r) :
      t ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le hs.1 ht.1, lt_of_le_of_lt ht.2 hr.2⟩
  have hDiff : ∀ t : ℝ, t ∈ Set.uIcc s r →
      DifferentiableAt ℝ (velocityH3EnergyAt u) t := by
    intro t ht
    rw [Set.uIcc_of_le hsr.le] at ht
    have hD : HasDerivAt (velocityH3EnergyAt u)
        (deriv (velocityH3EnergyAt u) t) t :=
      h3PathEnergyClassProducesCanonicalEnergyDifferentiability_of_orderEnergyDerivativeIdentities
        h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed
        u T hH3 a hClass t (hInside t ht)
    exact hD.differentiableAt
  have hFTC :
      (∫ t in s..r, deriv (velocityH3EnergyAt u) t) =
        velocityH3EnergyAt u r - velocityH3EnergyAt u s :=
    intervalIntegral.integral_deriv_eq_sub hDiff hDerivativeInt
  have hEqualIntegral :
      (∫ t in s..r, deriv (velocityH3EnergyAt u) t) =
        ∫ t in s..r,
          -(2 * velocityH3DissipationAt u t +
            velocityH3TransportDerivativeAt u t) := by
    apply intervalIntegral.integral_congr_Ioo_of_le hsr.le
    intro t ht
    have hBalance :=
      deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
        hH3 hClass (hInside t ⟨ht.1.le, ht.2.le⟩)
    linarith only [hBalance]
  have hSources :
      (∫ t in s..r,
        -(2 * velocityH3DissipationAt u t +
          velocityH3TransportDerivativeAt u t)) =
        -(2 * (∫ t in s..r, velocityH3DissipationAt u t)) -
          (∫ t in s..r, velocityH3TransportDerivativeAt u t) := by
    rw [intervalIntegral.integral_neg,
      intervalIntegral.integral_add (hDIntLocal.const_mul 2) hTrInt,
      intervalIntegral.integral_const_mul]
    ring
  rw [hEqualIntegral, hSources] at hFTC
  linarith only [hFTC]

/-- Under the explicit local FTC hypotheses, large canonical half-loss
forces a POSITIVE INTEGRAL of the actual signed physical transport. -/
theorem h3Path_physicalHalfLoss_positiveIntegratedTransport244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (s r : ℝ) (hs : s ∈ Set.Ioo a T) (hr : r ∈ Set.Ioo a T)
    (hsr : s < r)
    (hHalf : ‖h3AuditActualSpectralVelocityTotal hH3 r‖ <
      ‖h3AuditActualSpectralVelocityTotal hH3 s‖ / 2)
    (hThreshold :
      16 * (∫ t in a..T, velocityH3DissipationAt u t) ≤
        ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 2)
    (hDerivativeInt : IntervalIntegrable
      (deriv (velocityH3EnergyAt u)) volume s r)
    (hTrInt : IntervalIntegrable
      (velocityH3TransportDerivativeAt u) volume s r) :
    ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 2 / 8 <
      ∫ t in s..r, velocityH3TransportDerivativeAt u t := by
  have hResidual := h3Path_physicalHalfLoss_positiveTransportResidual244
    hH3 hClass hDInt s r hs hr hsr hHalf hThreshold
  have hIdentity := h3Path_physicalSignedTransportResidual_eq_integral244
    hH3 hClass hDInt s r hs hr hsr hDerivativeInt hTrInt
  rw [hIdentity] at hResidual
  exact hResidual


/-- On the unchanged canonical source-maximizer sequence, the finite total
viscous budget is eventually negligible compared with the escaping H³ peak
square. In the same conditional critical-width regime, late peaks therefore
obey terminal compression or a strictly positive integrated transport residual.
No new times are selected, and no temporal FTC is silently assumed. -/
theorem h3Path_noL2Trace_canonicalWidth_sourcePeakIntegratedTransportResidual244
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
      (∀ η U V : ℝ, 0 < η → 0 ≤ U → 0 ≤ V →
        (∀ᶠ k : ℕ in atTop,
          η ≤ ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2) ∧
          h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1 ≤
            U * (((v k : ℝ) + 1) ^ 6) ∧
          (((N (v k) - v k : ℕ) : ℝ) + 1) ^ 8 ≤
            V * (((v k : ℝ) + 1) ^ 9)) →
        ∀ b : ℝ, b ∈ Set.Ioo a T →
        ∀ᶠ k : ℕ in atTop,
          ∃ H : ℝ, 0 < H ∧
            ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ ^ 8 =
              16384 * (velocityH3Energy0At u b + 1) * H ^ 3 ∧
            let Budget := ∫ t in a..T, velocityH3DissipationAt u t
            T - s k ≤ (Budget + 1) / H ∨
              ∃ r : ℝ,
                r ∈ Set.Icc (s k) (s k + (Budget + 1) / H) ∧
                ‖h3AuditActualSpectralVelocityTotal hH3 r‖ <
                  ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ / 2 ∧
                ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ ^ 2 / 8 <
                  velocityH3EnergyAt u (s k) - velocityH3EnergyAt u r -
                    2 * (∫ t in (s k)..r, velocityH3DissipationAt u t)) := by
  obtain ⟨τ, N, K, C, δ, v, s, hv, hCofinal, hTime,
      hSeparate, hSummable, hCanonical, hPeak, hJoint⟩ :=
    h3Path_noL2Trace_finiteDissipation_canonicalWidth_fixedMaximizerJointEscape244
      hH3 hClass hTerminalMass hNoTrace hDInt
  refine ⟨τ, N, K, C, δ, v, s, hv, hCofinal, hTime,
    hSeparate, hSummable, hCanonical, hPeak, ?_⟩
  intro η U V hη hU hV hRegime b hb
  have hPeakEscape : Tendsto (fun k =>
      ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖) atTop atTop :=
    (hJoint η U V hη hU hV hRegime).2
  have hLate : ∀ᶠ k : ℕ in atTop, b < τ (v k) :=
    hCofinal.eventually (Ioi_mem_nhds hb.2)
  have hsEventually : ∀ᶠ k : ℕ in atTop, s k ∈ Set.Ioo b T := by
    filter_upwards [hLate] with k hk
    have hMid : τ (v k) + (T - τ (v k)) / 2 < T := by
      have ht := (hTime (v k)).2
      linarith only [ht]
    exact ⟨lt_of_lt_of_le hk (hPeak k).1.1,
      lt_of_le_of_lt (hPeak k).1.2 hMid⟩
  let Budget : ℝ := ∫ t in a..T, velocityH3DissipationAt u t
  let L : ℝ := max
    (32 * (velocityH3Energy0At u b + 1)) (16 * Budget)
  have hNormLarge : ∀ᶠ k : ℕ in atTop,
      max L 2 ≤ ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ :=
    hPeakEscape.eventually (eventually_ge_atTop (max L 2))
  filter_upwards [hsEventually, hNormLarge] with k ht hk
  let A : ℝ := ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖
  have hTwo : 2 ≤ A := (le_max_right _ _).trans hk
  have hBoundL : L ≤ A := (le_max_left _ _).trans hk
  have hSq : A ≤ A ^ 2 := by
    have hMul : 0 ≤ A * (A - 1) :=
      mul_nonneg (by dsimp only [A]; exact norm_nonneg _)
        (by linarith only [hTwo])
    nlinarith only [hMul]
  have hLarge : 32 * (velocityH3Energy0At u b + 1) ≤ A ^ 2 := by
    exact (le_trans (le_trans (le_max_left _ _) hBoundL) hSq)
  have hThreshold : 16 * Budget ≤ A ^ 2 := by
    exact (le_trans (le_trans (le_max_right _ _) hBoundL) hSq)
  exact h3Path_optimizedPeak_terminalCompression_or_integratedTransportResidual244
    hH3 hClass hDInt b hb (s k) ht hTwo hLarge
    (by simpa only [Budget, A] using hThreshold)

end
end PrimeTensor.FirstMonomialTriad
