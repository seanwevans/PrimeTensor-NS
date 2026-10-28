import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalPeakAutomaticIntegratedTransport244
import Mathlib.Tactic

/-!
# Canonical half-loss forces an actual positive physical H³ transport spike

The preceding automatic signed-transport integrability proof identifies the
full physical transport integral on the genuine canonical half-loss interval.
If A = ‖U₃(s)‖ and B is the total finite physical H³ dissipation budget,
then the noncompressed half-loss interval [s,r] has length at most
L = (B+1)/H and carries signed transport integral strictly above A²/8.
Hence some q in [s,r] obeys
  H*A² < 8*(B+1)*Transport₃(q).
With the exact optimized identity A^8 = 16384*(E₀(b)+1)*H³, this implies
  A^14 < 8388608*(E₀(b)+1)*(B+1)^3*Transport₃(q)^3.
The time q is an actual physical time, not a new source maximizing time.
The original canonical source maxima and conditional critical-width regime
are preserved. No uniform terminal transport bound is obtained.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- A positive integral exceeding a constant-height rectangle forces an
actual point at or between the time endpoints above that height. The lemma
requires only interval-integrability, not temporal continuity of the rate. -/
theorem h3Path_integral_above_rectangle_exists_point244
    (f : ℝ → ℝ) (s r K : ℝ)
    (hsr : s ≤ r)
    (hInt : IntervalIntegrable f volume s r)
    (hLarge : (r - s) * K < ∫ t in s..r, f t) :
    ∃ q : ℝ, q ∈ Set.Icc s r ∧ K < f q := by
  by_contra hNo
  have hBound : ∀ q : ℝ, q ∈ Set.Icc s r → f q ≤ K := by
    intro q hq
    by_contra hNot
    exact hNo ⟨q, hq, lt_of_not_ge hNot⟩
  have hIntegral :
      (∫ t in s..r, f t) ≤ (∫ _t in s..r, K) :=
    intervalIntegral.integral_mono_on
      hsr hInt intervalIntegrable_const hBound
  have hConst : (∫ _t in s..r, K) = (r - s) * K := by
    simp [mul_comm]
  linarith only [hLarge, hIntegral, hConst]

/-- The budget clock and the strict integrated transport expenditure give
a pointwise lower bound on the genuine signed transport rate. No choice of
small continuity window is involved. -/
theorem h3Path_positiveTransportIntegral_forces_budgetClock_spike244
    (f : ℝ → ℝ) (A B H s r : ℝ)
    (hB : 0 ≤ B) (hH : 0 < H)
    (hsr : s ≤ r)
    (hClock : r - s ≤ (B + 1) / H)
    (hInt : IntervalIntegrable f volume s r)
    (hMass : A ^ 2 / 8 < ∫ t in s..r, f t) :
    ∃ q : ℝ, q ∈ Set.Icc s r ∧
      H * A ^ 2 < 8 * (B + 1) * f q := by
  have hDen : 0 < 8 * (B + 1) := by positivity
  have hWidth : (r - s) * H ≤ B + 1 := by
    calc
      (r - s) * H ≤ ((B + 1) / H) * H :=
        mul_le_mul_of_nonneg_right hClock hH.le
      _ = B + 1 := div_mul_cancel₀ _ (ne_of_gt hH)
  have hWidthMass : ((r - s) * H) * A ^ 2 ≤ (B + 1) * A ^ 2 :=
    mul_le_mul_of_nonneg_right hWidth (sq_nonneg A)
  have hShortMass :
      (r - s) * (H * A ^ 2 / (8 * (B + 1))) ≤ A ^ 2 / 8 := by
    calc
      (r - s) * (H * A ^ 2 / (8 * (B + 1))) =
          ((r - s) * H * A ^ 2) / (8 * (B + 1)) := by ring
      _ ≤ A ^ 2 / 8 := by
        apply (div_le_iff₀ hDen).2
        nlinarith only [hWidthMass]
  have hRectangle :
      (r - s) * (H * A ^ 2 / (8 * (B + 1))) <
        ∫ t in s..r, f t :=
    lt_of_le_of_lt hShortMass hMass
  obtain ⟨q, hq, hBig⟩ :=
    h3Path_integral_above_rectangle_exists_point244
      f s r (H * A ^ 2 / (8 * (B + 1))) hsr hInt hRectangle
  refine ⟨q, hq, ?_⟩
  have hScaled := (div_lt_iff₀ hDen).mp hBig
  nlinarith only [hScaled]

/-- Root-free consequence of the sharp optimized peak-height identity and
the actual positive transport-rate spike. It is a necessary lower rate,
not a transport upper bound. -/
theorem h3Path_transportSpike_fourteenthPower244
    (A E B H Tr : ℝ)
    (hE : 0 ≤ E) (hH : 0 < H)
    (hIdentity : A ^ 8 = 16384 * (E + 1) * H ^ 3)
    (hSpike : H * A ^ 2 < 8 * (B + 1) * Tr) :
    A ^ 14 < 8388608 * (E + 1) * (B + 1) ^ 3 * Tr ^ 3 := by
  have hNonneg : 0 ≤ H * A ^ 2 :=
    mul_nonneg hH.le (sq_nonneg A)
  have hCube : (H * A ^ 2) ^ 3 <
      (8 * (B + 1) * Tr) ^ 3 :=
    pow_lt_pow_left₀ hSpike hNonneg (by norm_num)
  have hFactor : 0 < 16384 * (E + 1) := by positivity
  have hScaled := mul_lt_mul_of_pos_left hCube hFactor
  calc
    A ^ 14 = A ^ 8 * A ^ 6 := by ring
    _ = (16384 * (E + 1) * H ^ 3) * A ^ 6 := by rw [hIdentity]
    _ = (16384 * (E + 1)) * (H * A ^ 2) ^ 3 := by ring
    _ < (16384 * (E + 1)) * (8 * (B + 1) * Tr) ^ 3 := hScaled
    _ = 8388608 * (E + 1) * (B + 1) ^ 3 * Tr ^ 3 := by ring

/-- At the original canonical source peak, terminal compression or a true
physical-time signed transport spike is necessary. The witness also obeys
the sharp fourteenth-power rate constraint. -/
theorem h3Path_optimizedPeak_terminalCompression_or_transportSpike244
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
        ∃ r q : ℝ,
          r ∈ Set.Icc s (s + (B + 1) / H) ∧
          q ∈ Set.Icc s r ∧
          ‖h3AuditActualSpectralVelocityTotal hH3 r‖ <
            ‖h3AuditActualSpectralVelocityTotal hH3 s‖ / 2 ∧
          H * ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 2 <
            8 * (B + 1) * velocityH3TransportDerivativeAt u q ∧
          ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 14 <
            8388608 * (velocityH3Energy0At u b + 1) *
              (B + 1) ^ 3 * velocityH3TransportDerivativeAt u q ^ 3 := by
  obtain ⟨H, hH, hIdentity, hAlternative⟩ :=
    h3Path_optimizedPeak_terminalCompression_or_integratedTransport_automatic244
      hH3 hClass hDInt b hb s hs hTwo hLarge hThreshold
  let B : ℝ := ∫ t in a..T, velocityH3DissipationAt u t
  refine ⟨H, hH, hIdentity, ?_⟩
  change T - s ≤ (B + 1) / H ∨
    ∃ r : ℝ,
      r ∈ Set.Icc s (s + (B + 1) / H) ∧
      ‖h3AuditActualSpectralVelocityTotal hH3 r‖ <
        ‖h3AuditActualSpectralVelocityTotal hH3 s‖ / 2 ∧
      ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 2 / 8 <
        ∫ t in s..r, velocityH3TransportDerivativeAt u t at hAlternative
  rcases hAlternative with hCompression | ⟨r, hr, hHalf, hMass⟩
  · exact Or.inl hCompression
  · by_cases hCompression : T - s ≤ (B + 1) / H
    · exact Or.inl hCompression
    · right
      have hEnd : s + (B + 1) / H < T := by
        have hShort := lt_of_not_ge hCompression
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
      have hB : 0 ≤ B := by
        dsimp only [B]
        exact intervalIntegral.integral_nonneg hClass.terminal_start.2.le
          (fun t _ => velocityH3DissipationAt_nonneg u t)
      have hClock : r - s ≤ (B + 1) / H := by
        linarith only [hr.2]
      have hTrInt :=
        h3Path_canonicalSignedTransport_intervalIntegrable_automatic244
          hH3 hClass hDInt s r hsClass hrClass hsr.le
      obtain ⟨q, hq, hSpike⟩ :=
        h3Path_positiveTransportIntegral_forces_budgetClock_spike244
          (velocityH3TransportDerivativeAt u)
          ‖h3AuditActualSpectralVelocityTotal hH3 s‖ B H s r
          hB hH hsr.le hClock hTrInt hMass
      have hE : 0 ≤ velocityH3Energy0At u b :=
        velocityH3Energy0At_nonneg u b
      have hPoly := h3Path_transportSpike_fourteenthPower244
        ‖h3AuditActualSpectralVelocityTotal hH3 s‖
        (velocityH3Energy0At u b) B H
        (velocityH3TransportDerivativeAt u q)
        hE hH hIdentity hSpike
      exact ⟨r, q, hr, hq, hHalf, hSpike, hPoly⟩


/-- The ORIGINAL canonical source-maximizing times retain their finite-annulus
witnesses and critical-width hypotheses. Eventually, each peak is terminally
compressed or has a true signed-transport spike satisfying a root-free
fourteenth-power lower bound. The point q is within the half-loss interval;
no transport point is asserted to maximize the projected physical source. -/
theorem h3Path_noL2Trace_canonicalWidth_sourcePeakTransportSpike244
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
              ∃ r q : ℝ,
                r ∈ Set.Icc (s k) (s k + (Budget + 1) / H) ∧
                q ∈ Set.Icc (s k) r ∧
                ‖h3AuditActualSpectralVelocityTotal hH3 r‖ <
                  ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ / 2 ∧
                H * ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ ^ 2 <
                  8 * (Budget + 1) * velocityH3TransportDerivativeAt u q ∧
                ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ ^ 14 <
                  8388608 * (velocityH3Energy0At u b + 1) *
                    (Budget + 1) ^ 3 * velocityH3TransportDerivativeAt u q ^ 3) := by
  obtain ⟨τ, N, K, C, δ, v, s, hv, hCofinal, hTime,
      hSeparate, hSummable, hCanonical, hPeak, hJoint⟩ :=
    h3Path_noL2Trace_canonicalWidth_sourcePeakIntegratedTransport_automatic244
      hH3 hClass hTerminalMass hNoTrace hDInt
  refine ⟨τ, N, K, C, δ, v, s, hv, hCofinal, hTime,
    hSeparate, hSummable, hCanonical, hPeak, ?_⟩
  intro η U V hη hU hV hRegime b hb
  have hLate := hJoint η U V hη hU hV hRegime b hb
  filter_upwards [hLate] with k hk
  obtain ⟨H, hH, hIdentity, hAlternative⟩ := hk
  let Budget : ℝ := ∫ t in a..T, velocityH3DissipationAt u t
  refine ⟨H, hH, hIdentity, ?_⟩
  change T - s k ≤ (Budget + 1) / H ∨
    ∃ r : ℝ,
      r ∈ Set.Icc (s k) (s k + (Budget + 1) / H) ∧
      ‖h3AuditActualSpectralVelocityTotal hH3 r‖ <
        ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ / 2 ∧
      ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ ^ 2 / 8 <
        ∫ t in (s k)..r, velocityH3TransportDerivativeAt u t at hAlternative
  rcases hAlternative with hCompression | ⟨r, hr, hHalf, hMass⟩
  · exact Or.inl hCompression
  · by_cases hCompression : T - s k ≤ (Budget + 1) / H
    · exact Or.inl hCompression
    · right
      have hEnd : s k + (Budget + 1) / H < T := by
        have hShort := lt_of_not_ge hCompression
        linarith only [hShort]
      have hsr : s k < r := by
        rcases lt_or_eq_of_le hr.1 with hlt | heq
        · exact hlt
        · subst r
          have hNonnegative := norm_nonneg (h3AuditActualSpectralVelocityTotal hH3 (s k))
          linarith only [hHalf, hNonnegative]
      have hsClass : s k ∈ Set.Ioo a T := by
        have hLeft := (hPeak k).1.1
        have hRight := (hPeak k).1.2
        have hTau := (hTime (v k)).1
        have hEndMid : τ (v k) + (T - τ (v k)) / 2 < T := by
          linarith only [(hTime (v k)).2]
        exact ⟨lt_of_lt_of_le hTau hLeft, lt_of_le_of_lt hRight hEndMid⟩
      have hrClass : r ∈ Set.Ioo a T :=
        ⟨lt_of_lt_of_le hsClass.1 hr.1, lt_of_le_of_lt hr.2 hEnd⟩
      have hB : 0 ≤ Budget := by
        dsimp only [Budget]
        exact intervalIntegral.integral_nonneg hClass.terminal_start.2.le
          (fun t _ => velocityH3DissipationAt_nonneg u t)
      have hClock : r - s k ≤ (Budget + 1) / H := by
        linarith only [hr.2]
      have hTrInt :=
        h3Path_canonicalSignedTransport_intervalIntegrable_automatic244
          hH3 hClass hDInt (s k) r hsClass hrClass hsr.le
      obtain ⟨q, hq, hSpike⟩ :=
        h3Path_positiveTransportIntegral_forces_budgetClock_spike244
          (velocityH3TransportDerivativeAt u)
          ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ Budget H (s k) r
          hB hH hsr.le hClock hTrInt hMass
      have hE : 0 ≤ velocityH3Energy0At u b :=
        velocityH3Energy0At_nonneg u b
      have hPoly := h3Path_transportSpike_fourteenthPower244
        ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖
        (velocityH3Energy0At u b) Budget H
        (velocityH3TransportDerivativeAt u q)
        hE hH hIdentity hSpike
      exact ⟨r, q, hr, hq, hHalf, hSpike, hPoly⟩

end
end PrimeTensor.FirstMonomialTriad
