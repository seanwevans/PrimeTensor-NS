import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalPeakSignedDrain244
import Mathlib.Tactic

/-!
# Forced physical viscous or signed-transport expenditure after canonical half-loss

At an actual canonical source-peak time s, the prior exact H³ energy balance
and mean-value theorem give a point q between s and the first reported half-loss
observation r with

  A²/4 < (r-s) * (2 D(q) + Transport(q)).

The budget clock is L=(B+1)/H, with B the full finite physical H³ dissipation
integral and A^8=16384*(E₀(b)+1)*H^3. Since r-s <= L, the actual physical
signed drain must obey

  H*A² < 4*(B+1)*(2D(q)+Transport(q)).

Consequently either

  H*A² < 16*(B+1)*D(q)

or

  H*A² < 8*(B+1)*Transport(q).

In the second branch the signed transport is necessarily positive. Cubing the
unsplit drain inequality also gives the exact root-free polynomial constraint

  A^14 < 1048576*(E₀(b)+1)*(B+1)^3*(2D(q)+Transport(q))^3.

These are necessary alternatives, not new bounds on either physical PDE term.
No terminal contradiction, global regularity, or uniform persistence is claimed.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- The fixed physical budget clock turns the signed MVT secant into a
rate inequality independent of the arbitrarily selected local continuity
radius. The secant itself forces the signed drain rate to be positive. -/
theorem h3Path_signedDrain_budgetClock_normalizedRate244
    (A B H D Tr d : ℝ)
    (hH : 0 < H) (hd : 0 < d)
    (hClock : d ≤ (B + 1) / H)
    (hSecant : A ^ 2 / 4 < d * (2 * D + Tr)) :
    H * A ^ 2 < 4 * (B + 1) * (2 * D + Tr) := by
  have hPosProduct : 0 < d * (2 * D + Tr) :=
    lt_of_le_of_lt (by positivity : 0 ≤ A ^ 2 / 4) hSecant
  have hRatePos : 0 < 2 * D + Tr := by
    by_contra hNot
    have hNonpos : 2 * D + Tr ≤ 0 := le_of_not_gt hNot
    have hProdNonpos : d * (2 * D + Tr) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hd.le hNonpos
    linarith only [hPosProduct, hProdNonpos]
  have hWidthCost : d * H ≤ B + 1 := by
    have hMul := mul_le_mul_of_nonneg_right hClock hH.le
    have hCancel : ((B + 1) / H) * H = B + 1 :=
      div_mul_cancel₀ _ (ne_of_gt hH)
    linarith only [hMul, hCancel]
  have hUpper : d * H * (2 * D + Tr) ≤
      (B + 1) * (2 * D + Tr) :=
    mul_le_mul_of_nonneg_right hWidthCost hRatePos.le
  have hLower : A ^ 2 / 4 * H <
      (d * (2 * D + Tr)) * H :=
    mul_lt_mul_of_pos_right hSecant hH
  nlinarith only [hUpper, hLower]

/-- A large positive signed physical drain must be paid for either by
physical viscosity or by strictly positive signed transport. The two
branches are deliberately not conflated with a sign bound on transport. -/
theorem h3Path_signedDrain_normalizedRate_viscousOrTransport244
    (X B D Tr : ℝ)
    (hRate : X < 4 * (B + 1) * (2 * D + Tr)) :
    X < 16 * (B + 1) * D ∨
      X < 8 * (B + 1) * Tr := by
  by_cases hViscous : X < 16 * (B + 1) * D
  · exact Or.inl hViscous
  · right
    have hViscousNot : 16 * (B + 1) * D ≤ X :=
      le_of_not_gt hViscous
    nlinarith only [hRate, hViscousNot]

/-- The exact optimized sixth-root peak-height identity converts the
normalized signed-drain rate into a fourteenth-power polynomial constraint.
This is a RATE necessity and does not bound the rate from above. -/
theorem h3Path_signedDrain_normalizedRate_fourteenthPower244
    (A E B H D Tr : ℝ)
    (hE : 0 ≤ E) (hH : 0 < H)
    (hIdentity : A ^ 8 = 16384 * (E + 1) * H ^ 3)
    (hRate : H * A ^ 2 < 4 * (B + 1) * (2 * D + Tr)) :
    A ^ 14 < 1048576 * (E + 1) * (B + 1) ^ 3 *
      (2 * D + Tr) ^ 3 := by
  have hNonneg : 0 ≤ H * A ^ 2 :=
    mul_nonneg hH.le (sq_nonneg A)
  have hCube : (H * A ^ 2) ^ 3 <
      (4 * (B + 1) * (2 * D + Tr)) ^ 3 :=
    pow_lt_pow_left₀ hRate hNonneg (by norm_num)
  have hFactor : 0 < 16384 * (E + 1) := by positivity
  have hScaled := mul_lt_mul_of_pos_left hCube hFactor
  calc
    A ^ 14 = A ^ 8 * A ^ 6 := by ring
    _ = (16384 * (E + 1) * H ^ 3) * A ^ 6 := by rw [hIdentity]
    _ = (16384 * (E + 1)) * (H * A ^ 2) ^ 3 := by ring
    _ < (16384 * (E + 1)) *
        (4 * (B + 1) * (2 * D + Tr)) ^ 3 := hScaled
    _ = 1048576 * (E + 1) * (B + 1) ^ 3 *
          (2 * D + Tr) ^ 3 := by ring

/-- At the ORIGINAL strict physical source peak, either the fixed
budget clock reaches the terminal time, or an actual intermediate time
carries a quantified viscous-or-positive-transport drain. Its full signed
rate also obeys an explicit fourteenth-power necessary lower bound. -/
theorem h3Path_optimizedPeak_terminalCompression_or_signedDrainSplit244
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
          H * ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 2 <
            4 * (B + 1) * (2 * velocityH3DissipationAt u q +
              velocityH3TransportDerivativeAt u q) ∧
          (H * ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 2 <
              16 * (B + 1) * velocityH3DissipationAt u q ∨
            H * ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 2 <
              8 * (B + 1) * velocityH3TransportDerivativeAt u q) ∧
          ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 14 <
            1048576 * (velocityH3Energy0At u b + 1) * (B + 1) ^ 3 *
              (2 * velocityH3DissipationAt u q +
                velocityH3TransportDerivativeAt u q) ^ 3 := by
  obtain ⟨H, hH, hIdentity, hAlternative⟩ :=
    h3Path_optimizedPeak_terminalCompression_or_signedDrain244
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
          velocityH3TransportDerivativeAt u q) at hAlternative
  rcases hAlternative with hCompression | ⟨r, q, hr, hq, hHalf, hSecant⟩
  · exact Or.inl hCompression
  · right
    have hPos : 0 < r - s := sub_pos.mpr (lt_trans hq.1 hq.2)
    have hClock : r - s ≤ (B + 1) / H := by
      have hRight := hr.2
      linarith only [hRight]
    have hRate := h3Path_signedDrain_budgetClock_normalizedRate244
      ‖h3AuditActualSpectralVelocityTotal hH3 s‖ B H
      (velocityH3DissipationAt u q)
      (velocityH3TransportDerivativeAt u q)
      (r - s) hH hPos hClock hSecant
    have hSplit := h3Path_signedDrain_normalizedRate_viscousOrTransport244
      (H * ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 2)
      B (velocityH3DissipationAt u q)
      (velocityH3TransportDerivativeAt u q) hRate
    have hE : 0 ≤ velocityH3Energy0At u b :=
      velocityH3Energy0At_nonneg u b
    have hFourteen := h3Path_signedDrain_normalizedRate_fourteenthPower244
      ‖h3AuditActualSpectralVelocityTotal hH3 s‖
      (velocityH3Energy0At u b) B H
      (velocityH3DissipationAt u q)
      (velocityH3TransportDerivativeAt u q)
      hE hH hIdentity hRate
    exact ⟨r, q, hr, hq, hHalf, hRate, hSplit, hFourteen⟩

/-- Preserve the EXACT canonical physical projected-source maximizing times
and quadratic-sharp annulus witnesses in the unchanged critical-width regime.
Each sufficiently late peak obeys terminal compression or the actual
viscous-versus-signed-transport drain split at an intermediate physical time. -/
theorem h3Path_noL2Trace_canonicalWidth_sourcePeakSignedDrainSplit244
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
            let Budget := ∫ t in a..T, velocityH3DissipationAt u t
            T - s k ≤ (Budget + 1) / H ∨
              ∃ r q : ℝ,
                r ∈ Set.Icc (s k) (s k + (Budget + 1) / H) ∧
                q ∈ Set.Ioo (s k) r ∧
                ‖h3AuditActualSpectralVelocityTotal hH3 r‖ <
                  ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ / 2 ∧
                H * ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ ^ 2 <
                  4 * (Budget + 1) *
                    (2 * velocityH3DissipationAt u q +
                      velocityH3TransportDerivativeAt u q) ∧
                (H * ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ ^ 2 <
                    16 * (Budget + 1) * velocityH3DissipationAt u q ∨
                  H * ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ ^ 2 <
                    8 * (Budget + 1) * velocityH3TransportDerivativeAt u q) ∧
                ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ ^ 14 <
                  1048576 * (velocityH3Energy0At u b + 1) *
                    (Budget + 1) ^ 3 *
                      (2 * velocityH3DissipationAt u q +
                        velocityH3TransportDerivativeAt u q) ^ 3) := by
  obtain ⟨τ, N, K, C, δ, v, s, hv, hCofinal, hTime,
      hSeparate, hSummable, hCanonical, hPeak, hJoint⟩ :=
    h3Path_noL2Trace_canonicalWidth_sourcePeakSignedDrain244
      hH3 hClass hTerminalMass hNoTrace hDInt
  refine ⟨τ, N, K, C, δ, v, s, hv, hCofinal, hTime,
    hSeparate, hSummable, hCanonical, hPeak, ?_⟩
  intro η B D hη hB hD hRegime b hb
  have hLate := hJoint η B D hη hB hD hRegime b hb
  filter_upwards [hLate] with k hk
  obtain ⟨H, hH, hIdentity, hAlternative⟩ := hk
  let Budget : ℝ := ∫ t in a..T, velocityH3DissipationAt u t
  refine ⟨H, hH, hIdentity, ?_⟩
  change T - s k ≤ (Budget + 1) / H ∨
    ∃ r q : ℝ,
      r ∈ Set.Icc (s k) (s k + (Budget + 1) / H) ∧
      q ∈ Set.Ioo (s k) r ∧
      ‖h3AuditActualSpectralVelocityTotal hH3 r‖ <
        ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ / 2 ∧
      ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ ^ 2 / 4 <
        (r - s k) * (2 * velocityH3DissipationAt u q +
          velocityH3TransportDerivativeAt u q) at hAlternative
  rcases hAlternative with hCompression | ⟨r, q, hr, hq, hHalf, hSecant⟩
  · exact Or.inl hCompression
  · right
    have hPos : 0 < r - s k := sub_pos.mpr (lt_trans hq.1 hq.2)
    have hClock : r - s k ≤ (Budget + 1) / H := by
      have hRight := hr.2
      linarith only [hRight]
    have hRate := h3Path_signedDrain_budgetClock_normalizedRate244
      ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ Budget H
      (velocityH3DissipationAt u q)
      (velocityH3TransportDerivativeAt u q)
      (r - s k) hH hPos hClock hSecant
    have hSplit := h3Path_signedDrain_normalizedRate_viscousOrTransport244
      (H * ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ ^ 2)
      Budget (velocityH3DissipationAt u q)
      (velocityH3TransportDerivativeAt u q) hRate
    have hE : 0 ≤ velocityH3Energy0At u b :=
      velocityH3Energy0At_nonneg u b
    have hFourteen := h3Path_signedDrain_normalizedRate_fourteenthPower244
      ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖
      (velocityH3Energy0At u b) Budget H
      (velocityH3DissipationAt u q)
      (velocityH3TransportDerivativeAt u q)
      hE hH hIdentity hRate
    exact ⟨r, q, hr, hq, hHalf, hRate, hSplit, hFourteen⟩

end
end PrimeTensor.FirstMonomialTriad
