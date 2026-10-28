import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalPeakCubicWidthClock244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralQuantitativeTemporalDissipationWindow244
import Mathlib.Tactic

/-!
# Canonical physical source peaks: forced half-amplitude loss or terminal compression

The previous cubic-width-clock theorem concerns a CHOSEN persistence width,
which may always be shortened. This module instead examines a definite time
scale determined by the total available physical dissipation budget and the
optimized Fourier coercivity height at the ORIGINAL peak.

For A = ‖U₃(s)‖ sufficiently large, E = E₀(b), B = ∫_a^T D₃(t) dt,
construct H > 0 with A^8 = 16384*(E+1)*H^3 and a GLOBAL implication:

  (b < r < T and A/2 <= ‖U₃(r)‖) ==> H <= D₃(r).

Define L = (B+1)/H. Either T-s <= L, or there is an ACTUAL physical
observation r in [s,s+L] with ‖U₃(r)‖ < A/2. The first alternative gives

  (T-s)^3 * A^8 <= 16384*(E+1)*(B+1)^3.

This is an unavoidable time-scale alternative independent of the arbitrarily
chosen positive continuity neighborhoods. No contradiction or global H³
regularity claim follows: rapid norm loss remains compatible with finite
H³ dissipation unless another PDE estimate rules it out.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- A nonnegative time density with a finite encompassing integral cannot
remain above a floor on an interval whose height-width cost exceeds the
whole budget. No disjoint-window extraction is needed. -/
theorem h3Path_finiteIntegral_forces_floorFailure244
    (f : ℝ → ℝ) (a T s L H : ℝ)
    (haT : a ≤ T) (has : a ≤ s) (hL : 0 < L)
    (hEnd : s + L < T)
    (hf : ∀ r : ℝ, 0 ≤ f r)
    (hInt : IntervalIntegrable f volume a T)
    (hTooExpensive : (∫ r in a..T, f r) < L * H) :
    ∃ r : ℝ, r ∈ Set.Icc s (s + L) ∧ f r < H := by
  by_contra hNo
  have hFloor (r : ℝ) (hr : r ∈ Set.Icc s (s + L)) :
      H ≤ f r := by
    by_contra hNot
    exact hNo ⟨r, hr, lt_of_not_ge hNot⟩
  have hRight : s ≤ s + L := by linarith only [hL]
  have hIntLocal : IntervalIntegrable f volume s (s + L) := by
    apply hInt.mono_set
    rw [Set.uIcc_of_le hRight, Set.uIcc_of_le haT]
    exact Set.Icc_subset_Icc has hEnd.le
  have hCost := h3Path_localPositiveHeight_forces_integratedCost244
    f s (s + L) H hRight hIntLocal hFloor
  have hPos : 0 ≤ᵐ[volume.restrict (Set.Ioc a T)] f :=
    Filter.Eventually.of_forall (fun r => hf r)
  have hBudget :
      (∫ r in s..(s + L), f r) ≤ (∫ r in a..T, f r) :=
    intervalIntegral.integral_mono_interval
      has hRight hEnd.le hPos hInt
  have hCost' : L * H ≤ (∫ r in s..(s + L), f r) := by
    convert hCost using 1 <;> ring
  exact (not_lt_of_ge (hCost'.trans hBudget)) hTooExpensive

/-- A fixed spectral peak defines an optimized H³ dissipation floor at ALL
later physical times whose H³ amplitude remains at least HALF the peak.
The floor and sixth-root radius are selected ONCE from the peak amplitude;
there is no assertion of global temporal persistence. -/
theorem h3Path_peakHalfAmplitude_optimizedGlobalFloor244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (s : ℝ) (_hs : s ∈ Set.Ioo b T)
    (hTwo : 2 ≤ ‖h3AuditActualSpectralVelocityTotal hH3 s‖)
    (hLarge : 32 * (velocityH3Energy0At u b + 1) ≤
      ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 2) :
    ∃ H : ℝ, 0 < H ∧
      ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 8 =
        16384 * (velocityH3Energy0At u b + 1) * H ^ 3 ∧
      ∀ r : ℝ, r ∈ Set.Ioo b T →
        ‖h3AuditActualSpectralVelocityTotal hH3 s‖ / 2 ≤
          ‖h3AuditActualSpectralVelocityTotal hH3 r‖ →
        H ≤ velocityH3DissipationAt u r := by
  let A : ℝ := ‖h3AuditActualSpectralVelocityTotal hH3 s‖
  let E : ℝ := velocityH3Energy0At u b
  have hE : 0 ≤ E := velocityH3Energy0At_nonneg u b
  have hHalfLarge : 8 * (E + 1) ≤ (A / 2) ^ 2 := by
    dsimp only [A, E] at hLarge ⊢
    nlinarith only [hLarge]
  obtain ⟨ρ, hρ, hRoot, hThreshold⟩ :=
    h3Path_optimizedSixthRootRadius244 (A / 2) E hE hHalfLarge
  let H : ℝ := (ρ ^ 2 / 8) * A ^ 2
  have hAPos : 0 < A := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hTwo
  have hHPos : 0 < H := by
    dsimp only [H]
    positivity
  have hRoot' : 32 * (E + 1) * ρ ^ 6 = A ^ 2 := by
    nlinarith only [hRoot]
  have hIdentity : A ^ 8 = 16384 * (E + 1) * H ^ 3 := by
    calc
      A ^ 8 = A ^ 2 * A ^ 6 := by ring
      _ = (32 * (E + 1) * ρ ^ 6) * A ^ 6 := by rw [← hRoot']
      _ = 16384 * (E + 1) * H ^ 3 := by dsimp only [H]; ring
  refine ⟨H, hHPos, (by simpa only [A, E] using hIdentity), ?_⟩
  intro r hr hHalf
  have hHalfNonneg : 0 ≤ A / 2 := by dsimp only [A]; positivity
  have hSquare : (A / 2) ^ 2 ≤
      ‖h3AuditActualSpectralVelocityTotal hH3 r‖ ^ 2 :=
    pow_le_pow_left₀ hHalfNonneg hHalf 2
  have hCost := h3Path_physicalPeak_sixthThreshold_forces_dissipation244
    hH3 hClass b hb r hr ρ hρ hE (hThreshold.trans hSquare)
  have hScaled := mul_le_mul_of_nonneg_left hSquare
    (by positivity : 0 ≤ ρ ^ 2 / 2)
  calc
    H = (ρ ^ 2 / 2) * (A / 2) ^ 2 := by dsimp only [H]; ring
    _ ≤ (ρ ^ 2 / 2) *
        ‖h3AuditActualSpectralVelocityTotal hH3 r‖ ^ 2 := hScaled
    _ ≤ velocityH3DissipationAt u r := hCost

/-- If the terminal slack is too long to fit inside the available budget
at optimized height H, the actual spectral path MUST lose more than half
its peak amplitude before that budget-length interval ends. The horizon is
specified independently of any selectable continuity radius. -/
theorem h3Path_optimizedPeak_terminalCompression_or_halfLoss244
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
      let B := ∫ r in a..T, velocityH3DissipationAt u r
      T - s ≤ (B + 1) / H ∨
        ∃ r : ℝ, r ∈ Set.Icc s (s + (B + 1) / H) ∧
          ‖h3AuditActualSpectralVelocityTotal hH3 r‖ <
            ‖h3AuditActualSpectralVelocityTotal hH3 s‖ / 2 := by
  obtain ⟨H, hH, hIdentity, hFloor⟩ :=
    h3Path_peakHalfAmplitude_optimizedGlobalFloor244
      hH3 hClass b hb s hs hTwo hLarge
  let B : ℝ := ∫ r in a..T, velocityH3DissipationAt u r
  let L : ℝ := (B + 1) / H
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact intervalIntegral.integral_nonneg hClass.terminal_start.2.le
      (fun r _ => velocityH3DissipationAt_nonneg u r)
  have hL : 0 < L := by
    dsimp only [L]
    exact div_pos (by linarith only [hB]) hH
  refine ⟨H, hH, hIdentity, ?_⟩
  change T - s ≤ L ∨
    ∃ r : ℝ, r ∈ Set.Icc s (s + L) ∧
      ‖h3AuditActualSpectralVelocityTotal hH3 r‖ <
        ‖h3AuditActualSpectralVelocityTotal hH3 s‖ / 2
  by_cases hShort : T - s ≤ L
  · exact Or.inl hShort
  · right
    have hEnd : s + L < T := by
      have hLt : L < T - s := lt_of_not_ge hShort
      linarith only [hLt]
    have hTooExpensive : B < L * H := by
      have hIdentity' : L * H = B + 1 := by
        dsimp only [L]
        exact div_mul_cancel₀ _ (ne_of_gt hH)
      linarith only [hIdentity']
    obtain ⟨r, hr, hLowD⟩ := h3Path_finiteIntegral_forces_floorFailure244
      (velocityH3DissipationAt u) a T s L H
      hClass.terminal_start.2.le
      (lt_trans hb.1 hs.1).le hL hEnd
      (velocityH3DissipationAt_nonneg u) hDInt
      (by simpa only [B] using hTooExpensive)
    refine ⟨r, hr, ?_⟩
    by_contra hNot
    have hHalf : ‖h3AuditActualSpectralVelocityTotal hH3 s‖ / 2 ≤
        ‖h3AuditActualSpectralVelocityTotal hH3 r‖ :=
      le_of_not_gt hNot
    have hrClass : r ∈ Set.Ioo b T :=
      ⟨lt_of_lt_of_le hs.1 hr.1, lt_of_le_of_lt hr.2 hEnd⟩
    exact (not_lt_of_ge (hFloor r hrClass hHalf)) hLowD

/-- In the compressed-terminal-time branch, the peak's remaining physical
time must satisfy a root-free cubic eighth-power clock. This estimate is
independent of any chosen local persistence interval. -/
theorem h3Path_optimizedPeak_terminalCompression_cube244
    (A E B H T s : ℝ)
    (hE : 0 ≤ E) (hH : 0 < H) (hs : s ≤ T)
    (hIdentity : A ^ 8 = 16384 * (E + 1) * H ^ 3)
    (hCompression : T - s ≤ (B + 1) / H) :
    (T - s) ^ 3 * A ^ 8 ≤
      16384 * (E + 1) * (B + 1) ^ 3 := by
  have hMul : (T - s) * H ≤ B + 1 := by
    calc
      (T - s) * H ≤ ((B + 1) / H) * H :=
        mul_le_mul_of_nonneg_right hCompression hH.le
      _ = B + 1 := div_mul_cancel₀ _ (ne_of_gt hH)
  have hCube := pow_le_pow_left₀ (mul_nonneg (sub_nonneg.mpr hs) hH.le) hMul 3
  have hScaled := mul_le_mul_of_nonneg_left hCube
    (by positivity : 0 ≤ 16384 * (E + 1))
  calc
    (T - s) ^ 3 * A ^ 8 =
        (16384 * (E + 1)) * ((T - s) * H) ^ 3 := by
          rw [hIdentity]
          ring
    _ ≤ 16384 * (E + 1) * (B + 1) ^ 3 := hScaled

/-- End-to-end canonical source-peak terminal-time alternative. Retain the
SAME source-envelope maximizers, the SAME disjoint quadratic-sharp annulus
windows and the unchanged conditional critical-width regime. At every
sufficiently late source peak after any fixed physical kinetic anchor,
either its remaining terminal time is at most the optimized budget scale,
or the genuine H³ spectral norm drops below HALF its source-peak value on
that same explicitly specified scale. No artificially shortened continuity
interval enters the statement. -/
theorem h3Path_noL2Trace_canonicalWidth_sourcePeakForcedHalfAmplitude244
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
              ∃ r : ℝ,
                r ∈ Set.Icc (s k) (s k + (Budget + 1) / H) ∧
                ‖h3AuditActualSpectralVelocityTotal hH3 r‖ <
                  ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ / 2) := by
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
  exact h3Path_optimizedPeak_terminalCompression_or_halfLoss244
    hH3 hClass hDInt b hb (s k) ht hTwo hLarge

end
end PrimeTensor.FirstMonomialTriad
