import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalPeakEventuallyCompressed244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Riccati.Lower.Bound
import Mathlib.Tactic

/-!
# Terminal compression versus intrinsic Riccati growth: conditional closure

Let A be the three-component spectral sup norm at the unchanged canonical
projected-source maximum s, and B the fixed finite total physical H³
viscous budget. Previous work proves that all sufficiently large canonical
peaks, under explicit conditional critical-width tests, are compressed:

  A^8 = 16384*(E₀(b)+1)*H^3,    T-s <= (B+1)/H.

Assuming no smooth continuation, the *previously proved* intrinsic Riccati
necessity gives
  2 <= K*(T-s)*sqrt(E₃(s)),    K = 4422*(C₁+1).

The exact physical spectral energy and the three-component product sup
comparison give E₃(s) <= 1+3*A² <= 4*A², for A>=2. Therefore compression
forces H <= K*(B+1)*A. The eighth-power clock identity then yields the
fixed, amplitude-independent ceiling
  A <= 16384*(E₀(b)+1)*(K*(B+1))^3.

The same canonical peak sequence has A -> +infinity if the unchanged
critical-width tests hold. Hence *under those tests* nonextension is
impossible. Neither the critical-width tests nor a universal Navier--Stokes
continuation theorem are established by this module.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- A terminal inverse-root Riccati floor and a compressed optimized clock
bound the physical peak clock linearly in the starting spectral amplitude. -/
theorem h3Path_scalar_compression_riccati_forces_linearClock244
    (A B H K E d : ℝ)
    (hA : 2 ≤ A) (hB : 0 ≤ B) (hH : 0 < H) (hK : 0 ≤ K)
    (hE : 0 ≤ E) (hd : 0 ≤ d)
    (hEnergy : E ≤ 4 * A ^ 2)
    (hRiccati : 2 ≤ K * d * Real.sqrt E)
    (hCompression : d ≤ (B + 1) / H) :
    H ≤ K * (B + 1) * A := by
  have hRoot : Real.sqrt E ≤ 2 * A := by
    have hSq := Real.sq_sqrt hE
    have hNN := Real.sqrt_nonneg E
    nlinarith only [hSq, hNN, hEnergy, hA]
  have hRateNonneg : 0 ≤ K * d := mul_nonneg hK hd
  have hRateRoot := mul_le_mul_of_nonneg_left hRoot hRateNonneg
  have hOne : 1 ≤ K * d * A := by
    nlinarith only [hRateRoot, hRiccati]
  have hWidth : d * H ≤ B + 1 := by
    calc
      d * H ≤ ((B + 1) / H) * H :=
        mul_le_mul_of_nonneg_right hCompression hH.le
      _ = B + 1 := div_mul_cancel₀ _ (ne_of_gt hH)
  have hAPos : 0 ≤ A := le_trans (by norm_num : (0 : ℝ) ≤ 2) hA
  have hScaled := mul_le_mul_of_nonneg_left hWidth (mul_nonneg hK hAPos)
  have hOneScaled := mul_le_mul_of_nonneg_right hOne hH.le
  calc
    H = 1 * H := by ring
    _ ≤ (K * d * A) * H := hOneScaled
    _ = (K * A) * (d * H) := by ring
    _ ≤ (K * A) * (B + 1) := hScaled
    _ = K * (B + 1) * A := by ring

/-- Exact eighth-power source peak identity converts any linear clock bound
into a fixed amplitude ceiling. This lemma does not assume nonextension. -/
theorem h3Path_scalar_peakHeight_linearClock_amplitudeCeiling244
    (A E H L : ℝ)
    (hA : 2 ≤ A) (hE : 0 ≤ E) (hH : 0 < H) (hL : 0 ≤ L)
    (hIdentity : A ^ 8 = 16384 * (E + 1) * H ^ 3)
    (hClock : H ≤ L * A) :
    A ≤ 16384 * (E + 1) * L ^ 3 := by
  let P : ℝ := 16384 * (E + 1)
  have hAOne : 1 ≤ A := by linarith only [hA]
  have hANonneg : 0 ≤ A := by linarith only [hA]
  have hAPos : 0 < A := by linarith only [hA]
  have hPNonneg : 0 ≤ P := by
    dsimp only [P]
    positivity
  have hHcube : H ^ 3 ≤ (L * A) ^ 3 :=
    pow_le_pow_left₀ hH.le hClock 3
  have hScaled : P * H ^ 3 ≤ P * (L * A) ^ 3 :=
    mul_le_mul_of_nonneg_left hHcube hPNonneg
  have hPoly : A ^ 8 ≤ (P * L ^ 3) * A ^ 3 := by
    calc
      A ^ 8 = P * H ^ 3 := hIdentity
      _ ≤ P * (L * A) ^ 3 := hScaled
      _ = (P * L ^ 3) * A ^ 3 := by ring
  have hA3pos : 0 < A ^ 3 := pow_pos hAPos _
  have hFifth : A ^ 5 ≤ P * L ^ 3 := by
    by_contra hNot
    have hReverse : P * L ^ 3 < A ^ 5 := lt_of_not_ge hNot
    have hMultiply := mul_lt_mul_of_pos_right hReverse hA3pos
    have hConflict : (P * L ^ 3) * A ^ 3 < A ^ 8 := by
      calc
        _ < A ^ 5 * A ^ 3 := hMultiply
        _ = A ^ 8 := by ring
    exact (not_lt_of_ge hPoly) hConflict
  have hPowFourRaw : (1 : ℝ) ^ 4 ≤ A ^ 4 :=
    pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hAOne 4
  have hPowFour : (1 : ℝ) ≤ A ^ 4 := by
    simpa only [one_pow] using hPowFourRaw
  have hA_le_A5 : A ≤ A ^ 5 := by
    calc
      A = A * 1 := by ring
      _ ≤ A * A ^ 4 := mul_le_mul_of_nonneg_left hPowFour hANonneg
      _ = A ^ 5 := by ring
  change A ≤ P * L ^ 3
  exact le_trans hA_le_A5 hFifth

/-- If an actual compressed canonical peak exceeds the physical Riccati
amplitude ceiling, the preterminal solution must admit a smooth extension.
Nonextension is refuted using the intrinsic inverse-square-root floor; no
new source peak or time interval is chosen. -/
theorem h3Path_compressedPeak_above_riccatiCeiling_forces_extension244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (s H B : ℝ) (hs : s ∈ Set.Ioo b T)
    (hTwo : 2 ≤ ‖h3AuditActualSpectralVelocityTotal hH3 s‖)
    (hB : 0 ≤ B) (hH : 0 < H)
    (hIdentity : ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 8 =
      16384 * (velocityH3Energy0At u b + 1) * H ^ 3)
    (hCompression : T - s ≤ (B + 1) / H)
    (hBeyond : 16384 * (velocityH3Energy0At u b + 1) *
      (h3PathSqrtEnergyRiccatiCoefficient * (B + 1)) ^ 3 <
        ‖h3AuditActualSpectralVelocityTotal hH3 s‖) :
    ∃ w : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u w T := by
  by_contra hNoExtension
  let A : ℝ := ‖h3AuditActualSpectralVelocityTotal hH3 s‖
  let K : ℝ := h3PathSqrtEnergyRiccatiCoefficient
  let E : ℝ := velocityH3EnergyAt u s
  have hsClass : s ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hs.1, hs.2⟩
  have hsAbs : s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 hsClass.1, hsClass.2⟩
  have hExact := h3AuditActualSpectralVelocityTotal_energy_exact hH3 s hsAbs
  have hSup := h3Path_spectralSquareEnergy_le_threeSupSquare244
    (h3AuditActualSpectralVelocityTotal hH3 s)
  have hOne : 1 ≤ A ^ 2 := by
    nlinarith only [hTwo, sq_nonneg (A - 1)]
  have hEnergy : E ≤ 4 * A ^ 2 := by
    dsimp only [E, A]
    linarith only [hExact, hSup, hOne]
  have hE : 0 ≤ E :=
    le_trans zero_le_one (one_le_velocityH3EnergyAt u s)
  have hRiccati : 2 ≤ K * (T - s) * Real.sqrt E :=
    two_le_riccatiCoefficient_mul_terminalDistance_mul_sqrtEnergy_of_noH3PathExtension
      hH3 hNoExtension hClass hsClass
  have hK : 0 ≤ K := h3PathSqrtEnergyRiccatiCoefficient_nonneg
  have hSlow : H ≤ K * (B + 1) * A :=
    h3Path_scalar_compression_riccati_forces_linearClock244
      A B H K E (T - s) hTwo hB hH hK hE
      (sub_nonneg.mpr hsClass.2.le) hEnergy hRiccati hCompression
  have hL : 0 ≤ K * (B + 1) :=
    mul_nonneg hK (by linarith only [hB] : 0 ≤ B + 1)
  have hCeiling := h3Path_scalar_peakHeight_linearClock_amplitudeCeiling244
    A (velocityH3Energy0At u b) H (K * (B + 1))
    hTwo (velocityH3Energy0At_nonneg u b) hH hL hIdentity hSlow
  have hLarge : 16384 * (velocityH3Energy0At u b + 1) *
      (K * (B + 1)) ^ 3 < A := by
    simpa only [A, K] using hBeyond
  exact (not_lt_of_ge hCeiling) hLarge

/-- Under the original conditional critical ninth/eighth annulus regime,
no-trace canonical projected-source maximizers escape in H³. The preceding
terminal-compression theorem and intrinsic Riccati necessity then force
smooth continuation. The original disjoint windows, source maxima, and
finite-annulus witnesses are retained. This is a CONDITIONAL criterion; the
critical-width regime is an explicit hypothesis. -/
theorem h3Path_noL2Trace_canonicalWidth_criticalRegime_forces_extension244
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
        ∃ w : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
          SmoothContinuationExtension u w T) := by
  obtain ⟨τ, N, K, C, δ, v, s, hv, hCofinal, hTime,
      hSeparate, hSummable, hCanonical, hPeak, hJoint⟩ :=
    h3Path_noL2Trace_finiteDissipation_canonicalWidth_fixedMaximizerJointEscape244
      hH3 hClass hTerminalMass hNoTrace hDInt
  refine ⟨τ, N, K, C, δ, v, s, hv, hCofinal, hTime,
    hSeparate, hSummable, hCanonical, hPeak, ?_⟩
  intro η U V hη hU hV hRegime
  by_contra hNoExtension
  have hJointEscape := (hJoint η U V hη hU hV hRegime).2
  let b : ℝ := (a + T) / 2
  have hb : b ∈ Set.Ioo a T := by
    dsimp only [b]
    have haT := hClass.terminal_start.2
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
  let Budget : ℝ := ∫ t in a..T, velocityH3DissipationAt u t
  let Q : ℝ := h3PathCanonicalPeakLinearClockCoefficient244 Budget
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
    h3PathSqrtEnergyRiccatiCoefficient
  let OldLimit : ℝ := 16384 * (velocityH3Energy0At u b + 1) * Q ^ 3
  let NewLimit : ℝ := 16384 * (velocityH3Energy0At u b + 1) *
    (h3PathSqrtEnergyRiccatiCoefficient * (Budget + 1)) ^ 3
  let Size : ℝ := max
    (max (32 * (velocityH3Energy0At u b + 1)) (16 * Budget))
    (max 2 (max OldLimit (NewLimit + 1)))
  have hLargeEventually : ∀ᶠ k : ℕ in atTop,
      Size ≤ ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ :=
    hJointEscape.eventually (eventually_ge_atTop Size)
  obtain ⟨k, ht, hk⟩ := (hsEventually.and hLargeEventually).exists
  let A : ℝ := ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖
  have hRight : max 2 (max OldLimit (NewLimit + 1)) ≤ A :=
    (le_max_right _ _).trans hk
  have hTwo : 2 ≤ A := (le_max_left _ _).trans hRight
  have hLimits : max OldLimit (NewLimit + 1) ≤ A :=
    (le_max_right _ _).trans hRight
  have hOld : OldLimit ≤ A := (le_max_left _ _).trans hLimits
  have hNew : NewLimit + 1 ≤ A := (le_max_right _ _).trans hLimits
  have hPrior : max (32 * (velocityH3Energy0At u b + 1))
      (16 * Budget) ≤ A := (le_max_left _ _).trans hk
  have hLargeBound : 32 * (velocityH3Energy0At u b + 1) ≤ A :=
    (le_max_left _ _).trans hPrior
  have hViscousBound : 16 * Budget ≤ A :=
    (le_max_right _ _).trans hPrior
  have hSq : A ≤ A ^ 2 := by
    have hMul : 0 ≤ A * (A - 1) :=
      mul_nonneg (by dsimp only [A]; exact norm_nonneg _)
        (by linarith only [hTwo])
    nlinarith only [hMul]
  have hLarge : 32 * (velocityH3Energy0At u b + 1) ≤ A ^ 2 :=
    le_trans hLargeBound hSq
  have hThreshold : 16 * Budget ≤ A ^ 2 :=
    le_trans hViscousBound hSq
  have hB : 0 ≤ Budget := by
    dsimp only [Budget]
    exact intervalIntegral.integral_nonneg hClass.terminal_start.2.le
      (fun t _ => velocityH3DissipationAt_nonneg u t)
  obtain ⟨H, hH, hIdentity, hCompression⟩ :=
    h3Path_optimizedPeak_forces_terminalCompression_above_ceiling244
      hH3 hClass hDInt b hb (s k) ht hTwo hLarge
      (by simpa only [Budget, A] using hThreshold)
      (by simpa only [Budget, Q, OldLimit, A] using hOld)
  have hBeyond : 16384 * (velocityH3Energy0At u b + 1) *
      (h3PathSqrtEnergyRiccatiCoefficient * (Budget + 1)) ^ 3 < A := by
    dsimp only [NewLimit] at hNew
    linarith only [hNew]
  have hExtension :=
    h3Path_compressedPeak_above_riccatiCeiling_forces_extension244
      hH3 hClass b hb (s k) H Budget ht hTwo hB hH hIdentity
      (by simpa only [Budget, A] using hCompression)
      (by simpa only [A] using hBeyond)
  exact hNoExtension hExtension

end
end PrimeTensor.FirstMonomialTriad
