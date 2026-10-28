import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalPeakRiccatiClockBarrier244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalCriticalWidthJointH3State244
import Mathlib.Tactic

/-!
# Eliminate noncompressed half-loss for sufficiently large canonical H³ peaks

The established physical Riccati/Landau argument yields, on the half-loss arm,

    A^8 < 16384 (E₀(b)+1) M(A)^3,

where M(A) is the maximum of two affine-in-A positive clock ceilings.
For A>=2, M(A)<=Q*A, where Q is independent of A and depends only on
fixed viscosity budget, first-gradient coefficient and Riccati coefficient.
Thus the alternative entails A^5 < 16384 (E₀(b)+1) Q^3; in particular
A < 16384 (E₀(b)+1) Q^3.

For the original critical-width canonical source-maximizing sequence,
the existing joint H³ spectral escape makes A tend to infinity. Hence
sufficiently late source peaks must satisfy the terminal-compression arm
of the original optimized clock. This is a conditional branch elimination,
NOT a proof of smooth continuation: terminal compression remains possible.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Linear coefficient of the two physical Riccati/Landau clock ceilings,
independent of the escaping canonical spectral amplitude. -/
noncomputable def h3PathCanonicalPeakLinearClockCoefficient244
    (B C K : ℝ) : ℝ :=
  max (128 * (B + 1) * 4422 * (1 + 4 * C))
      (2 * K * (B + 1))

/-- For A>=2, the exact maximum clock envelope is bounded by Q*A. -/
theorem h3Path_canonicalLinearClockEnvelope_le_coefficient_mul_amplitude244
    (A B C K : ℝ)
    (hA : 2 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    max (128 * (B + 1) * 4422 * (1 + 4 * C * A))
        (2 * K * (B + 1) * A) ≤
      h3PathCanonicalPeakLinearClockCoefficient244 B C K * A := by
  let Q : ℝ := h3PathCanonicalPeakLinearClockCoefficient244 B C K
  have hANonneg : 0 ≤ A := by linarith only [hA]
  have hScaledOne : 1 + 4 * C * A ≤ (1 + 4 * C) * A := by
    nlinarith only [hA]
  have hFactor : 0 ≤ 128 * (B + 1) * 4422 := by positivity
  have hFirst :
      128 * (B + 1) * 4422 * (1 + 4 * C * A) ≤
        (128 * (B + 1) * 4422 * (1 + 4 * C)) * A := by
    calc
      _ ≤ (128 * (B + 1) * 4422) * ((1 + 4 * C) * A) :=
        mul_le_mul_of_nonneg_left hScaledOne hFactor
      _ = _ := by ring
  have hFirstQ :
      (128 * (B + 1) * 4422 * (1 + 4 * C)) * A ≤ Q * A := by
    apply mul_le_mul_of_nonneg_right _ hANonneg
    exact le_max_left _ _
  have hSecondQ :
      (2 * K * (B + 1)) * A ≤ Q * A := by
    apply mul_le_mul_of_nonneg_right _ hANonneg
    exact le_max_right _ _
  change max (128 * (B + 1) * 4422 * (1 + 4 * C * A))
      (2 * K * (B + 1) * A) ≤ Q * A
  apply max_le
  · exact le_trans hFirst hFirstQ
  · calc
      2 * K * (B + 1) * A = (2 * K * (B + 1)) * A := by ring
      _ ≤ Q * A := hSecondQ

/-- The noncompressed eighth-power clock barrier puts a FINITE ceiling on
its initial spectral amplitude. No terminal bound is assumed. -/
theorem h3Path_canonicalEighthPowerBarrier_amplitudeCeiling244
    (A E B C K : ℝ)
    (hA : 2 ≤ A) (hE : 0 ≤ E) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hBarrier : A ^ 8 < 16384 * (E + 1) *
      (max (128 * (B + 1) * 4422 * (1 + 4 * C * A))
           (2 * K * (B + 1) * A)) ^ 3) :
    A < 16384 * (E + 1) *
      (h3PathCanonicalPeakLinearClockCoefficient244 B C K) ^ 3 := by
  let Q : ℝ := h3PathCanonicalPeakLinearClockCoefficient244 B C K
  let M : ℝ := max (128 * (B + 1) * 4422 * (1 + 4 * C * A))
    (2 * K * (B + 1) * A)
  let P : ℝ := 16384 * (E + 1)
  have hANonneg : 0 ≤ A := by linarith only [hA]
  have hOne : (1 : ℝ) ≤ A := by linarith only [hA]
  have hMNonneg : 0 ≤ M := by
    dsimp only [M]
    apply le_max_of_le_left
    positivity
  have hMUpper : M ≤ Q * A := by
    exact h3Path_canonicalLinearClockEnvelope_le_coefficient_mul_amplitude244
      A B C K hA hB hC
  have hCube : M ^ 3 ≤ (Q * A) ^ 3 :=
    pow_le_pow_left₀ hMNonneg hMUpper 3
  have hPNonneg : 0 ≤ P := by
    dsimp only [P]
    positivity
  have hScaled : P * M ^ 3 ≤ P * (Q * A) ^ 3 :=
    mul_le_mul_of_nonneg_left hCube hPNonneg
  have hPoly : A ^ 8 < (P * Q ^ 3) * A ^ 3 := by
    calc
      A ^ 8 < P * M ^ 3 := hBarrier
      _ ≤ P * (Q * A) ^ 3 := hScaled
      _ = (P * Q ^ 3) * A ^ 3 := by ring
  have hA3Nonneg : 0 ≤ A ^ 3 := pow_nonneg hANonneg _
  have hFifth : A ^ 5 < P * Q ^ 3 := by
    by_contra hNot
    have hReverse : P * Q ^ 3 ≤ A ^ 5 := le_of_not_gt hNot
    have hMultiply := mul_le_mul_of_nonneg_right hReverse hA3Nonneg
    have hContradiction : (P * Q ^ 3) * A ^ 3 ≤ A ^ 8 := by
      calc
        _ ≤ A ^ 5 * A ^ 3 := hMultiply
        _ = A ^ 8 := by ring
    exact (not_lt_of_ge hContradiction) hPoly
  have hPowFourRaw : (1 : ℝ) ^ 4 ≤ A ^ 4 :=
    pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hOne 4
  have hPowFour : (1 : ℝ) ≤ A ^ 4 := by
    simpa only [one_pow] using hPowFourRaw
  have hA_le_A5 : A ≤ A ^ 5 := by
    calc
      A = A * 1 := by ring
      _ ≤ A * A ^ 4 := mul_le_mul_of_nonneg_left hPowFour hANonneg
      _ = A ^ 5 := by ring
  change A < P * Q ^ 3
  exact lt_of_le_of_lt hA_le_A5 hFifth

/-- An amplitude at or above the explicitly fixed coefficient ceiling
cannot inhabit the noncompressed half-loss branch. -/
theorem h3Path_optimizedPeak_forces_terminalCompression_above_ceiling244
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
      ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 2)
    (hBeyond :
      16384 * (velocityH3Energy0At u b + 1) *
        (h3PathCanonicalPeakLinearClockCoefficient244
          (∫ t in a..T, velocityH3DissipationAt u t)
          h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
          h3PathSqrtEnergyRiccatiCoefficient) ^ 3 ≤
        ‖h3AuditActualSpectralVelocityTotal hH3 s‖) :
    ∃ H : ℝ, 0 < H ∧
      ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 8 =
        16384 * (velocityH3Energy0At u b + 1) * H ^ 3 ∧
      T - s ≤ ((∫ t in a..T, velocityH3DissipationAt u t) + 1) / H := by
  obtain ⟨H, hH, hIdentity, hAlt⟩ :=
    h3Path_optimizedPeak_terminalCompression_or_linearRiccatiClock244
      hH3 hClass hDInt b hb s hs hTwo hLarge hThreshold
  refine ⟨H, hH, hIdentity, ?_⟩
  dsimp at hAlt
  rcases hAlt with hCompressed | ⟨r, q, hr, hq, hHalf, hSpike, hSlow, hPoly⟩
  · exact hCompressed
  · have hB : 0 ≤ (∫ t in a..T, velocityH3DissipationAt u t) :=
      intervalIntegral.integral_nonneg hClass.terminal_start.2.le
        (fun t _ => velocityH3DissipationAt_nonneg u t)
    have hImpossible := h3Path_canonicalEighthPowerBarrier_amplitudeCeiling244
      ‖h3AuditActualSpectralVelocityTotal hH3 s‖
      (velocityH3Energy0At u b)
      (∫ t in a..T, velocityH3DissipationAt u t)
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
      h3PathSqrtEnergyRiccatiCoefficient
      hTwo (velocityH3Energy0At_nonneg u b) hB
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
      hPoly
    exact False.elim ((not_lt_of_ge hBeyond) hImpossible)

/-- Under the UNCHANGED conditional critical-width tests, canonical
source-maximizing peaks of an escaping physical H³ state eventually admit
only terminal compression. All annulus and disjoint-window witnesses remain
exactly those of the prior construction; they are not reselected. -/
theorem h3Path_noL2Trace_canonicalWidth_sourcePeakEventuallyCompressed244
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
            T - s k ≤
              ((∫ t in a..T, velocityH3DissipationAt u t) + 1) / H) := by
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
  let Q : ℝ := h3PathCanonicalPeakLinearClockCoefficient244 Budget
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
    h3PathSqrtEnergyRiccatiCoefficient
  let Limit : ℝ := 16384 * (velocityH3Energy0At u b + 1) * Q ^ 3
  let Size : ℝ := max (max (32 * (velocityH3Energy0At u b + 1))
    (16 * Budget)) (max 2 Limit)
  have hLargeEventually : ∀ᶠ k : ℕ in atTop,
      Size ≤ ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ :=
    hPeakEscape.eventually (eventually_ge_atTop Size)
  filter_upwards [hsEventually, hLargeEventually] with k ht hk
  let A : ℝ := ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖
  have hTwo : 2 ≤ A :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hk)
  have hBoundPrior : max (32 * (velocityH3Energy0At u b + 1))
      (16 * Budget) ≤ A :=
    (le_max_left _ _).trans hk
  have hLargeBound : 32 * (velocityH3Energy0At u b + 1) ≤ A :=
    (le_max_left _ _).trans hBoundPrior
  have hViscousBound : 16 * Budget ≤ A :=
    (le_max_right _ _).trans hBoundPrior
  have hBeyond : Limit ≤ A :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hk)
  have hSq : A ≤ A ^ 2 := by
    have hMul : 0 ≤ A * (A - 1) :=
      mul_nonneg (by dsimp only [A]; exact norm_nonneg _)
        (by linarith only [hTwo])
    nlinarith only [hMul]
  have hLarge : 32 * (velocityH3Energy0At u b + 1) ≤ A ^ 2 :=
    le_trans hLargeBound hSq
  have hThreshold : 16 * Budget ≤ A ^ 2 :=
    le_trans hViscousBound hSq
  exact h3Path_optimizedPeak_forces_terminalCompression_above_ceiling244
    hH3 hClass hDInt b hb (s k) ht hTwo hLarge
    (by simpa only [Budget, A] using hThreshold)
    (by simpa only [Budget, Q, Limit, A] using hBeyond)

end
end PrimeTensor.FirstMonomialTriad
