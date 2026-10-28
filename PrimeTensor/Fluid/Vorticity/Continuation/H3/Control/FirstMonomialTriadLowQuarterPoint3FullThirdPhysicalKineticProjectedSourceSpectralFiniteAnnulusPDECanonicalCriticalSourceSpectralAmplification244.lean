import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalCriticalRegimeFailure244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalCriticalWidthPhysicalSource244
import Mathlib.Tactic

/-!
# Critical outer-width cap forces physical source–spectral amplification

The actual finite-annulus PDE coefficient is
  Λ(R,Q,K,C) = 6 K C [(Q+1)^2 sqrt(3 W(Q)) + (R+1)^2 sqrt(3 W(R))]
where W(x) = 1+x²+x⁴+x⁶. Its *nonnegative* polynomial ceiling is
  Λ <= 48 |K C| (Q+1)^5       (1 <= R <= Q).
An outer annular cap (Q+1)^8 <= D R^9 and a sixth-order linear-rate
escape U R^6 < Λ imply the sharp root-free consequence
  U^8 R^3 < (48 |K C|)^8 D^5.

The final theorem transfers this restriction to the original minimal
canonical annuli and source-maximizing times under hypothetical
nonextension, geometric noncompression and a fixed critical-width cap.
The six-order linear rate must then grow through the *actual* product of
starting Fourier H3 amplitude and attained physical projected-source norm.
No source bound, uniform cutoff cap, or continuation is asserted.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- The exact radial H³ weight has a degree-five PDE multiplier ceiling.
The constants are algebraic, using only the nonnegative physical cutoff. -/
theorem h3Path_radialPDEMultiplier_le_fourFifth244
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    Real.sqrt (3 * h3TerminalRadialSobolevWeightSquareCeiling ρ) ≤
      4 * (ρ + 1) ^ 3 := by
  have hWeight : 0 ≤ 3 * h3TerminalRadialSobolevWeightSquareCeiling ρ := by
    unfold h3TerminalRadialSobolevWeightSquareCeiling
    positivity
  have hPolyPos : 0 ≤
      13 + 96 * ρ + 237 * ρ ^ 2 + 320 * ρ ^ 3 +
        237 * ρ ^ 4 + 96 * ρ ^ 5 + 13 * ρ ^ 6 := by
    positivity
  have hPolynomial :
      3 * h3TerminalRadialSobolevWeightSquareCeiling ρ ≤
        (4 * (ρ + 1) ^ 3) ^ 2 := by
    unfold h3TerminalRadialSobolevWeightSquareCeiling
    nlinarith only [hPolyPos]
  have hRootSq := Real.sq_sqrt hWeight
  have hRootNonneg := Real.sqrt_nonneg
    (3 * h3TerminalRadialSobolevWeightSquareCeiling ρ)
  have hUpperNonneg : 0 ≤ 4 * (ρ + 1) ^ 3 := by positivity
  nlinarith only [hPolynomial, hRootSq, hRootNonneg, hUpperNonneg]

/-- The *actual* PDE variation coefficient cannot grow faster than the
fifth power of the outer radius times the physical source–state product. -/
theorem h3Path_finiteAnnulusPDEVariation_le_sourceSpectralFifth244
    (R Q K C : ℝ) (hR : 0 ≤ R) (hRQ : R ≤ Q) :
    h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C ≤
      48 * |K * C| * (Q + 1) ^ 5 := by
  have hQ : 0 ≤ Q := le_trans hR hRQ
  have hRRoot := h3Path_radialPDEMultiplier_le_fourFifth244 R hR
  have hQRoot := h3Path_radialPDEMultiplier_le_fourFifth244 Q hQ
  have hRTerm :
      (R + 1) ^ 2 *
          Real.sqrt (3 * h3TerminalRadialSobolevWeightSquareCeiling R) ≤
        4 * (R + 1) ^ 5 := by
    calc
      _ ≤ (R + 1) ^ 2 * (4 * (R + 1) ^ 3) :=
        mul_le_mul_of_nonneg_left hRRoot (by positivity)
      _ = 4 * (R + 1) ^ 5 := by ring
  have hQTerm :
      (Q + 1) ^ 2 *
          Real.sqrt (3 * h3TerminalRadialSobolevWeightSquareCeiling Q) ≤
        4 * (Q + 1) ^ 5 := by
    calc
      _ ≤ (Q + 1) ^ 2 * (4 * (Q + 1) ^ 3) :=
        mul_le_mul_of_nonneg_left hQRoot (by positivity)
      _ = 4 * (Q + 1) ^ 5 := by ring
  have hPow : (R + 1) ^ 5 ≤ (Q + 1) ^ 5 :=
    pow_le_pow_left₀ (by positivity : 0 ≤ R + 1)
      (by linarith only [hRQ]) 5
  have hSum :
      (Q + 1) ^ 2 *
          Real.sqrt (3 * h3TerminalRadialSobolevWeightSquareCeiling Q) +
        (R + 1) ^ 2 *
          Real.sqrt (3 * h3TerminalRadialSobolevWeightSquareCeiling R) ≤
        8 * (Q + 1) ^ 5 := by
    linarith only [hQTerm, hRTerm, hPow]
  have hSumNonneg : 0 ≤
      (Q + 1) ^ 2 *
          Real.sqrt (3 * h3TerminalRadialSobolevWeightSquareCeiling Q) +
        (R + 1) ^ 2 *
          Real.sqrt (3 * h3TerminalRadialSobolevWeightSquareCeiling R) := by
    positivity
  have hK : 6 * (K * C) ≤ 6 * |K * C| :=
    mul_le_mul_of_nonneg_left (le_abs_self (K * C)) (by norm_num)
  calc
    h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C =
        (6 * (K * C)) *
          ((Q + 1) ^ 2 *
              Real.sqrt (3 * h3TerminalRadialSobolevWeightSquareCeiling Q) +
            (R + 1) ^ 2 *
              Real.sqrt (3 * h3TerminalRadialSobolevWeightSquareCeiling R)) := by
          unfold h3PathFiniteAnnulusPDEVariationCoefficient244
          ring
    _ ≤ (6 * |K * C|) *
          ((Q + 1) ^ 2 *
              Real.sqrt (3 * h3TerminalRadialSobolevWeightSquareCeiling Q) +
            (R + 1) ^ 2 *
              Real.sqrt (3 * h3TerminalRadialSobolevWeightSquareCeiling R)) :=
        mul_le_mul_of_nonneg_right hK hSumNonneg
    _ ≤ (6 * |K * C|) * (8 * (Q + 1) ^ 5) :=
        mul_le_mul_of_nonneg_left hSum (by positivity)
    _ = 48 * |K * C| * (Q + 1) ^ 5 := by ring

/-- Sharp root-free radial exponent: linear rate / R^6 escaping under an
outer ninth/eighth cap forces the actual KC product at scale R^(3/8). -/
theorem h3Path_scalarCriticalWidth_linearEscape_sourceSpectral244
    (R Q U D K C : ℝ)
    (hR : 1 ≤ R) (hQ : R ≤ Q)
    (hU : 0 ≤ U) (hD : 0 ≤ D)
    (hWidth : (Q + 1) ^ 8 ≤ D * R ^ 9)
    (hRate : U * R ^ 6 <
      h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C) :
    U ^ 8 * R ^ 3 < (48 * |K * C|) ^ 8 * D ^ 5 := by
  let S : ℝ := 48 * |K * C|
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hR0 : 0 ≤ R := le_trans (by norm_num) hR
  have hQ0 : 0 ≤ Q := le_trans hR0 hQ
  have hUpper := h3Path_finiteAnnulusPDEVariation_le_sourceSpectralFifth244
    R Q K C hR0 hQ
  have hRate' : U * R ^ 6 < S * (Q + 1) ^ 5 :=
    lt_of_lt_of_le hRate (by simpa only [S] using hUpper)
  have hLowerNonneg : 0 ≤ U * R ^ 6 := by positivity
  have hRatePow : (U * R ^ 6) ^ 8 < (S * (Q + 1) ^ 5) ^ 8 :=
    pow_lt_pow_left₀ hRate' hLowerNonneg (by norm_num : 8 ≠ 0)
  have hWidthPow : ((Q + 1) ^ 8) ^ 5 ≤ (D * R ^ 9) ^ 5 :=
    pow_le_pow_left₀ (by positivity : 0 ≤ (Q + 1) ^ 8) hWidth 5
  have hRateUpper : (S * (Q + 1) ^ 5) ^ 8 ≤
      S ^ 8 * (D * R ^ 9) ^ 5 := by
    calc
      _ = S ^ 8 * ((Q + 1) ^ 8) ^ 5 := by ring
      _ ≤ S ^ 8 * (D * R ^ 9) ^ 5 :=
        mul_le_mul_of_nonneg_left hWidthPow (by positivity)
  have hCombined : (U ^ 8 * R ^ 3) * R ^ 45 <
      (S ^ 8 * D ^ 5) * R ^ 45 := by
    calc
      _ = (U * R ^ 6) ^ 8 := by ring
      _ < (S * (Q + 1) ^ 5) ^ 8 := hRatePow
      _ ≤ S ^ 8 * (D * R ^ 9) ^ 5 := hRateUpper
      _ = _ := by ring
  have hR45 : 0 ≤ R ^ 45 := by positivity
  have hResult : U ^ 8 * R ^ 3 < S ^ 8 * D ^ 5 := by
    by_contra hNot
    have hReverse : S ^ 8 * D ^ 5 ≤ U ^ 8 * R ^ 3 :=
      le_of_not_gt hNot
    have hProduct := mul_le_mul_of_nonneg_right hReverse hR45
    exact (not_lt_of_ge hProduct) hCombined
  simpa only [S] using hResult

/-- Same original disjoint annuli and source-maximizer times. If the
geometric arm is noncompressed and the canonical ninth/eighth width has a
fixed cap, hypothetical nonextension forces arbitrarily late physical
source–spectral amplification at the sharp exponent 3/8. The selected
K(v k) is the original anchor Fourier H3 norm coefficient, and C(v k) is
the attained source maximum, never an artificially enlarged ceiling. -/
theorem h3Path_noExtension_canonicalWidth_forces_sourceSpectralAmplification244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hTerminalMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (hNoExtension : ¬ ∃ w : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u w T) :
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
      (∀ η V : ℝ, 0 < η → 0 ≤ V →
        (∀ᶠ k : ℕ in atTop,
          η ≤ ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2)) →
        (∀ᶠ k : ℕ in atTop,
          (((N (v k) - v k : ℕ) : ℝ) + 1) ^ 8 ≤
            V * (((v k : ℝ) + 1) ^ 9)) →
        ∀ U : ℝ, 0 ≤ U → ∀ n : ℕ, ∃ k : ℕ, n ≤ k ∧
          U ^ 8 * (((v k : ℝ) + 1) ^ 3) <
            (48 * |K (v k) * C (v k)|) ^ 8 *
              (256 * (V + 1)) ^ 5) := by
  obtain ⟨τ, N, K, C, δ, v, s, hv, hCofinal, hTime,
      hSeparate, hSummable, hCanonical, hPeak, _hThree, _hWidthEscape,
      hLinearEscape⟩ :=
    h3Path_noL2Trace_noExtension_canonicalCriticalRegimeCofinalFailure244
      hH3 hClass hTerminalMass hNoTrace hDInt hNoExtension
  refine ⟨τ, N, K, C, δ, v, s, hv, hCofinal, hTime,
    hSeparate, hSummable, hCanonical, hPeak, ?_⟩
  intro η V hη hV hGeom hWidth U hU n
  have hUplus : 0 ≤ U + 1 := by linarith only [hU]
  obtain ⟨nW, hnW⟩ := Filter.eventually_atTop.1 hWidth
  obtain ⟨k, hkn, hEsc⟩ :=
    hLinearEscape η V hη hV hGeom hWidth (U + 1) hUplus (max n nW)
  have hn : n ≤ k := (le_max_left _ _).trans hkn
  have hkW : (((N (v k) - v k : ℕ) : ℝ) + 1) ^ 8 ≤
      V * (((v k : ℝ) + 1) ^ 9) :=
    hnW k ((le_max_right _ _).trans hkn)
  let R : ℝ := (v k : ℝ) + 1
  let Q : ℝ := (N (v k) : ℝ) + 1
  let L : ℝ := ((N (v k) - v k : ℕ) : ℝ)
  have hR : 1 ≤ R := by
    dsimp only [R]
    have hNat : (0 : ℝ) ≤ (v k : ℝ) := Nat.cast_nonneg _
    linarith only [hNat]
  have hL : 0 ≤ L := by dsimp only [L]; exact Nat.cast_nonneg _
  have hN : v k ≤ N (v k) := (hCanonical k).1
  have hRQ : R ≤ Q := by
    have hCast : (v k : ℝ) ≤ (N (v k) : ℝ) := by exact_mod_cast hN
    dsimp only [R, Q]
    linarith only [hCast]
  have hOuterEq : R + L + 1 = Q + 1 := by
    dsimp only [R, L, Q]
    rw [Nat.cast_sub hN]
    ring
  have hWidth' : (L + 1) ^ 8 ≤ V * R ^ 9 := by
    simpa only [L, R] using hkW
  have hOuter := h3Path_criticalWidthCap_boundsOuter244 R L V hR hL hV hWidth'
  rw [hOuterEq] at hOuter
  have hR6 : 1 ≤ R ^ 6 := by
    simpa only [one_pow] using
      (pow_le_pow_left₀ (by norm_num : 0 ≤ (1 : ℝ)) hR 6)
  have hEsc' : (U + 1) * R ^ 6 <
      h3PathFiniteAnnulusPDEVariationCoefficient244 R Q (K (v k)) (C (v k)) + 1 := by
    simpa only [R, Q, h3PathCubicAnnulusActualLinearRate244] using hEsc
  have hRate : U * R ^ 6 <
      h3PathFiniteAnnulusPDEVariationCoefficient244 R Q (K (v k)) (C (v k)) := by
    nlinarith only [hEsc', hR6]
  have hAmplification :=
    h3Path_scalarCriticalWidth_linearEscape_sourceSpectral244
      R Q U (256 * (V + 1)) (K (v k)) (C (v k))
      hR hRQ hU (by positivity) hOuter hRate
  refine ⟨k, hn, ?_⟩
  simpa only [R] using hAmplification

end
end PrimeTensor.FirstMonomialTriad
