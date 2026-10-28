import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalPeakLandauOvershoot244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Riccati.Lower.Bound
import Mathlib.Tactic

/-!
# Canonical peak transport spike versus the intrinsic inverse-root Riccati clock

The actual Landau bound forces a noncompressed canonical transport spike to
occur at high H3 energy unless its optimized peak clock is at most linear in
the original spectral sup norm.  The already proved monotonicity of
1/sqrt(E3(t)) + K*t/2 shows that a fourfold physical H3 energy overshoot
requires at least an inverse-root time interval.  Combining these two
independent bounds makes the optimized clock at most O(A) on the entire
noncompressed half-loss branch, where A is the original peak sup norm.

This avoids pretending that E3(s)=1+A^2: the correct three-component estimate
is E3(s)<=1+3*A^2<=4*A^2 when A>=2.  No uniform terminal bound and no
regularity theorem are asserted; the alternative of terminal compression
remains present.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- A signed Landau transport spike requires either energy exceeding sixteen
starting sup-norm squares or a clock linear in the starting amplitude. -/
theorem h3Path_scalarLandauSpike_sixteenSquare_or_linearClock244
    (A B H C E Tr : ℝ)
    (hA : 2 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hSpike : H * A ^ 2 < 8 * (B + 1) * Tr)
    (hLandau : Tr ≤ 4422 * (1 + C * Real.sqrt E) * E) :
    16 * A ^ 2 < E ∨
      H < 128 * (B + 1) * 4422 * (1 + 4 * C * A) := by
  by_cases hLarge : 16 * A ^ 2 < E
  · exact Or.inl hLarge
  · right
    have hCap : E ≤ 16 * A ^ 2 := le_of_not_gt hLarge
    have hRoot : Real.sqrt E ≤ 4 * A := by
      have hSq := Real.sq_sqrt hE
      have hRootNN := Real.sqrt_nonneg E
      nlinarith only [hSq, hRootNN, hCap, hA]
    have hCScaled := mul_le_mul_of_nonneg_left hRoot hC
    have hCoeff :
        4422 * (1 + C * Real.sqrt E) ≤
          4422 * (1 + 4 * C * A) := by
      nlinarith only [hCScaled]
    have hFactor : 0 ≤ 4422 * (1 + C * Real.sqrt E) := by positivity
    have hTrUpper :
        Tr ≤ 4422 * (1 + 4 * C * A) * (16 * A ^ 2) := by
      calc
        Tr ≤ 4422 * (1 + C * Real.sqrt E) * E := hLandau
        _ ≤ 4422 * (1 + C * Real.sqrt E) * (16 * A ^ 2) :=
          mul_le_mul_of_nonneg_left hCap hFactor
        _ ≤ 4422 * (1 + 4 * C * A) * (16 * A ^ 2) :=
          mul_le_mul_of_nonneg_right hCoeff (by positivity)
    have hBudgetFactor : 0 ≤ 8 * (B + 1) := by positivity
    have hSpikeUpper :
        H * A ^ 2 <
          (128 * (B + 1) * 4422 * (1 + 4 * C * A)) * A ^ 2 := by
      calc
        H * A ^ 2 < 8 * (B + 1) * Tr := hSpike
        _ ≤ 8 * (B + 1) *
            (4422 * (1 + 4 * C * A) * (16 * A ^ 2)) :=
          mul_le_mul_of_nonneg_left hTrUpper hBudgetFactor
        _ = _ := by ring
    have hAPos : 0 < A ^ 2 := by
      have ha : 0 < A := by linarith only [hA]
      exact pow_pos ha _
    by_contra hNot
    have hSlow : 128 * (B + 1) * 4422 * (1 + 4 * C * A) ≤ H :=
      le_of_not_gt hNot
    have hScaled := mul_le_mul_of_nonneg_right hSlow hAPos.le
    exact (not_lt_of_ge hScaled) hSpikeUpper

/-- Elementary inverse-root Riccati comparison: a fourfold energy overshoot
cannot fit inside an optimized clock shorter than inverse starting amplitude.
The hypothesis on the inverse-root increment is obtained from the genuine H3
Riccati-shift monotonicity in the physical application below. -/
theorem h3Path_scalarRiccati_fourfoldOvershoot_forces_linearClock244
    (Es Eq A B H K d : ℝ)
    (hEs : 0 < Es) (hEq : 0 < Eq) (hA : 0 < A)
    (hB : 0 ≤ B) (hK : 0 ≤ K) (hH : 0 < H)
    (hStart : Es ≤ 4 * A ^ 2)
    (hOvershoot : 4 * Es < Eq)
    (hInverse : (Real.sqrt Es)⁻¹ ≤
      (Real.sqrt Eq)⁻¹ + (K / 2) * d)
    (hWidth : d ≤ (B + 1) / H) :
    H < 2 * K * (B + 1) * A := by
  let S : ℝ := Real.sqrt Es
  let Q : ℝ := Real.sqrt Eq
  have hSPos : 0 < S := Real.sqrt_pos.2 hEs
  have hQPos : 0 < Q := Real.sqrt_pos.2 hEq
  have hSSq : S ^ 2 = Es := Real.sq_sqrt hEs.le
  have hQSq : Q ^ 2 = Eq := Real.sq_sqrt hEq.le
  have hSquareGap : (2 * S) ^ 2 < Q ^ 2 := by
    nlinarith only [hSSq, hQSq, hOvershoot]
  have hDouble : 2 * S < Q :=
    (sq_lt_sq₀ (by positivity : 0 ≤ 2 * S) hQPos.le).1 hSquareGap
  have hInverseCompare : 2 * Q⁻¹ < S⁻¹ := by
    have hDiv : (2 : ℝ) / Q < 1 / S :=
      (div_lt_div_iff₀ hQPos hSPos).2 (by nlinarith only [hDouble])
    simpa only [div_eq_mul_inv, one_mul] using hDiv
  have hGap : S⁻¹ < K * d := by
    dsimp only [S, Q] at hInverseCompare ⊢
    linarith only [hInverse, hInverseCompare]
  have hOne : S⁻¹ * S = 1 := inv_mul_cancel₀ (ne_of_gt hSPos)
  have hTime : 1 < K * d * S := by
    calc
      (1 : ℝ) = S⁻¹ * S := hOne.symm
      _ < (K * d) * S := mul_lt_mul_of_pos_right hGap hSPos
  have hSquareBound : S ^ 2 ≤ (2 * A) ^ 2 := by
    nlinarith only [hSSq, hStart]
  have hRootBound : S ≤ 2 * A :=
    (sq_le_sq₀ hSPos.le (by positivity : 0 ≤ 2 * A)).mp hSquareBound
  have hWidthH : d * H ≤ B + 1 := by
    calc
      d * H ≤ ((B + 1) / H) * H :=
        mul_le_mul_of_nonneg_right hWidth hH.le
      _ = B + 1 := div_mul_cancel₀ _ (ne_of_gt hH)
  have hKTimesS : 0 ≤ K * S := mul_nonneg hK hSPos.le
  have hWidthScaled := mul_le_mul_of_nonneg_left hWidthH hKTimesS
  have hBudgetNonneg : 0 ≤ B + 1 := by
    linarith only [hB]
  have hRootScaled :
      (K * (B + 1)) * S ≤ (K * (B + 1)) * (2 * A) :=
    mul_le_mul_of_nonneg_left hRootBound
      (mul_nonneg hK hBudgetNonneg)
  have hTimeH := mul_lt_mul_of_pos_right hTime hH
  calc
    H = 1 * H := by ring
    _ < (K * d * S) * H := hTimeH
    _ = (K * S) * (d * H) := by ring
    _ ≤ (K * S) * (B + 1) := hWidthScaled
    _ = (K * (B + 1)) * S := by ring
    _ ≤ (K * (B + 1)) * (2 * A) := hRootScaled
    _ = 2 * K * (B + 1) * A := by ring

/-- The actual physical signed-transport spike, regardless of the size of
its energy overshoot, forces the optimized half-loss clock to be O(A).
The two mechanisms are distinguished internally: the instantaneous Landau
ceiling or the inverse-root time cost of a fourfold energy increase. -/
theorem h3Path_physicalTransportSpike_forces_linearClock244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (s q B H : ℝ)
    (hs : s ∈ Set.Ioo a T) (hq : q ∈ Set.Ioo a T)
    (hsq : s ≤ q)
    (hTwo : 2 ≤ ‖h3AuditActualSpectralVelocityTotal hH3 s‖)
    (hB : 0 ≤ B) (hH : 0 < H)
    (hWidth : q - s ≤ (B + 1) / H)
    (hSpike : H * ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 2 <
      8 * (B + 1) * velocityH3TransportDerivativeAt u q) :
    H < max
      (128 * (B + 1) * 4422 *
        (1 + 4 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          ‖h3AuditActualSpectralVelocityTotal hH3 s‖))
      (2 * h3PathSqrtEnergyRiccatiCoefficient * (B + 1) *
        ‖h3AuditActualSpectralVelocityTotal hH3 s‖) := by
  let A : ℝ := ‖h3AuditActualSpectralVelocityTotal hH3 s‖
  let Es : ℝ := velocityH3EnergyAt u s
  let Eq : ℝ := velocityH3EnergyAt u q
  let C : ℝ := h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
  let K : ℝ := h3PathSqrtEnergyRiccatiCoefficient
  have hsAbs : s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 hs.1, hs.2⟩
  have hExact := h3AuditActualSpectralVelocityTotal_energy_exact hH3 s hsAbs
  have hSup := h3Path_spectralSquareEnergy_le_threeSupSquare244
    (h3AuditActualSpectralVelocityTotal hH3 s)
  have hAOne : 1 ≤ A ^ 2 := by
    have hATwo : 2 ≤ A := hTwo
    nlinarith only [hATwo, sq_nonneg (A - 1)]
  have hStart : Es ≤ 4 * A ^ 2 := by
    dsimp only [Es, A]
    linarith only [hExact, hSup, hAOne]
  have hEsPos : 0 < Es :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (one_le_velocityH3EnergyAt u s)
  have hEqPos : 0 < Eq :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (one_le_velocityH3EnergyAt u q)
  have hAPos : 0 < A :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hTwo
  have hCNonneg : 0 ≤ C :=
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
  have hKNonneg : 0 ≤ K := h3PathSqrtEnergyRiccatiCoefficient_nonneg
  have hLandauRaw := h3Path_physicalFullTransport_abs_le_sqrtEnergy244
    hH3 hClass hq
  have hLandau : velocityH3TransportDerivativeAt u q ≤
      4422 * (1 + C * Real.sqrt Eq) * Eq := by
    have hBound := (le_abs_self _).trans hLandauRaw
    simpa only [C, Eq] using hBound
  have hSp : H * A ^ 2 <
      8 * (B + 1) * velocityH3TransportDerivativeAt u q := by
    simpa only [A] using hSpike
  have hAlt := h3Path_scalarLandauSpike_sixteenSquare_or_linearClock244
    A B H C Eq (velocityH3TransportDerivativeAt u q)
    hTwo hB hCNonneg hEqPos.le hSp hLandau
  rcases hAlt with hLargeEnergy | hSlowLandau
  · have hFourfold : 4 * Es < Eq := by
      linarith only [hLargeEnergy, hStart]
    have hMon := monotoneOn_h3PathInverseSqrtEnergyRiccatiShift
      hH3 hClass hs hq hsq
    have hInverse : (Real.sqrt Es)⁻¹ ≤
        (Real.sqrt Eq)⁻¹ + (K / 2) * (q - s) := by
      change (Real.sqrt Es)⁻¹ + (K / 2) * s ≤
        (Real.sqrt Eq)⁻¹ + (K / 2) * q at hMon
      linarith only [hMon]
    have hSlow := h3Path_scalarRiccati_fourfoldOvershoot_forces_linearClock244
      Es Eq A B H K (q - s)
      hEsPos hEqPos hAPos hB hKNonneg hH hStart hFourfold hInverse hWidth
    exact lt_of_lt_of_le hSlow (le_max_right _ _)
  · exact lt_of_lt_of_le hSlowLandau (le_max_left _ _)

/-- The optimized peak identity converts the linear upper clock into a
root-free polynomial obstruction, still conditional on the original
noncompressed half-loss branch. -/
theorem h3Path_linearClock_forces_eighthPowerBarrier244
    (A E H M : ℝ)
    (hE : 0 ≤ E) (hH : 0 < H)
    (hIdentity : A ^ 8 = 16384 * (E + 1) * H ^ 3)
    (hSlow : H < M) :
    A ^ 8 < 16384 * (E + 1) * M ^ 3 := by
  have hCube := pow_lt_pow_left₀ hSlow hH.le (by norm_num : 3 ≠ 0)
  have hFactor : 0 < 16384 * (E + 1) := by positivity
  have hScaled := mul_lt_mul_of_pos_left hCube hFactor
  calc
    A ^ 8 = 16384 * (E + 1) * H ^ 3 := hIdentity
    _ < 16384 * (E + 1) * M ^ 3 := hScaled

/-- The original canonical source peak and half-loss transport witness obey
terminal compression or an explicit O(A) upper clock and polynomial barrier.
No source-maximizing time is replaced. -/
theorem h3Path_optimizedPeak_terminalCompression_or_linearRiccatiClock244
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
      let A := ‖h3AuditActualSpectralVelocityTotal hH3 s‖
      let M := max
        (128 * (B + 1) * 4422 *
          (1 + 4 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient * A))
        (2 * h3PathSqrtEnergyRiccatiCoefficient * (B + 1) * A)
      T - s ≤ (B + 1) / H ∨
        ∃ r q : ℝ,
          r ∈ Set.Icc s (s + (B + 1) / H) ∧
          q ∈ Set.Icc s r ∧
          ‖h3AuditActualSpectralVelocityTotal hH3 r‖ < A / 2 ∧
          H * A ^ 2 < 8 * (B + 1) * velocityH3TransportDerivativeAt u q ∧
          H < M ∧
          A ^ 8 < 16384 * (velocityH3Energy0At u b + 1) * M ^ 3 := by
  obtain ⟨H, hH, hIdentity, hAlt⟩ :=
    h3Path_optimizedPeak_terminalCompression_or_transportSpike244
      hH3 hClass hDInt b hb s hs hTwo hLarge hThreshold
  let B : ℝ := ∫ t in a..T, velocityH3DissipationAt u t
  let A : ℝ := ‖h3AuditActualSpectralVelocityTotal hH3 s‖
  let M : ℝ := max
    (128 * (B + 1) * 4422 *
      (1 + 4 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient * A))
    (2 * h3PathSqrtEnergyRiccatiCoefficient * (B + 1) * A)
  refine ⟨H, hH, hIdentity, ?_⟩
  change T - s ≤ (B + 1) / H ∨
    ∃ r q : ℝ,
      r ∈ Set.Icc s (s + (B + 1) / H) ∧
      q ∈ Set.Icc s r ∧
      ‖h3AuditActualSpectralVelocityTotal hH3 r‖ < A / 2 ∧
      H * A ^ 2 < 8 * (B + 1) * velocityH3TransportDerivativeAt u q ∧
      A ^ 14 < 8388608 * (velocityH3Energy0At u b + 1) *
        (B + 1) ^ 3 * velocityH3TransportDerivativeAt u q ^ 3 at hAlt
  rcases hAlt with hCompressed | ⟨r, q, hr, hq, hHalf, hSpike, _hPoly⟩
  · exact Or.inl hCompressed
  · by_cases hCompressed : T - s ≤ (B + 1) / H
    · exact Or.inl hCompressed
    · right
      have hEnd : s + (B + 1) / H < T := by
        have hNot := lt_of_not_ge hCompressed
        linarith only [hNot]
      have hsClass : s ∈ Set.Ioo a T :=
        ⟨lt_trans hb.1 hs.1, hs.2⟩
      have hqClass : q ∈ Set.Ioo a T :=
        ⟨lt_of_lt_of_le hsClass.1 hq.1,
          lt_of_le_of_lt (le_trans hq.2 hr.2) hEnd⟩
      have hB : 0 ≤ B := by
        dsimp only [B]
        exact intervalIntegral.integral_nonneg hClass.terminal_start.2.le
          (fun t _ => velocityH3DissipationAt_nonneg u t)
      have hWidth : q - s ≤ (B + 1) / H := by
        have hRight := hr.2
        have hSub := hq.2
        linarith only [hRight, hSub]
      have hSlow := h3Path_physicalTransportSpike_forces_linearClock244
        hH3 hClass s q B H hsClass hqClass hq.1 hTwo hB hH hWidth hSpike
      have hPoly := h3Path_linearClock_forces_eighthPowerBarrier244
        A (velocityH3Energy0At u b) H M
        (velocityH3Energy0At_nonneg u b) hH hIdentity hSlow
      exact ⟨r, q, hr, hq, hHalf, hSpike, hSlow, hPoly⟩

end
end PrimeTensor.FirstMonomialTriad
