import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEQuadraticSharpClock244
import Mathlib.Tactic

/-!
# Joint intermittent sixth/ninth PDE barrier

The quadratic-sharp exact clock yields three branches on the physical
cofinal disjoint cubic annuli: compressed terminal lag, large linear PDE
rate, or large quadratic PDE rate. A single epsilon choice excludes both
bounded-rate branches at each sufficiently late noncompressed witness.

The quadratic rate is exactly the square of the actual projected-source
ceiling times the explicit nonnegative cutoff gain, not merely an upper
estimate. Consequently, a bounded source with bounded sixth-order linear
rate forces ninth-order cutoff amplification at noncompressed witnesses.

All conclusions remain conditional on full terminal H3 dissipation being
integrable and on the no-strong-terminal-L2-trace branch. No universal
source/cutoff bounds or lower terminal-time lag are proved.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Exact quadratic coefficient factorization. The physical quadratic
PDE rate carries a square of the selected source ceiling. -/
theorem h3Path_quadraticSharpQuadraticRate_sourceSquaredGain244
    (R Q C : ℝ) :
    h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244 R Q C =
      C ^ 2 * h3PathFiniteAnnulusPDEQuadraticGain244 R Q := by
  unfold h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
    h3PathLowRadialPDEGradientRate244
    h3PathFiniteAnnulusPDEQuadraticGain244
  ring

/-- A ninth-order physical quadratic-rate spike with a bounded squared
source ceiling must already be visible in the outer/inner cutoff gain. -/
theorem h3Path_ninthQuadraticRate_boundedSourceSquared_forces_gain244
    (R Q C S D : ℝ)
    (hSource : C ^ 2 ≤ S ^ 2)
    (hRate : D * R ^ 9 <
      h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244 R Q C + 1) :
    D * R ^ 9 <
      S ^ 2 * h3PathFiniteAnnulusPDEQuadraticGain244 R Q + 1 := by
  rw [h3Path_quadraticSharpQuadraticRate_sourceSquaredGain244] at hRate
  have hGainNonneg : 0 ≤ h3PathFiniteAnnulusPDEQuadraticGain244 R Q :=
    (h3Path_finiteAnnulusPDEGains_nonneg244 R Q 0 le_rfl).2
  have hComparison :
      C ^ 2 * h3PathFiniteAnnulusPDEQuadraticGain244 R Q ≤
        S ^ 2 * h3PathFiniteAnnulusPDEQuadraticGain244 R Q :=
    mul_le_mul_of_nonneg_right hSource hGainNonneg
  linarith only [hRate, hComparison]

/-- The three-scale epsilon-alternative implies an intermittent *joint*
barrier: at each late noncompressed index, no two fixed sixth/ninth order
rate ceilings can hold together. Neither branch needs to be eventually
selected. -/
theorem h3Path_quadraticSharpThreeScale_jointIntermittentEscape244
    (R G Λ Ξ : ℕ → ℝ)
    (hR : ∀ k : ℕ, 0 < R k)
    (hBarrier : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
      G k ≤ ε ∨ R k ^ 6 ≤ 16 * ε * (Λ k + 1) ∨
        R k ^ 9 ≤ 16 * ε ^ 2 * (Ξ k + 1))
    (η B D : ℝ) (hη : 0 < η) (hB : 0 ≤ B) (hD : 0 ≤ D) :
    ∀ᶠ k : ℕ in atTop,
      η ≤ G k →
        B * R k ^ 6 < Λ k + 1 ∨
          D * R k ^ 9 < Ξ k + 1 := by
  let W : ℝ := B + D + 1
  have hW : 0 < W := by dsimp only [W]; linarith only [hB, hD]
  let ε : ℝ := min (η / 2) (1 / (32 * W))
  have hε : 0 < ε := by
    dsimp only [ε]
    exact lt_min (by linarith only [hη]) (by positivity)
  have hTimeCap : ε ≤ η / 2 := by
    dsimp only [ε]
    exact min_le_left _ _
  have hWCap : ε ≤ 1 / (32 * W) := by
    dsimp only [ε]
    exact min_le_right _ _
  have hProduct : ε * (32 * W) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 32 * W)).mp hWCap
  have hEB : 0 ≤ ε * B := mul_nonneg hε.le hB
  have hED : 0 ≤ ε * D := mul_nonneg hε.le hD
  have hESum : 0 ≤ ε * (B + D) :=
    mul_nonneg hε.le (add_nonneg hB hD)
  have hEOne : ε ≤ 1 := by
    dsimp only [W] at hProduct
    nlinarith only [hProduct, hESum]
  have hESquare : ε ^ 2 ≤ ε := by
    have hFactor : 0 ≤ ε * (1 - ε) :=
      mul_nonneg hε.le (sub_nonneg.mpr hEOne)
    nlinarith only [hFactor]
  have hHalfB : 16 * ε * B ≤ 1 / 2 := by
    dsimp only [W] at hProduct
    nlinarith only [hProduct, hED, hε.le]
  have hHalfDLinear : 16 * ε * D ≤ 1 / 2 := by
    dsimp only [W] at hProduct
    nlinarith only [hProduct, hEB, hε.le]
  have hHalfD : 16 * ε ^ 2 * D ≤ 1 / 2 := by
    have hMul : ε ^ 2 * D ≤ ε * D :=
      mul_le_mul_of_nonneg_right hESquare hD
    nlinarith only [hMul, hHalfDLinear]
  filter_upwards [hBarrier ε hε] with k hk
  intro hGeom
  rcases hk with hTime | hLinear | hQuadratic
  · exact False.elim (by linarith only [hGeom, hTime, hTimeCap, hη])
  · left
    by_contra hNot
    have hRate : Λ k + 1 ≤ B * R k ^ 6 := le_of_not_gt hNot
    have hR6 : 0 < R k ^ 6 := pow_pos (hR k) _
    have hTooSmall : R k ^ 6 ≤ (1 / 2) * R k ^ 6 :=
      calc
        R k ^ 6 ≤ 16 * ε * (Λ k + 1) := hLinear
        _ ≤ 16 * ε * (B * R k ^ 6) :=
          mul_le_mul_of_nonneg_left hRate (by positivity)
        _ = (16 * ε * B) * R k ^ 6 := by ring
        _ ≤ (1 / 2) * R k ^ 6 :=
          mul_le_mul_of_nonneg_right hHalfB hR6.le
    nlinarith only [hTooSmall, hR6]
  · right
    by_contra hNot
    have hRate : Ξ k + 1 ≤ D * R k ^ 9 := le_of_not_gt hNot
    have hR9 : 0 < R k ^ 9 := pow_pos (hR k) _
    have hTooSmall : R k ^ 9 ≤ (1 / 2) * R k ^ 9 :=
      calc
        R k ^ 9 ≤ 16 * ε ^ 2 * (Ξ k + 1) := hQuadratic
        _ ≤ 16 * ε ^ 2 * (D * R k ^ 9) :=
          mul_le_mul_of_nonneg_left hRate (by positivity)
        _ = (16 * ε ^ 2 * D) * R k ^ 9 := by ring
        _ ≤ (1 / 2) * R k ^ 9 :=
          mul_le_mul_of_nonneg_right hHalfD hR9.le
    nlinarith only [hTooSmall, hR9]

/-- Physical quadratic-sharp clocks inherit a simultaneous intermittent
sixth/ninth-order rate obstruction. The source-squared alternative is
also retained at the same selected outer cutoff without new selection. -/
theorem h3Path_noL2Trace_finiteDissipation_jointSixthNinthSourceGain244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ)
        (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k : ℕ => τ (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      (∀ k : ℕ,
        ((v k : ℝ) + 1) ^ 3 / 4 <
          h3PathCubicAnnulusActualGap244 hH3 τ N (v k)) ∧
      Summable (fun k : ℕ =>
        δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ∧
      (∀ η B D : ℝ, 0 < η → 0 ≤ B → 0 ≤ D →
        ∀ᶠ k : ℕ in atTop,
          η ≤ ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2) →
            B * ((v k : ℝ) + 1) ^ 6 <
              h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1 ∨
            D * ((v k : ℝ) + 1) ^ 9 <
              h3PathCubicAnnulusActualQuadraticRate244 N C (v k) + 1) ∧
      (∀ η B D S : ℝ, 0 < η → 0 ≤ B → 0 ≤ D →
        ∀ᶠ k : ℕ in atTop,
          η ≤ ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2) →
            h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1 ≤
              B * ((v k : ℝ) + 1) ^ 6 →
            C (v k) ^ 2 ≤ S ^ 2 →
              D * ((v k : ℝ) + 1) ^ 9 <
                S ^ 2 * h3PathFiniteAnnulusPDEQuadraticGain244
                  ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) + 1) := by
  obtain ⟨τ, N, K, C, δ, v, hv, hCofinal, hSeparated,
      hGap, hSummable, hBarrier⟩ :=
    h3Path_noL2Trace_finiteDissipation_quadraticSharpThreeScale244
      hH3 hClass hMass hNoTrace hDInt
  have hJoint (η B D : ℝ) (hη : 0 < η) (hB : 0 ≤ B) (hD : 0 ≤ D) :
      ∀ᶠ k : ℕ in atTop,
        η ≤ ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2) →
          B * ((v k : ℝ) + 1) ^ 6 <
            h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1 ∨
          D * ((v k : ℝ) + 1) ^ 9 <
            h3PathCubicAnnulusActualQuadraticRate244 N C (v k) + 1 :=
    h3Path_quadraticSharpThreeScale_jointIntermittentEscape244
      (fun k => ((v k : ℝ) + 1))
      (fun k => ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2))
      (fun k => h3PathCubicAnnulusActualLinearRate244 N K C (v k))
      (fun k => h3PathCubicAnnulusActualQuadraticRate244 N C (v k))
      (fun k => by positivity) hBarrier η B D hη hB hD
  refine ⟨τ, N, K, C, δ, v, hv, hCofinal, hSeparated,
    hGap, hSummable, hJoint, ?_⟩
  intro η B D S hη hB hD
  filter_upwards [hJoint η B D hη hB hD] with k hk
  intro hkGeom hkLinear hkSource
  rcases hk hkGeom with hLinear | hQuadratic
  · exact False.elim ((not_lt_of_ge hkLinear) hLinear)
  · have hRate : D * ((v k : ℝ) + 1) ^ 9 <
        h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
          ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) (C (v k)) + 1 := by
      simpa only [h3PathCubicAnnulusActualQuadraticRate244] using hQuadratic
    exact h3Path_ninthQuadraticRate_boundedSourceSquared_forces_gain244
      ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
      (C (v k)) S D hkSource hRate

end
end PrimeTensor.FirstMonomialTriad
