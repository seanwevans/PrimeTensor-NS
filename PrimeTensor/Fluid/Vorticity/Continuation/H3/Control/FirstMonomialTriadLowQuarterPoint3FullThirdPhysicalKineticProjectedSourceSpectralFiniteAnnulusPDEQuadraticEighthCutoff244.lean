import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEQuadraticSharpJointBarrier244
import Mathlib.Tactic

/-!
# Eighth-order cutoff bound behind the ninth-order quadratic PDE barrier

The already-certified quadratic PDE variation coefficient is exactly the
square of the projected physical source ceiling times a cutoff gain. The
H³ radial Sobolev weight defining that gain is the polynomial
`1 + ρ² + ρ⁴ + ρ⁶`. This module derives a concrete eighth-power bound
for the cutoff gain, with no extra spectral envelope assumptions.

On the disjoint physical quadratic-sharp windows, the prior ninth-order
alternative therefore forces a quantitative inequality involving the
*selected outer cutoff*, rather than an opaque cutoff-gain symbol.
Neither an upper cutoff restriction nor a source ceiling is asserted by
preterminal admissibility; both remain assumptions in the corresponding
conditional implications.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Explicit H³ radial Sobolev weight grows at most like the sixth power
of the shifted radius on nonnegative radii. -/
theorem h3Path_radialSobolevCeiling_le_fourShiftSixth244
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    h3TerminalRadialSobolevWeightSquareCeiling ρ ≤ 4 * (ρ + 1) ^ 6 := by
  unfold h3TerminalRadialSobolevWeightSquareCeiling
  nlinarith only [hρ, pow_nonneg hρ 2, pow_nonneg hρ 3,
    pow_nonneg hρ 4, pow_nonneg hρ 5, pow_nonneg hρ 6]

/-- The exact physical source-quadratic gain is a polynomial in the
cutoff radii and the explicit radial weight ceilings; no square roots
remain after squaring the physical gradient estimate. -/
theorem h3Path_quadraticGain_eq_radialWeightPolynomial244
    (R Q : ℝ) :
    h3PathFiniteAnnulusPDEQuadraticGain244 R Q =
      9 * ((Q + 1) ^ 2 * h3TerminalRadialSobolevWeightSquareCeiling Q +
        (R + 1) ^ 2 * h3TerminalRadialSobolevWeightSquareCeiling R) := by
  have hQ : 0 ≤ 3 * h3TerminalRadialSobolevWeightSquareCeiling Q :=
    mul_nonneg (by norm_num) (h3TerminalRadialSobolevWeightSquareCeiling_pos Q).le
  have hR : 0 ≤ 3 * h3TerminalRadialSobolevWeightSquareCeiling R :=
    mul_nonneg (by norm_num) (h3TerminalRadialSobolevWeightSquareCeiling_pos R).le
  unfold h3PathFiniteAnnulusPDEQuadraticGain244
  simp only [mul_pow, Real.sq_sqrt hQ, Real.sq_sqrt hR]
  ring

/-- The explicit quadratic cutoff amplifier cannot grow faster than
an eighth power of the two shifted radii. In particular there is no
independent ninth-order growth at comparable Fourier cutoffs. -/
theorem h3Path_quadraticGain_le_eighthRadiusSum244
    (R Q : ℝ) (hR : 0 ≤ R) (hQ : 0 ≤ Q) :
    h3PathFiniteAnnulusPDEQuadraticGain244 R Q ≤
      36 * ((Q + 1) ^ 8 + (R + 1) ^ 8) := by
  have hWQ := h3Path_radialSobolevCeiling_le_fourShiftSixth244 Q hQ
  have hWR := h3Path_radialSobolevCeiling_le_fourShiftSixth244 R hR
  have hQBound :
      (Q + 1) ^ 2 * h3TerminalRadialSobolevWeightSquareCeiling Q ≤
        4 * (Q + 1) ^ 8 := by
    calc
      _ ≤ (Q + 1) ^ 2 * (4 * (Q + 1) ^ 6) :=
        mul_le_mul_of_nonneg_left hWQ (sq_nonneg _)
      _ = 4 * (Q + 1) ^ 8 := by ring
  have hRBound :
      (R + 1) ^ 2 * h3TerminalRadialSobolevWeightSquareCeiling R ≤
        4 * (R + 1) ^ 8 := by
    calc
      _ ≤ (R + 1) ^ 2 * (4 * (R + 1) ^ 6) :=
        mul_le_mul_of_nonneg_left hWR (sq_nonneg _)
      _ = 4 * (R + 1) ^ 8 := by ring
  rw [h3Path_quadraticGain_eq_radialWeightPolynomial244]
  linarith only [hQBound, hRBound]

/-- Concrete eighth-order estimate for the actual quadratic PDE
variation coefficient, directly in terms of the actual projected-source
ceiling and inner/outer radii. -/
theorem h3Path_quadraticPDESourceRate_le_eighthRadiusSum244
    (R Q C : ℝ) (hR : 0 ≤ R) (hQ : 0 ≤ Q) :
    h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244 R Q C ≤
      36 * C ^ 2 * ((Q + 1) ^ 8 + (R + 1) ^ 8) := by
  rw [h3Path_quadraticSharpQuadraticRate_sourceSquaredGain244]
  calc
    C ^ 2 * h3PathFiniteAnnulusPDEQuadraticGain244 R Q ≤
        C ^ 2 * (36 * ((Q + 1) ^ 8 + (R + 1) ^ 8)) :=
      mul_le_mul_of_nonneg_left
        (h3Path_quadraticGain_le_eighthRadiusSum244 R Q hR hQ)
        (sq_nonneg C)
    _ = 36 * C ^ 2 * ((Q + 1) ^ 8 + (R + 1) ^ 8) := by ring

/-- At a fixed ninth-order physical quadratic-rate spike, bounded
source square forces an explicit eighth-power Fourier-radius cost. -/
theorem h3Path_ninthQuadraticRate_boundedSource_forces_eighthCutoff244
    (R Q C S D : ℝ) (hR : 0 ≤ R) (hQ : 0 ≤ Q)
    (hSource : C ^ 2 ≤ S ^ 2)
    (hSpike : D * R ^ 9 <
      h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244 R Q C + 1) :
    D * R ^ 9 <
      36 * S ^ 2 * ((Q + 1) ^ 8 + (R + 1) ^ 8) + 1 := by
  have hSum : 0 ≤ (Q + 1) ^ 8 + (R + 1) ^ 8 := by positivity
  have hUpper := h3Path_quadraticPDESourceRate_le_eighthRadiusSum244
    R Q C hR hQ
  have hSourceUpper :
      36 * C ^ 2 * ((Q + 1) ^ 8 + (R + 1) ^ 8) ≤
        36 * S ^ 2 * ((Q + 1) ^ 8 + (R + 1) ^ 8) := by
    have hScaled : 36 * C ^ 2 ≤ 36 * S ^ 2 :=
      mul_le_mul_of_nonneg_left hSource (by norm_num)
    exact mul_le_mul_of_nonneg_right hScaled hSum
  linarith only [hSpike, hUpper, hSourceUpper]

/-- Quantitative exclusion of a linearly bounded outer cutoff when a
bounded source would have to pay a ninth-order PDE rate. The threshold
is explicit; in particular for fixed source and ratio it is eventually
met as the cubic witness radius increases. -/
theorem h3Path_ninthCutoffCost_excludes_linearOuterRadius244
    (R Q S D M : ℝ)
    (hR : 1 ≤ R) (hQ : 0 ≤ Q) (_hS : 0 ≤ S) (_hM : 0 ≤ M)
    (hSpike : D * R ^ 9 <
      36 * S ^ 2 * ((Q + 1) ^ 8 + (R + 1) ^ 8) + 1)
    (hLarge : 36 * S ^ 2 * (M ^ 8 + 256) + 1 ≤ D * R) :
    M * R < Q + 1 := by
  by_contra hNot
  have hOuter : Q + 1 ≤ M * R := le_of_not_gt hNot
  have hQ0 : 0 ≤ Q + 1 := by linarith only [hQ]
  have hQ8 : (Q + 1) ^ 8 ≤ (M * R) ^ 8 :=
    pow_le_pow_left₀ hQ0 hOuter 8
  have hR8two : (R + 1) ^ 8 ≤ (2 * R) ^ 8 :=
    pow_le_pow_left₀ (by linarith only [hR]) (by linarith only [hR]) 8
  have hR8 : 1 ≤ R ^ 8 := by
    have hp := pow_le_pow_left₀ (by norm_num : 0 ≤ (1 : ℝ)) hR 8
    simpa only [one_pow] using hp
  have hBoundPair :
      (Q + 1) ^ 8 + (R + 1) ^ 8 ≤ (M ^ 8 + 256) * R ^ 8 := by
    calc
      _ ≤ (M * R) ^ 8 + (2 * R) ^ 8 := add_le_add hQ8 hR8two
      _ = (M ^ 8 + 256) * R ^ 8 := by ring
  have hPairCost :
      36 * S ^ 2 * ((Q + 1) ^ 8 + (R + 1) ^ 8) + 1 ≤
        (36 * S ^ 2 * (M ^ 8 + 256) + 1) * R ^ 8 := by
    have hm := mul_le_mul_of_nonneg_left hBoundPair
      (by positivity : 0 ≤ 36 * S ^ 2)
    nlinarith only [hm, hR8]
  have hRateDom :
      (36 * S ^ 2 * (M ^ 8 + 256) + 1) * R ^ 8 ≤ D * R ^ 9 := by
    calc
      _ ≤ (D * R) * R ^ 8 :=
        mul_le_mul_of_nonneg_right hLarge (by positivity)
      _ = D * R ^ 9 := by ring
  have hNo := le_trans hPairCost hRateDom
  exact (not_lt_of_ge hNo) hSpike

/-- The actual quadratic-sharp physical cofinal witnesses carry the
ninth-order to eighth-order outer-cutoff implication. The source ceiling
and linear sixth-order assumptions remain explicit branch tests. -/
theorem h3Path_noL2Trace_finiteDissipation_ninthRateEighthCutoff244
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
      (∀ η B D S : ℝ, 0 < η → 0 ≤ B → 0 ≤ D →
        ∀ᶠ k : ℕ in atTop,
          η ≤ ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2) →
            h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1 ≤
              B * ((v k : ℝ) + 1) ^ 6 →
            C (v k) ^ 2 ≤ S ^ 2 →
              D * ((v k : ℝ) + 1) ^ 9 <
                36 * S ^ 2 *
                  ((((N (v k) : ℝ) + 1) + 1) ^ 8 +
                    (((v k : ℝ) + 1) + 1) ^ 8) + 1) := by
  obtain ⟨τ, N, K, C, δ, v, hv, hCofinal, hSeparate,
      hGap, hSummable, _hJoint, hGain⟩ :=
    h3Path_noL2Trace_finiteDissipation_jointSixthNinthSourceGain244
      hH3 hClass hMass hNoTrace hDInt
  refine ⟨τ, N, K, C, δ, v, hv, hCofinal, hSeparate,
    hGap, hSummable, ?_⟩
  intro η B D S hη hB hD
  filter_upwards [hGain η B D S hη hB hD] with k hk
  intro hkGeom hkLinear hkSource
  have hR : 0 ≤ ((v k : ℝ) + 1) := by positivity
  have hQ : 0 ≤ ((N (v k) : ℝ) + 1) := by positivity
  have hRate := hk hkGeom hkLinear hkSource
  have hUpper := h3Path_quadraticGain_le_eighthRadiusSum244
    ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) hR hQ
  have hSNonneg : 0 ≤ S ^ 2 := sq_nonneg S
  calc
    D * ((v k : ℝ) + 1) ^ 9 <
        S ^ 2 * h3PathFiniteAnnulusPDEQuadraticGain244
          ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) + 1 := hRate
    _ ≤ S ^ 2 *
          (36 * ((((N (v k) : ℝ) + 1) + 1) ^ 8 +
            (((v k : ℝ) + 1) + 1) ^ 8)) + 1 := by
      have hMul := mul_le_mul_of_nonneg_left hUpper hSNonneg
      linarith only [hMul]
    _ = 36 * S ^ 2 *
          ((((N (v k) : ℝ) + 1) + 1) ^ 8 +
            (((v k : ℝ) + 1) + 1) ^ 8) + 1 := by ring

end
end PrimeTensor.FirstMonomialTriad
