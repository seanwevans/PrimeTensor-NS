import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowVectorSchwartz

/-!
# A concrete sharp six-packet Schwartz field with isolated Fourier centers

Fix `t = 1/4`, hence a positive separation radius `1/16`.  All six centers
are distinct, and each smooth center cutoff is zero at each of the *other*
five centers.  This is an exact consequence of the already proved strict
coordinate-ball localization, not an assumed support condition.

Thus the actual divergence-free, Hermitian vector Schwartz field from the
previous module reproduces the three sharp polarizations at p, q, r.
The six-order coefficient at these centers is therefore exactly the
nonzero imaginary sharp symbol. This is a pointwise result on an actual
Schwartz field, not yet a nonzero integral over a frequency neighborhood.
-/

namespace PrimeTensor.FirstMonomialTriad

open scoped SchwartzMap

noncomputable section

private theorem quarter_ne : (1 / 4 : ℝ) ≠ 0 := by norm_num

/-- At t=1/4, distinct sharp centers are outside each other's smooth support. -/
theorem lowNormalQuarter_cutoff_off_center
    (i j : Fin 6) (hij : i ≠ j) :
    lowNormalSmoothCenterCutoff (1 / 4 : ℝ) quarter_ne i
      (lowNormalSixCenter (1 / 4 : ℝ) j) = 0 := by
  by_contra hNonzero
  have hBall := lowNormalSmoothCenterCutoff_nonzero_coordinateBall
    (1 / 4 : ℝ) quarter_ne i (lowNormalSixCenter (1 / 4 : ℝ) j) hNonzero
  have h0 := hBall 0
  have h1 := hBall 1
  fin_cases i <;> fin_cases j
  all_goals
    norm_num [lowNormalSixCenter, lowNormalLatticeEmbedding,
      lowNormalSignedLatticeCenter, lowNormalSixCenterSeparationRadius] at *

/-- Exact Kronecker data for the six compactly supported frequency cutoffs. -/
theorem lowNormalQuarter_cutoff_at_center (i j : Fin 6) :
    lowNormalSmoothCenterCutoff (1 / 4 : ℝ) quarter_ne i
      (lowNormalSixCenter (1 / 4 : ℝ) j) = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp [lowNormalSmoothCenterCutoff_at_center]
  · rw [if_neg hij]
    exact lowNormalQuarter_cutoff_off_center i j hij

/-- The full real-compatible, solenoidal Schwartz field with t = 1/4. -/
noncomputable def lowNormalQuarterSchwartz :
    𝓢(Fin 3 → ℝ, Fin 3 → ℂ) :=
  lowNormalSmoothSixPacketSchwartz (1 / 4 : ℝ) quarter_ne

/-- At any frequency where the negative-frequency half vanishes,
Hermitianization leaves the positive three-packet sum unchanged. -/
private theorem lowNormalSixPacket_at_positive_only
    (t : ℝ) (χP χQ χR : (Fin 3 → ℝ) → ℝ)
    (ξ : Fin 3 → ℝ) (a : Fin 3 → ℂ)
    (hPositive : lowNormalPositiveThreePacketSum t χP χQ χR ξ = a)
    (hNegative : lowNormalPositiveThreePacketSum t χP χQ χR
        (fun d => -ξ d) = fun _ => 0) :
    lowNormalSixPacketFourier t χP χQ χR ξ = a := by
  funext d
  simp [lowNormalSixPacketFourier, lowNormalHermitianize,
    hPositive, hNegative]

/-- At the first frequency, no other positive packet or reflected packet
contributes: the actual vector Schwartz field has polarization A. -/
theorem lowNormalQuarterSchwartz_at_P :
    lowNormalQuarterSchwartz lowNormalAuditP = lowNormalAuditA := by
  let t : ℝ := 1 / 4
  let χ (i : Fin 6) := lowNormalSmoothCenterCutoff t quarter_ne i
  have hP : lowNormalPositiveThreePacketSum t (χ 0) (χ 1) (χ 2)
      lowNormalAuditP = lowNormalAuditA := by
    apply lowNormalPositiveThreePacketSum_at_P t quarter_ne
    · rw [← (lowNormalSixCenter_primary t).1]
      exact lowNormalSmoothCenterCutoff_at_center t quarter_ne 0
    · rw [← (lowNormalSixCenter_primary t).1]
      exact lowNormalQuarter_cutoff_off_center 1 0 (by decide)
    · rw [← (lowNormalSixCenter_primary t).1]
      exact lowNormalQuarter_cutoff_off_center 2 0 (by decide)
  have hN : lowNormalPositiveThreePacketSum t (χ 0) (χ 1) (χ 2)
      (fun d => -lowNormalAuditP d) = fun _ => 0 := by
    apply lowNormalPositiveThreePacketSum_zero_of_cutoffs_zero
    · rw [← (lowNormalSixCenter_reflected t).1]
      exact lowNormalQuarter_cutoff_off_center 0 3 (by decide)
    · rw [← (lowNormalSixCenter_reflected t).1]
      exact lowNormalQuarter_cutoff_off_center 1 3 (by decide)
    · rw [← (lowNormalSixCenter_reflected t).1]
      exact lowNormalQuarter_cutoff_off_center 2 3 (by decide)
  change lowNormalSixPacketFourier t (χ 0) (χ 1) (χ 2) lowNormalAuditP = _
  exact lowNormalSixPacket_at_positive_only t (χ 0) (χ 1) (χ 2)
    lowNormalAuditP lowNormalAuditA hP hN

/-- The low middle q-frequency retains exactly polarization B. -/
theorem lowNormalQuarterSchwartz_at_Q :
    lowNormalQuarterSchwartz (lowNormalAuditQ (1 / 4 : ℝ)) = lowNormalAuditB := by
  let t : ℝ := 1 / 4
  let χ (i : Fin 6) := lowNormalSmoothCenterCutoff t quarter_ne i
  have hQ : lowNormalPositiveThreePacketSum t (χ 0) (χ 1) (χ 2)
      (lowNormalAuditQ t) = lowNormalAuditB := by
    apply lowNormalPositiveThreePacketSum_at_Q t quarter_ne
    · rw [← (lowNormalSixCenter_primary t).2.1]
      exact lowNormalQuarter_cutoff_off_center 0 1 (by decide)
    · rw [← (lowNormalSixCenter_primary t).2.1]
      exact lowNormalSmoothCenterCutoff_at_center t quarter_ne 1
    · rw [← (lowNormalSixCenter_primary t).2.1]
      exact lowNormalQuarter_cutoff_off_center 2 1 (by decide)
  have hN : lowNormalPositiveThreePacketSum t (χ 0) (χ 1) (χ 2)
      (fun d => -lowNormalAuditQ t d) = fun _ => 0 := by
    apply lowNormalPositiveThreePacketSum_zero_of_cutoffs_zero
    · rw [← (lowNormalSixCenter_reflected t).2.1]
      exact lowNormalQuarter_cutoff_off_center 0 4 (by decide)
    · rw [← (lowNormalSixCenter_reflected t).2.1]
      exact lowNormalQuarter_cutoff_off_center 1 4 (by decide)
    · rw [← (lowNormalSixCenter_reflected t).2.1]
      exact lowNormalQuarter_cutoff_off_center 2 4 (by decide)
  change lowNormalSixPacketFourier t (χ 0) (χ 1) (χ 2) (lowNormalAuditQ t) = _
  exact lowNormalSixPacket_at_positive_only t (χ 0) (χ 1) (χ 2)
    (lowNormalAuditQ t) lowNormalAuditB hQ hN

/-- The outer r-frequency retains exactly polarization C. -/
theorem lowNormalQuarterSchwartz_at_R :
    lowNormalQuarterSchwartz (lowNormalAuditR (1 / 4 : ℝ)) = lowNormalAuditC := by
  let t : ℝ := 1 / 4
  let χ (i : Fin 6) := lowNormalSmoothCenterCutoff t quarter_ne i
  have hR : lowNormalPositiveThreePacketSum t (χ 0) (χ 1) (χ 2)
      (lowNormalAuditR t) = lowNormalAuditC := by
    apply lowNormalPositiveThreePacketSum_at_R t quarter_ne
    · rw [← (lowNormalSixCenter_primary t).2.2]
      exact lowNormalQuarter_cutoff_off_center 0 2 (by decide)
    · rw [← (lowNormalSixCenter_primary t).2.2]
      exact lowNormalQuarter_cutoff_off_center 1 2 (by decide)
    · rw [← (lowNormalSixCenter_primary t).2.2]
      exact lowNormalSmoothCenterCutoff_at_center t quarter_ne 2
  have hN : lowNormalPositiveThreePacketSum t (χ 0) (χ 1) (χ 2)
      (fun d => -lowNormalAuditR t d) = fun _ => 0 := by
    apply lowNormalPositiveThreePacketSum_zero_of_cutoffs_zero
    · rw [← (lowNormalSixCenter_reflected t).2.2]
      exact lowNormalQuarter_cutoff_off_center 0 5 (by decide)
    · rw [← (lowNormalSixCenter_reflected t).2.2]
      exact lowNormalQuarter_cutoff_off_center 1 5 (by decide)
    · rw [← (lowNormalSixCenter_reflected t).2.2]
      exact lowNormalQuarter_cutoff_off_center 2 5 (by decide)
  change lowNormalSixPacketFourier t (χ 0) (χ 1) (χ 2) (lowNormalAuditR t) = _
  exact lowNormalSixPacket_at_positive_only t (χ 0) (χ 1) (χ 2)
    (lowNormalAuditR t) lowNormalAuditC hR hN

/-- The six-order sharp coefficient occurs at a genuine Schwartz Fourier
field, not merely for three independently prescribed amplitudes. -/
theorem lowNormalQuarterSchwartz_sixOrder :
    sixOrderTriadCoefficient lowNormalAuditP
      (lowNormalAuditQ (1 / 4 : ℝ)) (lowNormalAuditR (1 / 4 : ℝ))
      (lowNormalQuarterSchwartz lowNormalAuditP)
      (lowNormalQuarterSchwartz (lowNormalAuditQ (1 / 4 : ℝ)))
      (lowNormalQuarterSchwartz (lowNormalAuditR (1 / 4 : ℝ))) =
        -(((1 / 4 : ℝ)^2 * (1 + 2 * (1 / 4 : ℝ))^2 : ℝ) : ℂ) * Complex.I := by
  rw [lowNormalQuarterSchwartz_at_P, lowNormalQuarterSchwartz_at_Q,
    lowNormalQuarterSchwartz_at_R]
  exact lowNormalAudit_sixOrder (1 / 4 : ℝ)

/-- Consequently the coefficient is nonzero on the actual Schwartz field. -/
theorem lowNormalQuarterSchwartz_sixOrder_ne_zero :
    sixOrderTriadCoefficient lowNormalAuditP
      (lowNormalAuditQ (1 / 4 : ℝ)) (lowNormalAuditR (1 / 4 : ℝ))
      (lowNormalQuarterSchwartz lowNormalAuditP)
      (lowNormalQuarterSchwartz (lowNormalAuditQ (1 / 4 : ℝ)))
      (lowNormalQuarterSchwartz (lowNormalAuditR (1 / 4 : ℝ))) ≠ 0 := by
  rw [lowNormalQuarterSchwartz_sixOrder]
  norm_num

end
end PrimeTensor.FirstMonomialTriad
