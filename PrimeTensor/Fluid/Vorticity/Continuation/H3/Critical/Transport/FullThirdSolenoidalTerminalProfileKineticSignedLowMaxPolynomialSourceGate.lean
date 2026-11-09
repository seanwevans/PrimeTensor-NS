import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxOneRadiusSourceEnvelope
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
# Signed sixth flux: actual three-axis polynomial Fourier-ball source gate

The physical Fourier-gradient ball is transported by the canonical
volume-preserving `WithLp.ofLp` map into a real three-axis supremum-norm
cube. Its volume is at most `(2ρ)^3` for positive ρ, without assuming a
Euclidean-ball volume normalization or a free measure-space instance.

For natural radii ρ=k+1, this controls the exact physical projected-source
ceiling by `ρ² sqrt(E₀) + 54 ρ³ E₀`, and therefore the entire kinetic index
rate by one explicit polynomial of degree twelve in frequency (with kinetic
anchor coefficients). The original signed sixth-flux alternatives persist:
positive relative H³ gap dissipation, explicit polynomial rate payment,
or a certified outer annular frequency exceeding the gap index. The
original tenth-power residual must still be excluded.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal SchwartzMap FourierTransform LineDeriv

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

-- Exactly the physical three-axis Lebesgue product used in the imported
-- kinetic source estimate, not a separately postulated Fourier measure.
noncomputable local instance axisFintypePolynomialSource244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpacePolynomialSource244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

private theorem thirdFullKinetic_axis_card_three244 :
    Fintype.card (PrimeTensor.Axis Depth.three) = 3 := by
  classical
  have hSum := axis_sum_three
    (fun _ : PrimeTensor.Axis Depth.three => (1 : ℕ))
  simpa [Finset.sum_const, nsmul_eq_mul] using hSum

/-- The TRUE radial Fourier-gradient ball lies within the pullback of a
three-dimensional sup-norm cube. The radius is deliberately nonsharp:
`‖ξ‖ ≤ 2π‖ξ‖` eliminates constants involving π. -/
theorem thirdFullKinetic_signedLowMax_radialBall_subset_cube244
    (ρ : ℝ) (hρ : 0 < ρ) :
    h3TerminalRadialFrequencyBelow ρ ⊆
      (WithLp.ofLp : H3FourierPoint3 → Point3) ⁻¹'
        Metric.ball (0 : Point3) ρ := by
  intro ξ hξ
  have hRadial : h3FourierGradientMagnitude ξ < ρ := by
    simpa only [h3TerminalRadialFrequencyBelow, Set.mem_ofPred_eq] using hξ
  have hNorm : ‖ξ‖ < ρ :=
    (h3Fourier_norm_le_gradientMagnitude ξ).trans_lt hRadial
  have hSup : ‖(WithLp.ofLp ξ : Point3)‖ ≤ ‖ξ‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg ξ)).2
    intro i
    simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le ξ i)
  change (WithLp.ofLp ξ : Point3) ∈ Metric.ball 0 ρ
  simpa only [Metric.mem_ball, dist_zero_right] using hSup.trans_lt hNorm

/-- Cubic volume of the actual 3D Fourier-gradient ball. This is a
cube bound, not a claim about the sharp ball volume `4πr³/3`. -/
theorem thirdFullKinetic_signedLowMax_fourierBallVolume_le_cube244
    (ρ : ℝ) (hρ : 0 < ρ) :
    (volume : Measure H3FourierPoint3).real
        (h3TerminalRadialFrequencyBelow ρ) ≤ (2 * ρ) ^ 3 := by
  have hSub := thirdFullKinetic_signedLowMax_radialBall_subset_cube244 ρ hρ
  have hMeasure :
      (volume : Measure H3FourierPoint3)
        (h3TerminalRadialFrequencyBelow ρ) ≤
      ENNReal.ofReal ((2 * ρ) ^ 3) := by
    calc
      (volume : Measure H3FourierPoint3)
          (h3TerminalRadialFrequencyBelow ρ) ≤
        (volume : Measure H3FourierPoint3)
          ((WithLp.ofLp : H3FourierPoint3 → Point3) ⁻¹'
            Metric.ball (0 : Point3) ρ) := measure_mono hSub
      _ = (volume : Measure Point3) (Metric.ball 0 ρ) := by
        exact (PiLp.volume_preserving_ofLp
          (PrimeTensor.Axis Depth.three)).measure_preimage
            (measurableSet_ball : MeasurableSet (Metric.ball (0 : Point3) ρ)).nullMeasurableSet
      _ = ENNReal.ofReal ((2 * ρ) ^ 3) := by
        rw [Real.volume_pi_ball (0 : Point3) hρ]
        rw [thirdFullKinetic_axis_card_three244]
  rw [Measure.real_def]
  calc
    ((volume : Measure H3FourierPoint3)
        (h3TerminalRadialFrequencyBelow ρ)).toReal ≤
      (ENNReal.ofReal ((2 * ρ) ^ 3)).toReal :=
        ENNReal.toReal_mono (by simp) hMeasure
    _ = (2 * ρ) ^ 3 := ENNReal.toReal_ofReal (by positivity)

/-- Positive natural radii make the cube bound at most nine times the
fourth power. This elementary slack gives a clean square-root estimate. -/
theorem thirdFullKinetic_signedLowMax_fourierBallVolume_le_nineFourth244
    (ρ : ℝ) (hρ : 1 ≤ ρ) :
    (volume : Measure H3FourierPoint3).real
        (h3TerminalRadialFrequencyBelow ρ) ≤ 9 * ρ ^ 4 := by
  have hVolume := thirdFullKinetic_signedLowMax_fourierBallVolume_le_cube244
    ρ (by linarith only [hρ])
  have hρ0 : 0 ≤ ρ := by linarith only [hρ]
  have hPow : ρ ^ 3 ≤ ρ ^ 4 := by
    calc
      ρ ^ 3 = ρ ^ 3 * 1 := by ring
      _ ≤ ρ ^ 3 * ρ := mul_le_mul_of_nonneg_left hρ (pow_nonneg hρ0 3)
      _ = ρ ^ 4 := by ring
  have hEight : 8 * ρ ^ 3 ≤ 8 * ρ ^ 4 :=
    mul_le_mul_of_nonneg_left hPow (by norm_num)
  have hNine : 8 * ρ ^ 4 ≤ 9 * ρ ^ 4 := by nlinarith only [pow_nonneg hρ0 4]
  nlinarith only [hVolume, hEight, hNine]

/-- Bernstein plus the cubic Fourier cube bound gives a concrete source
rate polynomial, with kinetic anchor only and no moving H³ norm. -/
theorem thirdFullKinetic_signedLowMax_sourceCeiling_le_polynomial244
    (ρ E0 : ℝ) (hρ : 1 ≤ ρ) (hE : 0 ≤ E0) :
    thirdFullPhysicalKineticLowBandSourceCeiling244 ρ E0 ≤
      ρ ^ 2 * Real.sqrt E0 + 54 * ρ ^ 3 * E0 := by
  let V : ℝ := (volume : Measure H3FourierPoint3).real
    (h3TerminalRadialFrequencyBelow ρ)
  let A : ℝ := 18 * (ρ * E0)
  have hV : V ≤ 9 * ρ ^ 4 :=
    thirdFullKinetic_signedLowMax_fourierBallVolume_le_nineFourth244 ρ hρ
  have hA0 : 0 ≤ A := by
    dsimp only [A]
    have hρ0 : 0 ≤ ρ := by linarith only [hρ]
    positivity
  have hSquare : V * A ^ 2 ≤ (54 * ρ ^ 3 * E0) ^ 2 := by
    calc
      V * A ^ 2 ≤ (9 * ρ ^ 4) * A ^ 2 :=
        mul_le_mul_of_nonneg_right hV (sq_nonneg _)
      _ = (54 * ρ ^ 3 * E0) ^ 2 := by dsimp only [A]; ring
  have hRight : 0 ≤ 54 * ρ ^ 3 * E0 := by
    have hρ0 : 0 ≤ ρ := by linarith only [hρ]
    positivity
  have hSqrt : Real.sqrt (V * A ^ 2) ≤ 54 * ρ ^ 3 * E0 := by
    calc
      Real.sqrt (V * A ^ 2) ≤ Real.sqrt ((54 * ρ ^ 3 * E0) ^ 2) :=
        Real.sqrt_le_sqrt hSquare
      _ = 54 * ρ ^ 3 * E0 := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hRight]
  change ρ ^ 2 * Real.sqrt E0 + Real.sqrt (V * A ^ 2) ≤
    ρ ^ 2 * Real.sqrt E0 + 54 * ρ ^ 3 * E0
  exact add_le_add_right hSqrt (ρ ^ 2 * Real.sqrt E0)

/-- The exact index-rate bound with NO residual Fourier volume factor.
All frequency dependence is now a polynomial of degree twelve. -/
noncomputable def thirdFullKineticSignedLowMaxPolynomialIndexRate244
    (k : ℕ) (E0 : ℝ) : ℝ :=
  1 + 2 * ((k : ℝ) + 1) *
    (24 * ((k : ℝ) + 2) ^ 2 * ((k : ℝ) + 1) ^ 6 *
      Real.sqrt E0 *
      (((k : ℝ) + 1) ^ 2 * Real.sqrt E0 +
        54 * ((k : ℝ) + 1) ^ 3 * E0))

/-- The accepted full one-radius kinetic index rate is bounded by the
polynomial in natural gap index. -/
theorem thirdFullKinetic_signedLowMax_indexRate_le_polynomial244
    (k : ℕ) (E0 : ℝ) (hE : 0 ≤ E0) :
    thirdFullKineticSignedLowMaxOneRadiusIndexRate244 k E0 ≤
      thirdFullKineticSignedLowMaxPolynomialIndexRate244 k E0 := by
  let r : ℝ := (k : ℝ) + 1
  let F : ℝ := 24 * ((k : ℝ) + 2) ^ 2 * r ^ 6 * Real.sqrt E0
  have hr : 1 ≤ r := by
    dsimp only [r]
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith only [hk]
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hSource :
      thirdFullPhysicalKineticLowBandSourceCeiling244 r E0 ≤
        r ^ 2 * Real.sqrt E0 + 54 * r ^ 3 * E0 :=
    thirdFullKinetic_signedLowMax_sourceCeiling_le_polynomial244 r E0 hr hE
  have hBand : thirdFullKineticSignedLowMaxOneRadiusBandRate244 k E0 ≤
      F * (r ^ 2 * Real.sqrt E0 + 54 * r ^ 3 * E0) := by
    change F * thirdFullPhysicalKineticLowBandSourceCeiling244 r E0 ≤
      F * (r ^ 2 * Real.sqrt E0 + 54 * r ^ 3 * E0)
    exact mul_le_mul_of_nonneg_left hSource hF
  have hCoeff : 0 ≤ 2 * r := by dsimp only [r]; positivity
  have hScaled := mul_le_mul_of_nonneg_left hBand hCoeff
  change 1 + 2 * r * thirdFullKineticSignedLowMaxOneRadiusBandRate244 k E0 ≤
    1 + 2 * r * (F * (r ^ 2 * Real.sqrt E0 + 54 * r ^ 3 * E0))
  exact add_le_add_right hScaled 1

/-- The exact finite sum C_k is bounded by the genuine three-dimensional
kinetic Bernstein polynomial. -/
theorem thirdFullKinetic_signedLowMax_finiteRate_le_polynomial244
    (k : ℕ) (E0 : ℝ) (hE : 0 ≤ E0) :
    thirdFullKineticSignedLowMaxFiniteGaugeRateCeiling244 k E0 ≤
      thirdFullKineticSignedLowMaxPolynomialIndexRate244 k E0 :=
  (thirdFullKinetic_signedLowMax_indexRate_le_oneRadius244 k E0 hE).trans
    (thirdFullKinetic_signedLowMax_indexRate_le_polynomial244 k E0 hE)

/-- Positivity of the polynomial rate allows a true inverse gap charge. -/
theorem thirdFullKinetic_signedLowMax_polynomialRate_pos244
    (k : ℕ) (E0 : ℝ) (hE : 0 ≤ E0) :
    0 < thirdFullKineticSignedLowMaxPolynomialIndexRate244 k E0 := by
  have hOld := thirdFullKinetic_signedLowMax_oneRadiusIndexRate_pos244 k E0 hE
  exact lt_of_lt_of_le hOld
    (thirdFullKinetic_signedLowMax_indexRate_le_polynomial244 k E0 hE)

/-- Signed sixth flux: actual index-rate payment has a polynomial inverse
physical full H³ dissipation cost on the SAME original kinetic gap. -/
theorem thirdFullKinetic_signedLowMax_polynomial_inverseGapCharge244
    (k : ℕ) (E0 h D : ℝ) (hE : 0 ≤ E0) (hh : 0 < h)
    (hD : 0 ≤ D)
    (hRate : h ^ 2 ≤
      32 * thirdFullKineticSignedLowMaxOneRadiusIndexRate244 k E0 * D) :
    h ^ 2 / (32 * thirdFullKineticSignedLowMaxPolynomialIndexRate244 k E0) ≤ D := by
  have hC := thirdFullKinetic_signedLowMax_indexRate_le_polynomial244 k E0 hE
  have hP : 0 < thirdFullKineticSignedLowMaxPolynomialIndexRate244 k E0 :=
    thirdFullKinetic_signedLowMax_polynomialRate_pos244 k E0 hE
  have hBound : h ^ 2 ≤ 32 * thirdFullKineticSignedLowMaxPolynomialIndexRate244 k E0 * D := by
    calc
      h ^ 2 ≤ 32 * thirdFullKineticSignedLowMaxOneRadiusIndexRate244 k E0 * D := hRate
      _ ≤ 32 * thirdFullKineticSignedLowMaxPolynomialIndexRate244 k E0 * D := by
        have hMul := mul_le_mul_of_nonneg_right hC hD
        nlinarith only [hMul]
  have hDen : 0 < 32 * thirdFullKineticSignedLowMaxPolynomialIndexRate244 k E0 :=
    mul_pos (by norm_num) hP
  apply (div_le_iff₀ hDen).mpr
  calc
    h ^ 2 ≤ 32 * thirdFullKineticSignedLowMaxPolynomialIndexRate244 k E0 * D := hBound
    _ = D * (32 * thirdFullKineticSignedLowMaxPolynomialIndexRate244 k E0) := by ring

/-- The cofinal physical signed sixth-flux obstruction with its
THREE-DIMENSIONAL, polynomial index-rate charge. Neither the relative
full-H³ dissipation density nor the prior tenth-power residual vanishes
without an additional argument. -/
theorem thirdFullPhysical_kineticGaps_signedLowMax_tenthResidual_polynomialGate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (M : ℕ → ℝ) (tau : ℕ → ℝ) (N : ℕ → ℕ)
    (delta : ℕ → ℝ) (v : ℕ → ℕ)
    (hLimit : Tendsto (fun k => tau (v k)) atTop (𝓝 T))
    (hSeparated : ∀ k l : ℕ, k < l →
      tau (v k) + delta (v k) < tau (v l))
    (hWindows : ∀ k : ℕ,
      tau (v k) ∈ Set.Ioo b T ∧
      ThirdFullKineticNaturalAnnularLocalWitness244
        hH3 b (tau (v k)) (v k) (N (v k))
        (M (v k)) (delta (v k)))
    (eta : ℝ) (hEta : 0 < eta)
    (J : ℕ) (E epsilon : ℝ) (hE : 0 ≤ E) (hEpsilon : 0 < epsilon) :
    let h : ℝ := thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E
    let D : ℕ → ℝ := fun k =>
      ∫ r in (tau (v k) + delta (v k))..tau (v (k + 1)),
        velocityH3DissipationAt u r ∂volume
    let G : ℕ → ℕ := thirdFullKineticSignedLowMaxPhysicalAdaptiveGauge244
      (velocityH3Energy0At u b) h D
    Tendsto G atTop atTop ∧
      (∀ᶠ k : ℕ in atTop,
        ∀ (R : ℕ) (t : ℝ),
          t ∈ Set.Icc (tau (v k) + delta (v k)) (tau (v (k + 1))) →
          eta < -velocityH3TransportDerivative3At u t →
          ¬ ThirdFullKineticSignedLowMaxTenthPowerResidual244
            hH3 R J E eta epsilon
              (tau (v k) + delta (v k)) (tau (v (k + 1))) t →
          ((tau (v (k + 1)) - (tau (v k) + delta (v k))) * h ≤
              16 * D k) ∨
          (h ^ 2 ≤ 32 * thirdFullKineticSignedLowMaxPolynomialIndexRate244
              k (velocityH3Energy0At u b) * D k) ∨
          (∃ Q : ℕ, R ≤ Q ∧ k < Q)) := by
  let h : ℝ := thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E
  let D : ℕ → ℝ := fun k =>
    ∫ r in (tau (v k) + delta (v k))..tau (v (k + 1)),
      velocityH3DissipationAt u r ∂volume
  let G : ℕ → ℕ := thirdFullKineticSignedLowMaxPhysicalAdaptiveGauge244
    (velocityH3Energy0At u b) h D
  change Tendsto G atTop atTop ∧
    (∀ᶠ k : ℕ in atTop, ∀ (R : ℕ) (t : ℝ),
      t ∈ Set.Icc (tau (v k) + delta (v k)) (tau (v (k + 1))) →
      eta < -velocityH3TransportDerivative3At u t →
      ¬ ThirdFullKineticSignedLowMaxTenthPowerResidual244
        hH3 R J E eta epsilon
          (tau (v k) + delta (v k)) (tau (v (k + 1))) t →
      ((tau (v (k + 1)) - (tau (v k) + delta (v k))) * h ≤ 16 * D k) ∨
      (h ^ 2 ≤ 32 * thirdFullKineticSignedLowMaxPolynomialIndexRate244
        k (velocityH3Energy0At u b) * D k) ∨
      (∃ Q : ℕ, R ≤ Q ∧ k < Q))
  have hOld :=
    thirdFullPhysical_kineticGaps_signedLowMax_tenthResidual_oneRadiusGate244
      hH3 hClass hDInt b hb M tau N delta v
      hLimit hSeparated hWindows eta hEta J E epsilon hE hEpsilon
  change Tendsto G atTop atTop ∧
    (∀ᶠ k : ℕ in atTop, ∀ (R : ℕ) (t : ℝ),
      t ∈ Set.Icc (tau (v k) + delta (v k)) (tau (v (k + 1))) →
      eta < -velocityH3TransportDerivative3At u t →
      ¬ ThirdFullKineticSignedLowMaxTenthPowerResidual244
        hH3 R J E eta epsilon
          (tau (v k) + delta (v k)) (tau (v (k + 1))) t →
      ((tau (v (k + 1)) - (tau (v k) + delta (v k))) * h ≤ 16 * D k) ∨
      (h ^ 2 ≤ 32 * thirdFullKineticSignedLowMaxOneRadiusIndexRate244
        k (velocityH3Energy0At u b) * D k) ∨
      (∃ Q : ℕ, R ≤ Q ∧ k < Q)) at hOld
  refine ⟨hOld.1, ?_⟩
  filter_upwards [hOld.2] with k hk
  intro R t ht hAdverse hNoResidual
  rcases hk R t ht hAdverse hNoResidual with hClock | hRest
  · exact Or.inl hClock
  rcases hRest with hRate | hOuter
  · right; left
    have hCap := thirdFullKinetic_signedLowMax_indexRate_le_polynomial244
      k (velocityH3Energy0At u b) (velocityH3Energy0At_nonneg u b)
    have hxy : tau (v k) + delta (v k) < tau (v (k + 1)) :=
      hSeparated k (k + 1) (Nat.lt_succ_self k)
    have hD : 0 ≤ D k := by
      change 0 ≤ ∫ r in (tau (v k) + delta (v k))..tau (v (k + 1)),
        velocityH3DissipationAt u r ∂volume
      exact intervalIntegral.integral_nonneg hxy.le
        (fun r _hr => velocityH3DissipationAt_nonneg u r)
    have hMul := mul_le_mul_of_nonneg_right hCap hD
    calc
      h ^ 2 ≤ 32 * thirdFullKineticSignedLowMaxOneRadiusIndexRate244
          k (velocityH3Energy0At u b) * D k := hRate
      _ ≤ 32 * thirdFullKineticSignedLowMaxPolynomialIndexRate244
          k (velocityH3Energy0At u b) * D k := by
        nlinarith only [hMul]
  · exact Or.inr (Or.inr hOuter)

end
end PrimeTensor.FirstMonomialTriad
