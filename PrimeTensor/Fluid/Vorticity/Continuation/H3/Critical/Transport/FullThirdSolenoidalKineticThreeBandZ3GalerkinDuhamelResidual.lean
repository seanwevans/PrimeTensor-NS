import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3GalerkinJointTemporalWiener
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# Exact finite-Galerkin Duhamel residual and cutoff-free quadratic consistency

For a real strong Galerkin trajectory confined to the W_(9/5) analytic ball,
the previous module proved source variation <= 51,000,000 (t-a) at W_(5/4).
The full projected quadratic source also has Laplacian cost <= 5,000,000.
The simple exponential fact 1-exp(-x) <= x for x>=0 now controls the
frozen-source heat discrepancy. The two integrands together have integral

  ((51,000,000 + 5,000,000*mu)/2) * (b-a)^2

and hence at viscosity <= 1/10 the full local residual is <= 25,750,000*h^2.
No bound has a factor depending on the number of frequency modes or their
ordered-pair output collisions. A Fourier coefficient may vanish identically.

The exact mild/Duhamel identity is a VISIBLE hypothesis in the final theorem;
it is not mistaken for a consequence of a discrete step or proved from an
unconstructed ODE. Likewise the uniform W_(9/5) ball is an explicit temporal
assumption. The remaining problem is deriving that mild identity from the
actual coefficientwise strong ODE and constructing/controlling the flow.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Set
open scoped Interval
noncomputable section

private abbrev MildIndex244 := thirdFullThreeBandZ3Index244
private abbrev MildBand244 := EuclideanSpace ℂ (Fin 3)

/-- Physical nonnegative heat lag is at most the bare Laplacian clock. -/
theorem thirdFullThreeBand_z3GalerkinHeatLag_le_clock244
    (mu h : ℝ) (hmu : 0 ≤ mu) (hh : 0 ≤ h)
    (n : MildIndex244) :
    0 ≤ 1 - thirdFullThreeBandZ3GalerkinHeatFactor244 mu h n ∧
    1 - thirdFullThreeBandZ3GalerkinHeatFactor244 mu h n ≤
      mu * h * ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2 := by
  have hb := thirdFullThreeBand_z3GalerkinHeatFactor_bounds244 mu h hmu hh n
  constructor
  · exact sub_nonneg.mpr hb.2
  · have he := Real.add_one_le_exp
        (-(mu * h * ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2))
    unfold thirdFullThreeBandZ3GalerkinHeatFactor244
    linarith

/-- The lagged exponential convolution differs from its frozen source by
one nonlinear source increment and one genuinely viscous heat deficit. -/
theorem thirdFullThreeBand_z3GalerkinLaggedSource_norm_bound244
    (mu h : ℝ) (hmu : 0 ≤ mu) (hh : 0 ≤ h)
    (s : Finset MildIndex244)
    (u v : MildIndex244 → MildBand244) (n : MildIndex244) :
    ‖(thirdFullThreeBandZ3GalerkinHeatFactor244 mu h n) •
        thirdFullThreeBandZ3GalerkinQuadratic244 s s u u n -
      thirdFullThreeBandZ3GalerkinQuadratic244 s s v v n‖ ≤
    ‖thirdFullThreeBandZ3GalerkinQuadratic244 s s u u n -
      thirdFullThreeBandZ3GalerkinQuadratic244 s s v v n‖ +
    (mu * h * ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2) *
      ‖thirdFullThreeBandZ3GalerkinQuadratic244 s s v v n‖ := by
  let sigma := thirdFullThreeBandZ3GalerkinHeatFactor244 mu h n
  let A := thirdFullThreeBandZ3GalerkinQuadratic244 s s u u n
  let B := thirdFullThreeBandZ3GalerkinQuadratic244 s s v v n
  have hfac := thirdFullThreeBand_z3GalerkinHeatFactor_bounds244 mu h hmu hh n
  have hlag := (thirdFullThreeBand_z3GalerkinHeatLag_le_clock244 mu h hmu hh n).2
  have hsplit : sigma • A - B = sigma • (A - B) + (sigma - 1) • B := by
    rw [smul_sub, sub_smul, one_smul]
    abel
  have h1 : ‖sigma • (A - B)‖ = sigma * ‖A - B‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hfac.1.le]
  have h2 : ‖(sigma - 1) • B‖ = (1 - sigma) * ‖B‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hfac.2)]
    ring
  calc
    ‖sigma • A - B‖ = ‖sigma • (A - B) + (sigma - 1) • B‖ := by rw [hsplit]
    _ ≤ ‖sigma • (A - B)‖ + ‖(sigma - 1) • B‖ := norm_add_le _ _
    _ = sigma * ‖A - B‖ + (1 - sigma) * ‖B‖ := by rw [h1, h2]
    _ ≤ ‖A - B‖ + (mu * h * ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2) * ‖B‖ := by
      apply add_le_add
      · simpa only [one_mul] using
          (mul_le_mul_of_nonneg_right hfac.2 (norm_nonneg (A - B)))
      · exact mul_le_mul_of_nonneg_right hlag (norm_nonneg _)

/-- The entire lagged complex Leray source has a pointwise bound with no
frequency-cardinality loss. The 51M source term and the 5M Laplacian term
come from the genuine projected quadratic source, not a scalar proxy. -/
theorem thirdFullThreeBand_z3GalerkinLaggedSource_mass_bound244
    (mu a t b : ℝ) (hmu : 0 ≤ mu) (hat : a ≤ t) (htb : t ≤ b)
    (s : Finset MildIndex244)
    (u : ℝ → MildIndex244 → MildBand244)
    (hHighA : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (9 / 5 : ℝ)) s (u a) ≤ 100)
    (hHighT : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (9 / 5 : ℝ)) s (u t) ≤ 100)
    (hIncrement : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (3 / 2 : ℝ)) s (fun n => u t n - u a n) ≤
      51000 * (t - a)) :
    (∑ n ∈ s,
      thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n *
        ‖(thirdFullThreeBandZ3GalerkinHeatFactor244 mu (b - t) n) •
            thirdFullThreeBandZ3GalerkinQuadratic244 s s (u t) (u t) n -
          thirdFullThreeBandZ3GalerkinQuadratic244 s s (u a) (u a) n‖) ≤
      51000000 * (t - a) + mu * 5000000 * (b - t) := by
  classical
  have hSource := thirdFullThreeBand_z3GalerkinSourceTimeVariation51000000_100Ball244
    a t s u hHighA hHighT hIncrement
  have hLaplacian := thirdFullThreeBand_z3GalerkinLaplacianSource5000000_100Ball244
    s s (u a) hHighA
  have hclock : 0 ≤ b - t := sub_nonneg.mpr htb
  have hpoint (n : MildIndex244) :
      thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n *
        ‖(thirdFullThreeBandZ3GalerkinHeatFactor244 mu (b - t) n) •
            thirdFullThreeBandZ3GalerkinQuadratic244 s s (u t) (u t) n -
          thirdFullThreeBandZ3GalerkinQuadratic244 s s (u a) (u a) n‖ ≤
      thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n *
        ‖thirdFullThreeBandZ3GalerkinQuadratic244 s s (u t) (u t) n -
          thirdFullThreeBandZ3GalerkinQuadratic244 s s (u a) (u a) n‖ +
      (mu * (b - t)) *
        (‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2 *
          thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n *
          ‖thirdFullThreeBandZ3GalerkinQuadratic244 s s (u a) (u a) n‖) := by
    have h := mul_le_mul_of_nonneg_left
      (thirdFullThreeBand_z3GalerkinLaggedSource_norm_bound244
        mu (b - t) hmu hclock s (u t) (u a) n)
      (thirdFullThreeBand_z3Weight_pos244 (Real.log (5 / 4 : ℝ)) n).le
    calc
      _ ≤ thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n *
        (‖thirdFullThreeBandZ3GalerkinQuadratic244 s s (u t) (u t) n -
          thirdFullThreeBandZ3GalerkinQuadratic244 s s (u a) (u a) n‖ +
         (mu * (b - t) * ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2) *
          ‖thirdFullThreeBandZ3GalerkinQuadratic244 s s (u a) (u a) n‖) := h
      _ = _ := by ring
  have hRaw :
      (∑ n ∈ s,
        thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n *
          ‖(thirdFullThreeBandZ3GalerkinHeatFactor244 mu (b - t) n) •
              thirdFullThreeBandZ3GalerkinQuadratic244 s s (u t) (u t) n -
            thirdFullThreeBandZ3GalerkinQuadratic244 s s (u a) (u a) n‖) ≤
      (∑ n ∈ s,
        thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n *
          ‖thirdFullThreeBandZ3GalerkinQuadratic244 s s (u t) (u t) n -
            thirdFullThreeBandZ3GalerkinQuadratic244 s s (u a) (u a) n‖) +
      (mu * (b - t)) *
        (∑ n ∈ s,
          ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2 *
            thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n *
            ‖thirdFullThreeBandZ3GalerkinQuadratic244 s s (u a) (u a) n‖) := by
    calc
      _ ≤ ∑ n ∈ s,
        (thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n *
            ‖thirdFullThreeBandZ3GalerkinQuadratic244 s s (u t) (u t) n -
              thirdFullThreeBandZ3GalerkinQuadratic244 s s (u a) (u a) n‖ +
         (mu * (b - t)) *
            (‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2 *
              thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n *
              ‖thirdFullThreeBandZ3GalerkinQuadratic244 s s (u a) (u a) n‖)) := by
        apply Finset.sum_le_sum
        intro n hn
        exact hpoint n
      _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hmuclock : 0 ≤ mu * (b - t) := mul_nonneg hmu hclock
  have hMult := mul_le_mul_of_nonneg_left hLaplacian hmuclock
  calc
    _ ≤ (∑ n ∈ s,
        thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n *
          ‖thirdFullThreeBandZ3GalerkinQuadratic244 s s (u t) (u t) n -
            thirdFullThreeBandZ3GalerkinQuadratic244 s s (u a) (u a) n‖) +
      (mu * (b - t)) *
        (∑ n ∈ s,
          ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2 *
            thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n *
            ‖thirdFullThreeBandZ3GalerkinQuadratic244 s s (u a) (u a) n‖) := hRaw
    _ ≤ 51000000 * (t - a) + (mu * (b - t)) * 5000000 :=
      add_le_add hSource hMult
    _ = _ := by ring

/-- Exact integral of the two *different* source and heat-lag clocks. -/
theorem thirdFullThreeBand_z3GalerkinDuhamelClockIntegral244
    (mu a b : ℝ) :
    (∫ t in a..b, (51000000 : ℝ) * (t - a) +
      (mu * 5000000) * (b - t)) =
    ((51000000 + mu * 5000000) / 2) * (b - a) ^ 2 := by
  have hI1 : IntervalIntegrable (fun t : ℝ => t - a) volume a b := by
    exact (by fun_prop : Continuous (fun t : ℝ => t - a)).intervalIntegrable a b
  have hI2 : IntervalIntegrable (fun t : ℝ => b - t) volume a b := by
    exact (by fun_prop : Continuous (fun t : ℝ => b - t)).intervalIntegrable a b
  have hIdInt : IntervalIntegrable (fun t : ℝ => t) volume a b :=
    continuous_id.intervalIntegrable a b
  have hV1 : (∫ t in a..b, t - a) = (b - a) ^ 2 / 2 := by
    rw [intervalIntegral.integral_sub hIdInt intervalIntegrable_const]
    simp only [integral_id, intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hV2 : (∫ t in a..b, b - t) = (b - a) ^ 2 / 2 := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hIdInt]
    simp only [integral_id, intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hScaled1 : IntervalIntegrable
      (fun t : ℝ => (51000000 : ℝ) * (t - a)) volume a b :=
    hI1.const_mul _
  have hScaled2 : IntervalIntegrable
      (fun t : ℝ => (mu * 5000000) * (b - t)) volume a b :=
    hI2.const_mul _
  rw [intervalIntegral.integral_add hScaled1 hScaled2]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [hV1, hV2]
  ring

/-- Under a finite-Galerkin Duhamel identity, the LOCAL weighted residual
is exactly the integral of the lagged-source deviation, with no artificial
per-frequency smallness or division by an old Fourier coefficient. -/
theorem thirdFullThreeBand_z3GalerkinDuhamelResidual_integral_bound244
    (mu a b : ℝ) (hab : a ≤ b)
    (s : Finset MildIndex244)
    (u : ℝ → MildIndex244 → MildBand244)
    (hIntegrable : ∀ n ∈ s,
      IntervalIntegrable (fun t : ℝ =>
        (thirdFullThreeBandZ3GalerkinHeatFactor244 mu (b - t) n) •
          thirdFullThreeBandZ3GalerkinQuadratic244 s s (u t) (u t) n)
        volume a b)
    (hDuhamel : ∀ n ∈ s,
      u b n =
        (thirdFullThreeBandZ3GalerkinHeatFactor244 mu (b - a) n) • u a n +
        ∫ t in a..b,
          (thirdFullThreeBandZ3GalerkinHeatFactor244 mu (b - t) n) •
            thirdFullThreeBandZ3GalerkinQuadratic244 s s (u t) (u t) n) :
    thirdFullThreeBandZ3GalerkinStepResidual244
      mu (b - a) (Real.log (5 / 4 : ℝ)) s (u a) (u b) ≤
    ∫ t in a..b,
      ∑ n ∈ s,
        thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n *
          ‖(thirdFullThreeBandZ3GalerkinHeatFactor244 mu (b - t) n) •
              thirdFullThreeBandZ3GalerkinQuadratic244 s s (u t) (u t) n -
            thirdFullThreeBandZ3GalerkinQuadratic244 s s (u a) (u a) n‖ := by
  classical
  let G : MildIndex244 → ℝ → MildBand244 := fun n t =>
    (thirdFullThreeBandZ3GalerkinHeatFactor244 mu (b - t) n) •
        thirdFullThreeBandZ3GalerkinQuadratic244 s s (u t) (u t) n -
      thirdFullThreeBandZ3GalerkinQuadratic244 s s (u a) (u a) n
  have hGInt : ∀ n ∈ s, IntervalIntegrable (G n) volume a b := by
    intro n hn
    exact (hIntegrable n hn).sub intervalIntegrable_const
  have hG : ∀ n ∈ s,
      u b n - thirdFullThreeBandZ3GalerkinHeatStep244 mu (b - a) s (u a) n =
        ∫ t in a..b, G n t := by
    intro n hn
    have hD := hDuhamel n hn
    have hSubtract := intervalIntegral.integral_sub (hIntegrable n hn)
      (intervalIntegrable_const : IntervalIntegrable
        (fun _t : ℝ => thirdFullThreeBandZ3GalerkinQuadratic244 s s (u a) (u a) n)
        volume a b)
    have hConst :
        (∫ _t in a..b,
          thirdFullThreeBandZ3GalerkinQuadratic244 s s (u a) (u a) n) =
        (b - a) • thirdFullThreeBandZ3GalerkinQuadratic244 s s (u a) (u a) n := by
      simp
    dsimp [G]
    rw [hSubtract, hConst]
    unfold thirdFullThreeBandZ3GalerkinHeatStep244
    rw [hD]
    abel
  have hNormInt : ∀ n ∈ s, IntervalIntegrable (fun t => ‖G n t‖) volume a b := by
    intro n hn
    exact (hGInt n hn).norm
  have hWeightedInt : ∀ n ∈ s,
      IntervalIntegrable (fun t : ℝ =>
        thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n * ‖G n t‖)
        volume a b := by
    intro n hn
    exact (hNormInt n hn).const_mul _
  unfold thirdFullThreeBandZ3GalerkinStepResidual244
  calc
    (∑ n ∈ s,
      thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n *
        ‖u b n - thirdFullThreeBandZ3GalerkinHeatStep244 mu (b - a) s (u a) n‖) ≤
      ∑ n ∈ s, thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n *
        (∫ t in a..b, ‖G n t‖) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [hG n hn]
      exact mul_le_mul_of_nonneg_left
        (intervalIntegral.norm_integral_le_integral_norm hab)
        (thirdFullThreeBand_z3Weight_pos244 _ n).le
    _ = ∑ n ∈ s, ∫ t in a..b,
        thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n * ‖G n t‖ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [intervalIntegral.integral_const_mul]
    _ = ∫ t in a..b, ∑ n ∈ s,
        thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n * ‖G n t‖ :=
      thirdFullThreeBand_z3GalerkinFiniteTimeIntegralSum244 a b s _ hWeightedInt
    _ = _ := by rfl

/-- The genuine full-source local residual has exactly the original
25,750,000 h² bound once Duhamel and the high-radius ball hold. The
coefficient and the proof contain NO finite-support cardinality factor. -/
theorem thirdFullThreeBand_z3GalerkinDuhamelResidual25750000_100Ball244
    (mu a b : ℝ) (hab : a ≤ b)
    (hmu : 0 ≤ mu) (hmuMax : mu ≤ (1 / 10 : ℝ))
    (s : Finset MildIndex244)
    (u : ℝ → MildIndex244 → MildBand244)
    (hHighBall : ∀ t ∈ Set.Icc a b,
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (9 / 5 : ℝ)) s (u t) ≤ 100)
    (hIncrements : ∀ t ∈ Set.Icc a b,
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (3 / 2 : ℝ)) s (fun n => u t n - u a n) ≤
        51000 * (t - a))
    (hIntegrable : ∀ n ∈ s,
      IntervalIntegrable (fun t : ℝ =>
        (thirdFullThreeBandZ3GalerkinHeatFactor244 mu (b - t) n) •
          thirdFullThreeBandZ3GalerkinQuadratic244 s s (u t) (u t) n)
        volume a b)
    (hDuhamel : ∀ n ∈ s,
      u b n =
        (thirdFullThreeBandZ3GalerkinHeatFactor244 mu (b - a) n) • u a n +
        ∫ t in a..b,
          (thirdFullThreeBandZ3GalerkinHeatFactor244 mu (b - t) n) •
            thirdFullThreeBandZ3GalerkinQuadratic244 s s (u t) (u t) n) :
    thirdFullThreeBandZ3GalerkinStepResidual244
      mu (b - a) (Real.log (5 / 4 : ℝ)) s (u a) (u b) ≤
      thirdFullThreeBandZ3GalerkinLocalConsistencyCap244 * (b - a) ^ 2 := by
  classical
  let f : ℝ → ℝ := fun t =>
    ∑ n ∈ s, thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n *
      ‖(thirdFullThreeBandZ3GalerkinHeatFactor244 mu (b - t) n) •
          thirdFullThreeBandZ3GalerkinQuadratic244 s s (u t) (u t) n -
        thirdFullThreeBandZ3GalerkinQuadratic244 s s (u a) (u a) n‖
  let g : ℝ → ℝ := fun t =>
    51000000 * (t - a) + (mu * 5000000) * (b - t)
  have hBase := thirdFullThreeBand_z3GalerkinDuhamelResidual_integral_bound244
    mu a b hab s u hIntegrable hDuhamel
  have hDevInt : ∀ n ∈ s, IntervalIntegrable
      (fun t : ℝ =>
        (thirdFullThreeBandZ3GalerkinHeatFactor244 mu (b - t) n) •
            thirdFullThreeBandZ3GalerkinQuadratic244 s s (u t) (u t) n -
          thirdFullThreeBandZ3GalerkinQuadratic244 s s (u a) (u a) n)
      volume a b := by
    intro n hn
    exact (hIntegrable n hn).sub intervalIntegrable_const
  have hW : ∀ n ∈ s, IntervalIntegrable (fun t : ℝ =>
      thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n *
        ‖(thirdFullThreeBandZ3GalerkinHeatFactor244 mu (b - t) n) •
            thirdFullThreeBandZ3GalerkinQuadratic244 s s (u t) (u t) n -
          thirdFullThreeBandZ3GalerkinQuadratic244 s s (u a) (u a) n‖)
      volume a b := by
    intro n hn
    exact (hDevInt n hn).norm.const_mul _
  have hFInt : IntervalIntegrable f volume a b := by
    dsimp only [f]
    have hEq :
        (∑ n ∈ s, (fun t : ℝ =>
          thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n *
            ‖(thirdFullThreeBandZ3GalerkinHeatFactor244 mu (b - t) n) •
                thirdFullThreeBandZ3GalerkinQuadratic244 s s (u t) (u t) n -
              thirdFullThreeBandZ3GalerkinQuadratic244 s s (u a) (u a) n‖)) =
        (fun t : ℝ => ∑ n ∈ s,
          thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n *
            ‖(thirdFullThreeBandZ3GalerkinHeatFactor244 mu (b - t) n) •
                thirdFullThreeBandZ3GalerkinQuadratic244 s s (u t) (u t) n -
              thirdFullThreeBandZ3GalerkinQuadratic244 s s (u a) (u a) n‖) := by
      funext t
      rw [Finset.sum_apply]
    rw [← hEq]
    exact IntervalIntegrable.sum s hW
  have hGInt : IntervalIntegrable g volume a b := by
    have hcont : Continuous (fun t : ℝ =>
        51000000 * (t - a) + (mu * 5000000) * (b - t)) := by fun_prop
    exact hcont.intervalIntegrable a b
  have hPoint : ∀ t ∈ Set.Icc a b, f t ≤ g t := by
    intro t ht
    exact thirdFullThreeBand_z3GalerkinLaggedSource_mass_bound244
      mu a t b hmu ht.1 ht.2 s u
      (hHighBall a ⟨le_rfl, hab⟩) (hHighBall t ht) (hIncrements t ht)
  have hMono : (∫ t in a..b, f t) ≤ ∫ t in a..b, g t :=
    intervalIntegral.integral_mono_on hab hFInt hGInt hPoint
  have hClock := thirdFullThreeBand_z3GalerkinDuhamelClockIntegral244 mu a b
  have hCoeff := thirdFullThreeBand_z3GalerkinLocalConsistencyCoefficient244
    mu hmu hmuMax
  have hSq : 0 ≤ (b - a) ^ 2 := sq_nonneg _
  calc
    _ ≤ ∫ t in a..b, f t := hBase
    _ ≤ ∫ t in a..b, g t := hMono
    _ = ((51000000 + mu * 5000000) / 2) * (b - a) ^ 2 := hClock
    _ ≤ thirdFullThreeBandZ3GalerkinLocalConsistencyCap244 * (b - a) ^ 2 :=
      mul_le_mul_of_nonneg_right (by
        have h : (51000000 + mu * 5000000) / 2 =
          (1000 * 51000 + mu * 5000000) / 2 := by ring
        rw [h]
        exact hCoeff) hSq


/-- Finite-mesh Galerkin balance with the LOCAL residual hypothesis
replaced by a quantified actual-Duhamel/path-ball hypothesis on every
step. All heat debts are retained; the total error is O(hMax*sum h).
There is no step-count or Galerkin-cardinality constant. -/
theorem thirdFullThreeBand_z3GalerkinDuhamelCumulativeOmesh244
    (N : ℕ) (mu hMax : ℝ)
    (hmu : 0 ≤ mu) (hmuMax : mu ≤ (1 / 10 : ℝ))
    (s : Finset MildIndex244)
    (time : ℕ → ℝ)
    (u : ℝ → MildIndex244 → MildBand244)
    (hOrdered : ∀ i, time i ≤ time (i + 1))
    (hMesh : ∀ i ∈ Finset.range N, time (i + 1) - time i ≤ hMax)
    (hHighBall : ∀ i ∈ Finset.range N, ∀ t ∈ Set.Icc (time i) (time (i + 1)),
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (9 / 5 : ℝ)) s (u t) ≤ 100)
    (hIncrements : ∀ i ∈ Finset.range N, ∀ t ∈ Set.Icc (time i) (time (i + 1)),
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (3 / 2 : ℝ)) s
        (fun n => u t n - u (time i) n) ≤
          51000 * (t - time i))
    (hIntegrable : ∀ i ∈ Finset.range N, ∀ n ∈ s,
      IntervalIntegrable (fun t : ℝ =>
        (thirdFullThreeBandZ3GalerkinHeatFactor244
          mu (time (i + 1) - t) n) •
          thirdFullThreeBandZ3GalerkinQuadratic244 s s (u t) (u t) n)
        volume (time i) (time (i + 1)))
    (hDuhamel : ∀ i ∈ Finset.range N, ∀ n ∈ s,
      u (time (i + 1)) n =
        (thirdFullThreeBandZ3GalerkinHeatFactor244
          mu (time (i + 1) - time i) n) • u (time i) n +
        ∫ t in (time i)..(time (i + 1)),
          (thirdFullThreeBandZ3GalerkinHeatFactor244
            mu (time (i + 1) - t) n) •
            thirdFullThreeBandZ3GalerkinQuadratic244 s s (u t) (u t) n) :
    thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (5 / 4 : ℝ)) s (u (time N)) +
      (∑ i ∈ Finset.range N,
        thirdFullThreeBandZ3GalerkinHeatDebt244
          mu (time (i + 1) - time i)
          (Real.log (5 / 4 : ℝ)) s (u (time i))) ≤
    thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (5 / 4 : ℝ)) s (u (time 0)) +
      (∑ i ∈ Finset.range N,
        (time (i + 1) - time i) *
          (thirdFullThreeBandZ3GalerkinWienerMass244
              (Real.log (5 / 4 : ℝ)) s (u (time i)) *
            thirdFullThreeBandZ3GalerkinWienerDerivative244
              (Real.log (5 / 4 : ℝ)) s (u (time i)))) +
      thirdFullThreeBandZ3GalerkinLocalConsistencyCap244 * hMax *
        (Finset.sum (Finset.range N) (fun i : ℕ =>
          time (i + 1) - time i)) := by
  -- Use the literal mesh and state maps: this keeps the kernel's
  -- indexed finite sums definitionally identical to the theorem target.
  have hh : ∀ i, 0 ≤ time (i + 1) - time i := by
    intro i
    exact sub_nonneg.mpr (hOrdered i)
  have hLocal : ∀ i ∈ Finset.range N,
      thirdFullThreeBandZ3GalerkinStepResidual244
        mu (time (i + 1) - time i) (Real.log (5 / 4 : ℝ)) s
        (u (time i)) (u (time (i + 1))) ≤
      thirdFullThreeBandZ3GalerkinLocalConsistencyCap244 *
        (time (i + 1) - time i) ^ 2 := by
    intro i hi
    exact thirdFullThreeBand_z3GalerkinDuhamelResidual25750000_100Ball244
      mu (time i) (time (i + 1)) (hOrdered i)
      hmu hmuMax s u (hHighBall i hi) (hIncrements i hi)
      (hIntegrable i hi) (hDuhamel i hi)
  -- The previous notation incorrectly scoped the final `- time i` outside
  -- the finite-sum binder, introducing an unintended implicit free index.
  -- The theorem statement now uses an explicit `Finset.sum` function, so
  -- the cumulative-budget result matches without rewriting or ring tactics.
  exact thirdFullThreeBand_z3GalerkinCumulativeOmeshBudget244
    N mu (Real.log (5 / 4 : ℝ))
    thirdFullThreeBandZ3GalerkinLocalConsistencyCap244 hMax
    hmu (Real.log_nonneg (by norm_num))
    (by unfold thirdFullThreeBandZ3GalerkinLocalConsistencyCap244; norm_num)
    s (fun i => time (i + 1) - time i) (fun i => u (time i))
    hh hMesh hLocal

end
end PrimeTensor.FirstMonomialTriad
