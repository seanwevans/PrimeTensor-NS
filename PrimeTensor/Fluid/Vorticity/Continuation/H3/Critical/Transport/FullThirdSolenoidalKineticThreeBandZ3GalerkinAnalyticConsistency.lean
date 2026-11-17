import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3GalerkinResidualBudget
import Mathlib.Tactic

/-!
# Cutoff-uniform analytic reserves for actual Galerkin ODE consistency

The all-degree Wiener inequalities already proved in this development
are now transferred without a finite-frequency search to the actual
three-dimensional INTEGER Fourier lattice. The exact radius ladder is
5/4 -> 3/2 -> 9/5; the second ratio is precisely 6/5, matching the
first. No mode-count or output-collision factor is introduced.

The quadratic-source variation estimate is for the ACTUAL full-output
complex Leray Galerkin source. Its pointwise polarization identity is
an EXPLICIT hypothesis, rather than a silently assumed new theorem.
For actual bilinear convolution this identity is algebraic, but that
identity is not yet formalized in this file.

The last theorems identify the quantitative ODE residual coefficient
25,750,000 for viscosity <=1/10, conditional on a Duhamel / temporal
source-variation bound. They feed it into the previously proved zero-safe
cumulative heat-debt budget. The finite-dimensional ODE solution,
temporal FTC, cutoff-uniform higher-radius ball and infinite Fourier
PDE limit are not asserted or introduced as axioms.
-/

namespace PrimeTensor.FirstMonomialTriad

noncomputable section

private abbrev AnalyticBand244 := EuclideanSpace ℂ (Fin 3)
private abbrev AnalyticIndex244 := thirdFullThreeBandZ3Index244

/-- Genuine integer l1 degree, with no real-valued rounding. -/
def thirdFullThreeBandZ3NatDegree244 (n : AnalyticIndex244) : ℕ :=
  ∑ j : Fin 3, (n j).natAbs

/-- The previous real Z3 Fourier degree is EXACTLY an integer cast. -/
theorem thirdFullThreeBand_z3Degree_eq_natCast244 (n : AnalyticIndex244) :
    thirdFullThreeBandZ3Degree244 n =
      (thirdFullThreeBandZ3NatDegree244 n : ℝ) := by
  unfold thirdFullThreeBandZ3Degree244 thirdFullThreeBandZ3NatDegree244
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    |(n j : ℝ)| = ((|(n j)| : ℤ) : ℝ) := by
      simp only [Int.cast_abs]
    _ = (((n j).natAbs : ℕ) : ℝ) := by
      simpa only [Int.cast_natCast] using
        (congrArg (fun z : ℤ => (z : ℝ))
          (Int.abs_eq_natAbs (n j)))

/-- The exponential analytic Z3 weight is the corresponding integer power. -/
theorem thirdFullThreeBand_z3Weight_log_eq_pow244
    (R : ℝ) (hR : 0 < R) (n : AnalyticIndex244) :
    thirdFullThreeBandZ3Weight244 (Real.log R) n =
      R ^ (thirdFullThreeBandZ3NatDegree244 n) := by
  rw [thirdFullThreeBandZ3Weight244,
      thirdFullThreeBand_z3Degree_eq_natCast244]
  rw [mul_comm, Real.exp_nat_mul, Real.exp_log hR]

/-- All Z3 modes (not just a bounded computer enumeration) pay ONE
frequency derivative when passing from analytic radius 5/4 to 3/2. -/
theorem thirdFullThreeBand_z3TwoRadiusDerivativeEnvelope244
    (n : AnalyticIndex244) :
    thirdFullThreeBandZ3Degree244 n *
        thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n ≤
      5 * thirdFullThreeBandZ3Weight244 (Real.log (3 / 2 : ℝ)) n := by
  rw [thirdFullThreeBand_z3Degree_eq_natCast244,
      thirdFullThreeBand_z3Weight_log_eq_pow244 (5 / 4) (by norm_num),
      thirdFullThreeBand_z3Weight_log_eq_pow244 (3 / 2) (by norm_num)]
  exact (thirdFullThreeBand_allDegreeWienerEnvelopes244
    (thirdFullThreeBandZ3NatDegree244 n)).2.1

/-- The physical Fourier Laplacian pays at most 100 units of the
5/4 -> 3/2 analytic reserve, uniformly over all Z3 modes. -/
theorem thirdFullThreeBand_z3TwoRadiusLaplacianEnvelope244
    (n : AnalyticIndex244) :
    ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2 *
        thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n ≤
      100 * thirdFullThreeBandZ3Weight244 (Real.log (3 / 2 : ℝ)) n := by
  have hn := thirdFullThreeBand_z3Laplacian_le_degreeSquare244 n
  have hweight := (thirdFullThreeBand_z3Weight_pos244
    (Real.log (5 / 4 : ℝ)) n).le
  calc
    _ ≤ (thirdFullThreeBandZ3Degree244 n) ^ 2 *
          thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n :=
        mul_le_mul_of_nonneg_right hn hweight
    _ ≤ _ := by
      rw [thirdFullThreeBand_z3Degree_eq_natCast244,
          thirdFullThreeBand_z3Weight_log_eq_pow244 (5 / 4) (by norm_num),
          thirdFullThreeBand_z3Weight_log_eq_pow244 (3 / 2) (by norm_num)]
      exact (thirdFullThreeBand_allDegreeWienerEnvelopes244
        (thirdFullThreeBandZ3NatDegree244 n)).2.2

/-- The 3/2 -> 9/5 reserve uses the SAME exact ratio 6/5.
This controls one derivative of the genuine Galerkin time vector field. -/
theorem thirdFullThreeBand_z3ThreeRadiusDerivativeEnvelope244
    (n : AnalyticIndex244) :
    thirdFullThreeBandZ3Degree244 n *
        thirdFullThreeBandZ3Weight244 (Real.log (3 / 2 : ℝ)) n ≤
      5 * thirdFullThreeBandZ3Weight244 (Real.log (9 / 5 : ℝ)) n := by
  let m := thirdFullThreeBandZ3NatDegree244 n
  have hold := (thirdFullThreeBand_allDegreeWienerEnvelopes244 m).2.1
  have hs := mul_le_mul_of_nonneg_right hold
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 6 / 5) m)
  have h15 : (5 / 4 : ℝ) ^ m * (6 / 5 : ℝ) ^ m = (3 / 2 : ℝ) ^ m := by
    rw [← mul_pow]
    norm_num
  have h18 : (3 / 2 : ℝ) ^ m * (6 / 5 : ℝ) ^ m = (9 / 5 : ℝ) ^ m := by
    rw [← mul_pow]
    norm_num
  rw [thirdFullThreeBand_z3Degree_eq_natCast244,
      thirdFullThreeBand_z3Weight_log_eq_pow244 (3 / 2) (by norm_num),
      thirdFullThreeBand_z3Weight_log_eq_pow244 (9 / 5) (by norm_num)]
  calc
    (m : ℝ) * (3 / 2 : ℝ) ^ m =
        ((m : ℝ) * (5 / 4 : ℝ) ^ m) * (6 / 5 : ℝ) ^ m := by
      rw [← h15]
      ring
    _ ≤ (5 * (3 / 2 : ℝ) ^ m) * (6 / 5 : ℝ) ^ m := hs
    _ = 5 * (9 / 5 : ℝ) ^ m := by
      rw [← h18]
      ring

/-- Two Laplacian derivatives at the middle radius cost no more than
100 times the 9/5-radius mass. -/
theorem thirdFullThreeBand_z3ThreeRadiusLaplacianEnvelope244
    (n : AnalyticIndex244) :
    ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2 *
        thirdFullThreeBandZ3Weight244 (Real.log (3 / 2 : ℝ)) n ≤
      100 * thirdFullThreeBandZ3Weight244 (Real.log (9 / 5 : ℝ)) n := by
  let m := thirdFullThreeBandZ3NatDegree244 n
  have hold := (thirdFullThreeBand_allDegreeWienerEnvelopes244 m).2.2
  have hs := mul_le_mul_of_nonneg_right hold
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 6 / 5) m)
  have h15 : (5 / 4 : ℝ) ^ m * (6 / 5 : ℝ) ^ m = (3 / 2 : ℝ) ^ m := by
    rw [← mul_pow]
    norm_num
  have h18 : (3 / 2 : ℝ) ^ m * (6 / 5 : ℝ) ^ m = (9 / 5 : ℝ) ^ m := by
    rw [← mul_pow]
    norm_num
  have hL := thirdFullThreeBand_z3Laplacian_le_degreeSquare244 n
  have hw := (thirdFullThreeBand_z3Weight_pos244
    (Real.log (3 / 2 : ℝ)) n).le
  calc
    _ ≤ (thirdFullThreeBandZ3Degree244 n) ^ 2 *
          thirdFullThreeBandZ3Weight244 (Real.log (3 / 2 : ℝ)) n :=
        mul_le_mul_of_nonneg_right hL hw
    _ = (m : ℝ) ^ 2 * (3 / 2 : ℝ) ^ m := by
      rw [thirdFullThreeBand_z3Degree_eq_natCast244,
          thirdFullThreeBand_z3Weight_log_eq_pow244 (3 / 2) (by norm_num)]
    _ = ((m : ℝ) ^ 2 * (5 / 4 : ℝ) ^ m) * (6 / 5 : ℝ) ^ m := by
      rw [← h15]
      ring
    _ ≤ (100 * (3 / 2 : ℝ) ^ m) * (6 / 5 : ℝ) ^ m := hs
    _ = 100 * thirdFullThreeBandZ3Weight244 (Real.log (9 / 5 : ℝ)) n := by
      rw [thirdFullThreeBand_z3Weight_log_eq_pow244 (9 / 5) (by norm_num)]
      rw [← h18]
      ring

/-- The finite Wiener mass is monotone in its analytic radius. -/
theorem thirdFullThreeBand_z3WienerMass_radius_mono244
    (r R : ℝ) (hRadius : r ≤ R)
    (s : Finset AnalyticIndex244) (u : AnalyticIndex244 → AnalyticBand244) :
    thirdFullThreeBandZ3GalerkinWienerMass244 r s u ≤
      thirdFullThreeBandZ3GalerkinWienerMass244 R s u := by
  classical
  unfold thirdFullThreeBandZ3GalerkinWienerMass244
  apply Finset.sum_le_sum
  intro n hn
  have hdeg := thirdFullThreeBand_z3Degree_nonneg244 n
  have hw : thirdFullThreeBandZ3Weight244 r n ≤
      thirdFullThreeBandZ3Weight244 R n := by
    unfold thirdFullThreeBandZ3Weight244
    exact Real.exp_le_exp.mpr (by
      nlinarith [mul_nonneg (sub_nonneg.mpr hRadius) hdeg])
  exact mul_le_mul_of_nonneg_right hw (norm_nonneg (u n))

/-- If the larger radius absorbs one full lattice derivative, then
all finite Galerkin derivative sums obey the same bound. -/
theorem thirdFullThreeBand_z3WienerDerivative_reserved244
    (r R C : ℝ) (hC : 0 ≤ C)
    (s : Finset AnalyticIndex244) (u : AnalyticIndex244 → AnalyticBand244)
    (hReserve : ∀ n ∈ s,
      thirdFullThreeBandZ3Degree244 n * thirdFullThreeBandZ3Weight244 r n ≤
        C * thirdFullThreeBandZ3Weight244 R n) :
    thirdFullThreeBandZ3GalerkinWienerDerivative244 r s u ≤
      C * thirdFullThreeBandZ3GalerkinWienerMass244 R s u := by
  classical
  unfold thirdFullThreeBandZ3GalerkinWienerDerivative244
    thirdFullThreeBandZ3GalerkinWienerMass244
  calc
    _ ≤ ∑ n ∈ s, C * (thirdFullThreeBandZ3Weight244 R n * ‖u n‖) := by
      apply Finset.sum_le_sum
      intro n hn
      have h := mul_le_mul_of_nonneg_right (hReserve n hn) (norm_nonneg (u n))
      calc
        _ = (thirdFullThreeBandZ3Degree244 n *
            thirdFullThreeBandZ3Weight244 r n) * ‖u n‖ := by ring
        _ ≤ (C * thirdFullThreeBandZ3Weight244 R n) * ‖u n‖ := h
        _ = C * (thirdFullThreeBandZ3Weight244 R n * ‖u n‖) := by ring
    _ = _ := by rw [Finset.mul_sum]

/-- The exact full-output quadratic polarization has a support-independent
weighted norm estimate; all newly created and colliding modes are included. -/
theorem thirdFullThreeBand_z3PolarizedSource_mass_bound244
    (r : ℝ) (hr : 0 ≤ r)
    (outputs s : Finset AnalyticIndex244)
    (u v : AnalyticIndex244 → AnalyticBand244) :
    (∑ n ∈ outputs, thirdFullThreeBandZ3Weight244 r n *
      ‖thirdFullThreeBandZ3GalerkinQuadratic244 s s
          (fun p => u p - v p) u n +
        thirdFullThreeBandZ3GalerkinQuadratic244 s s
          v (fun p => u p - v p) n‖) ≤
    thirdFullThreeBandZ3GalerkinWienerMass244 r s (fun p => u p - v p) *
      thirdFullThreeBandZ3GalerkinWienerDerivative244 r s u +
    thirdFullThreeBandZ3GalerkinWienerMass244 r s v *
      thirdFullThreeBandZ3GalerkinWienerDerivative244 r s (fun p => u p - v p) := by
  classical
  have hA := thirdFullThreeBand_z3GalerkinAllOutputWienerBound244
    r hr outputs s s (fun p => u p - v p) u
  have hB := thirdFullThreeBand_z3GalerkinAllOutputWienerBound244
    r hr outputs s s v (fun p => u p - v p)
  have hpoint (n : AnalyticIndex244) :
      thirdFullThreeBandZ3Weight244 r n *
        ‖thirdFullThreeBandZ3GalerkinQuadratic244 s s
            (fun p => u p - v p) u n +
          thirdFullThreeBandZ3GalerkinQuadratic244 s s
            v (fun p => u p - v p) n‖ ≤
      thirdFullThreeBandZ3Weight244 r n *
        ‖thirdFullThreeBandZ3GalerkinQuadratic244 s s
            (fun p => u p - v p) u n‖ +
      thirdFullThreeBandZ3Weight244 r n *
        ‖thirdFullThreeBandZ3GalerkinQuadratic244 s s
            v (fun p => u p - v p) n‖ := by
    have hnorm := norm_add_le
      (thirdFullThreeBandZ3GalerkinQuadratic244 s s (fun p => u p - v p) u n)
      (thirdFullThreeBandZ3GalerkinQuadratic244 s s v (fun p => u p - v p) n)
    have h := mul_le_mul_of_nonneg_left hnorm
      (thirdFullThreeBand_z3Weight_pos244 r n).le
    calc
      _ ≤ thirdFullThreeBandZ3Weight244 r n *
        (‖thirdFullThreeBandZ3GalerkinQuadratic244 s s
            (fun p => u p - v p) u n‖ +
          ‖thirdFullThreeBandZ3GalerkinQuadratic244 s s
            v (fun p => u p - v p) n‖) := h
      _ = _ := by ring
  calc
    _ ≤ (∑ n ∈ outputs, thirdFullThreeBandZ3Weight244 r n *
        ‖thirdFullThreeBandZ3GalerkinQuadratic244 s s
            (fun p => u p - v p) u n‖) +
        (∑ n ∈ outputs, thirdFullThreeBandZ3Weight244 r n *
          ‖thirdFullThreeBandZ3GalerkinQuadratic244 s s
            v (fun p => u p - v p) n‖) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro n hn
      exact hpoint n
    _ ≤ _ := add_le_add hA hB

/-- An explicit polarization identity plus the two-radius derivative
reserve converts the genuine quadratic source difference into a Lipschitz
bound that has NO Galerkin cardinality dependence. -/
theorem thirdFullThreeBand_z3SourceDifference_twoRadius244
    (r R : ℝ) (hr : 0 ≤ r) (hRadius : r ≤ R)
    (outputs s : Finset AnalyticIndex244)
    (u v : AnalyticIndex244 → AnalyticBand244)
    (hReserve : ∀ n ∈ s,
      thirdFullThreeBandZ3Degree244 n * thirdFullThreeBandZ3Weight244 r n ≤
        5 * thirdFullThreeBandZ3Weight244 R n)
    (hPolar : ∀ n ∈ outputs,
      thirdFullThreeBandZ3GalerkinQuadratic244 s s u u n -
        thirdFullThreeBandZ3GalerkinQuadratic244 s s v v n =
        thirdFullThreeBandZ3GalerkinQuadratic244 s s
          (fun p => u p - v p) u n +
        thirdFullThreeBandZ3GalerkinQuadratic244 s s
          v (fun p => u p - v p) n) :
    (∑ n ∈ outputs, thirdFullThreeBandZ3Weight244 r n *
       ‖thirdFullThreeBandZ3GalerkinQuadratic244 s s u u n -
         thirdFullThreeBandZ3GalerkinQuadratic244 s s v v n‖) ≤
      5 * thirdFullThreeBandZ3GalerkinWienerMass244 R s (fun p => u p - v p) *
        (thirdFullThreeBandZ3GalerkinWienerMass244 R s u +
         thirdFullThreeBandZ3GalerkinWienerMass244 R s v) := by
  classical
  have hSource := thirdFullThreeBand_z3PolarizedSource_mass_bound244 r hr outputs s u v
  have hDU := thirdFullThreeBand_z3WienerDerivative_reserved244 r R 5 (by norm_num) s u hReserve
  have hDD := thirdFullThreeBand_z3WienerDerivative_reserved244 r R 5 (by norm_num)
    s (fun p => u p - v p) hReserve
  have hWU := thirdFullThreeBand_z3WienerMass_radius_mono244 r R hRadius s (fun p => u p - v p)
  have hWV := thirdFullThreeBand_z3WienerMass_radius_mono244 r R hRadius s v
  have hposU : 0 ≤ thirdFullThreeBandZ3GalerkinWienerMass244 R s (fun p => u p - v p) := by
    unfold thirdFullThreeBandZ3GalerkinWienerMass244
    exact Finset.sum_nonneg (by
      intro n hn
      exact mul_nonneg (thirdFullThreeBand_z3Weight_pos244 R n).le (norm_nonneg _))
  have hposV : 0 ≤ thirdFullThreeBandZ3GalerkinWienerDerivative244 r s u := by
    unfold thirdFullThreeBandZ3GalerkinWienerDerivative244
    exact Finset.sum_nonneg (by
      intro n hn
      exact mul_nonneg (mul_nonneg
        (thirdFullThreeBand_z3Weight_pos244 r n).le
        (thirdFullThreeBand_z3Degree_nonneg244 n)) (norm_nonneg _))
  have hposR : 0 ≤ thirdFullThreeBandZ3GalerkinWienerMass244 R s v := by
    unfold thirdFullThreeBandZ3GalerkinWienerMass244
    exact Finset.sum_nonneg (by
      intro n hn
      exact mul_nonneg (thirdFullThreeBand_z3Weight_pos244 R n).le (norm_nonneg _))
  have hFirst :
      thirdFullThreeBandZ3GalerkinWienerMass244 r s (fun p => u p - v p) *
        thirdFullThreeBandZ3GalerkinWienerDerivative244 r s u ≤
      thirdFullThreeBandZ3GalerkinWienerMass244 R s (fun p => u p - v p) *
        (5 * thirdFullThreeBandZ3GalerkinWienerMass244 R s u) := by
    exact (mul_le_mul_of_nonneg_right hWU hposV).trans
      (mul_le_mul_of_nonneg_left hDU hposU)
  have hSecond :
      thirdFullThreeBandZ3GalerkinWienerMass244 r s v *
        thirdFullThreeBandZ3GalerkinWienerDerivative244 r s (fun p => u p - v p) ≤
      thirdFullThreeBandZ3GalerkinWienerMass244 R s v *
        (5 * thirdFullThreeBandZ3GalerkinWienerMass244 R s (fun p => u p - v p)) := by
    have hposD : 0 ≤ thirdFullThreeBandZ3GalerkinWienerDerivative244
        r s (fun p => u p - v p) := by
      unfold thirdFullThreeBandZ3GalerkinWienerDerivative244
      exact Finset.sum_nonneg (by
        intro n hn
        exact mul_nonneg (mul_nonneg
          (thirdFullThreeBand_z3Weight_pos244 r n).le
          (thirdFullThreeBand_z3Degree_nonneg244 n)) (norm_nonneg _))
    exact (mul_le_mul_of_nonneg_right hWV hposD).trans
      (mul_le_mul_of_nonneg_left hDD hposR)
  calc
    _ = (∑ n ∈ outputs, thirdFullThreeBandZ3Weight244 r n *
       ‖thirdFullThreeBandZ3GalerkinQuadratic244 s s
            (fun p => u p - v p) u n +
         thirdFullThreeBandZ3GalerkinQuadratic244 s s
            v (fun p => u p - v p) n‖) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [hPolar n hn]
    _ ≤ _ := by
      calc
        _ ≤ thirdFullThreeBandZ3GalerkinWienerMass244 r s (fun p => u p - v p) *
              thirdFullThreeBandZ3GalerkinWienerDerivative244 r s u +
            thirdFullThreeBandZ3GalerkinWienerMass244 r s v *
              thirdFullThreeBandZ3GalerkinWienerDerivative244 r s (fun p => u p - v p) := hSource
        _ ≤ thirdFullThreeBandZ3GalerkinWienerMass244 R s (fun p => u p - v p) *
              (5 * thirdFullThreeBandZ3GalerkinWienerMass244 R s u) +
            thirdFullThreeBandZ3GalerkinWienerMass244 R s v *
              (5 * thirdFullThreeBandZ3GalerkinWienerMass244 R s (fun p => u p - v p)) :=
          add_le_add hFirst hSecond
        _ = _ := by ring

/-- Under a common 100-ball at the higher radius, the exact nonlinear
source is 1000-Lipschitz with respect to the higher Wiener distance. -/
theorem thirdFullThreeBand_z3SourceDifference_100Ball244
    (r R : ℝ) (hr : 0 ≤ r) (hRadius : r ≤ R)
    (outputs s : Finset AnalyticIndex244)
    (u v : AnalyticIndex244 → AnalyticBand244)
    (hReserve : ∀ n ∈ s,
      thirdFullThreeBandZ3Degree244 n * thirdFullThreeBandZ3Weight244 r n ≤
        5 * thirdFullThreeBandZ3Weight244 R n)
    (hPolar : ∀ n ∈ outputs,
      thirdFullThreeBandZ3GalerkinQuadratic244 s s u u n -
        thirdFullThreeBandZ3GalerkinQuadratic244 s s v v n =
        thirdFullThreeBandZ3GalerkinQuadratic244 s s
          (fun p => u p - v p) u n +
        thirdFullThreeBandZ3GalerkinQuadratic244 s s
          v (fun p => u p - v p) n)
    (hU : thirdFullThreeBandZ3GalerkinWienerMass244 R s u ≤ 100)
    (hV : thirdFullThreeBandZ3GalerkinWienerMass244 R s v ≤ 100) :
    (∑ n ∈ outputs, thirdFullThreeBandZ3Weight244 r n *
       ‖thirdFullThreeBandZ3GalerkinQuadratic244 s s u u n -
         thirdFullThreeBandZ3GalerkinQuadratic244 s s v v n‖) ≤
      1000 * thirdFullThreeBandZ3GalerkinWienerMass244 R s
        (fun p => u p - v p) := by
  have h := thirdFullThreeBand_z3SourceDifference_twoRadius244
    r R hr hRadius outputs s u v hReserve hPolar
  have hD : 0 ≤ thirdFullThreeBandZ3GalerkinWienerMass244 R s
      (fun p => u p - v p) := by
    unfold thirdFullThreeBandZ3GalerkinWienerMass244
    exact Finset.sum_nonneg (by
      intro n hn
      exact mul_nonneg (thirdFullThreeBand_z3Weight_pos244 R n).le (norm_nonneg _))
  have hB : thirdFullThreeBandZ3GalerkinWienerMass244 R s u +
      thirdFullThreeBandZ3GalerkinWienerMass244 R s v ≤ 200 := by linarith
  have hBound := mul_le_mul_of_nonneg_left hB (mul_nonneg (by norm_num : (0:ℝ) ≤ 5) hD)
  nlinarith [h, hBound]

/-- Cutoff-independent exponential-Euler local residual coefficient when
mu <= 1/10, the middle-radius source moves at most 51,000 per unit time
in W_(3/2), and its Laplacian reserve is at most 5,000,000. -/
def thirdFullThreeBandZ3GalerkinLocalConsistencyCap244 : ℝ := 25750000

theorem thirdFullThreeBand_z3GalerkinLocalConsistencyCoefficient244
    (mu : ℝ) (hmu : 0 ≤ mu) (hmuMax : mu ≤ (1 / 10 : ℝ)) :
    (1000 * 51000 + mu * 5000000) / 2 ≤
      thirdFullThreeBandZ3GalerkinLocalConsistencyCap244 := by
  unfold thirdFullThreeBandZ3GalerkinLocalConsistencyCap244
  nlinarith

/-- Applying the genuine ODE residual estimate, if supplied by a Duhamel
path proof, gives an explicit O(hMax) finite Galerkin budget. The local
ODE estimate is a visible hypothesis; it is not silently asserted. -/
theorem thirdFullThreeBand_z3GalerkinExplicitOmeshBudget244
    (N : ℕ) (mu r hMax : ℝ)
    (hmu : 0 ≤ mu) (hmuMax : mu ≤ (1 / 10 : ℝ))
    (hr : 0 ≤ r)
    (s : Finset AnalyticIndex244)
    (h : ℕ → ℝ)
    (u : ℕ → AnalyticIndex244 → AnalyticBand244)
    (hh : ∀ i, 0 ≤ h i)
    (hMesh : ∀ i ∈ Finset.range N, h i ≤ hMax)
    (hLocalODE : ∀ i ∈ Finset.range N,
      thirdFullThreeBandZ3GalerkinStepResidual244
        mu (h i) r s (u i) (u (i + 1)) ≤
      ((1000 * 51000 + mu * 5000000) / 2) * (h i) ^ 2) :
    thirdFullThreeBandZ3GalerkinWienerMass244 r s (u N) +
      (∑ i ∈ Finset.range N,
        thirdFullThreeBandZ3GalerkinHeatDebt244 mu (h i) r s (u i)) ≤
    thirdFullThreeBandZ3GalerkinWienerMass244 r s (u 0) +
      (∑ i ∈ Finset.range N,
        h i * (thirdFullThreeBandZ3GalerkinWienerMass244 r s (u i) *
          thirdFullThreeBandZ3GalerkinWienerDerivative244 r s (u i))) +
      thirdFullThreeBandZ3GalerkinLocalConsistencyCap244 * hMax *
        (∑ i ∈ Finset.range N, h i) := by
  have hC := thirdFullThreeBand_z3GalerkinLocalConsistencyCoefficient244
    mu hmu hmuMax
  apply thirdFullThreeBand_z3GalerkinCumulativeOmeshBudget244
    N mu r thirdFullThreeBandZ3GalerkinLocalConsistencyCap244 hMax
    hmu hr (by unfold thirdFullThreeBandZ3GalerkinLocalConsistencyCap244; norm_num)
    s h u hh hMesh
  intro i hi
  have hp : 0 ≤ (h i) ^ 2 := sq_nonneg _
  exact (hLocalODE i hi).trans (mul_le_mul_of_nonneg_right hC hp)

end
end PrimeTensor.FirstMonomialTriad
