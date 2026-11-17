import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3GalerkinAnalyticConsistency
import Mathlib.Tactic

/-!
# Exact Fourier polarization and the genuine Galerkin NS vector-field speed

We close the explicit polarization hypothesis in the preceding three-radius
analytic consistency module. The actual ordered complex Fourier transport
is bilinear in its two coefficient inputs, even though its norm is not.
Finite, collision-sensitive output sums inherit this exact bilinearity.

Therefore the previous source-difference 1000-Lipschitz estimate becomes an
UNCONDITIONAL theorem of the actual finite Galerkin convolution (under its
quantified analytic 100-ball assumptions). Neither a six-mode closure nor a
Fourier-output cardinality factor is used.

We also define the actual viscosity-plus-Leray finite-dimensional Galerkin
vector field. Its W_(3/2) speed is at most 51000, for every finite support,
provided W_(9/5) <= 100 and 0 <= viscosity <= 1/10. In particular the ODE
speed ceiling that motivated the previous 25750000 consistency constant is
now proved directly from the same spatial nonlinear source. This is still
NOT the Galerkin ODE flow or a theorem about its temporal FTC/Duhamel
formula; no time derivative or PDE existence is asserted here.
-/

namespace PrimeTensor.FirstMonomialTriad

noncomputable section

private abbrev Z3ExactBand244 := EuclideanSpace ℂ (Fin 3)
private abbrev Z3ExactIndex244 := thirdFullThreeBandZ3Index244

/-- Exact complex linearity in the advecting amplitude. -/
theorem thirdFullThreeBand_z3ComplexTransport_sub_left244
    (n q : Z3ExactIndex244) (u v w : Z3ExactBand244) :
    thirdFullThreeBandZ3ComplexTransport244 n q (u - v) w =
      thirdFullThreeBandZ3ComplexTransport244 n q u w -
        thirdFullThreeBandZ3ComplexTransport244 n q v w := by
  unfold thirdFullThreeBandZ3ComplexTransport244
  rw [inner_sub_right, mul_sub, sub_smul, map_sub]

/-- Exact complex linearity in the transported amplitude. -/
theorem thirdFullThreeBand_z3ComplexTransport_sub_right244
    (n q : Z3ExactIndex244) (u v w : Z3ExactBand244) :
    thirdFullThreeBandZ3ComplexTransport244 n q u (v - w) =
      thirdFullThreeBandZ3ComplexTransport244 n q u v -
        thirdFullThreeBandZ3ComplexTransport244 n q u w := by
  unfold thirdFullThreeBandZ3ComplexTransport244
  rw [smul_sub, map_sub]

/-- The actual COMPLETE ordered Galerkin convolution is left-additive.
The proof keeps both finite input sums and their output collision tests. -/
theorem thirdFullThreeBand_z3GalerkinQuadratic_sub_left244
    (s t : Finset Z3ExactIndex244)
    (u v w : Z3ExactIndex244 → Z3ExactBand244)
    (n : Z3ExactIndex244) :
    thirdFullThreeBandZ3GalerkinQuadratic244 s t (fun p => u p - v p) w n =
      thirdFullThreeBandZ3GalerkinQuadratic244 s t u w n -
        thirdFullThreeBandZ3GalerkinQuadratic244 s t v w n := by
  classical
  unfold thirdFullThreeBandZ3GalerkinQuadratic244
  calc
    (∑ p ∈ s, ∑ q ∈ t,
        if p + q = n then
          thirdFullThreeBandZ3ComplexTransport244 n q (u p - v p) (w q)
        else 0) =
      ∑ p ∈ s, ∑ q ∈ t,
        ((if p + q = n then
            thirdFullThreeBandZ3ComplexTransport244 n q (u p) (w q)
          else 0) -
         (if p + q = n then
            thirdFullThreeBandZ3ComplexTransport244 n q (v p) (w q)
          else 0)) := by
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.sum_congr rfl
        intro q hq
        by_cases h : p + q = n
        · simp [h, thirdFullThreeBand_z3ComplexTransport_sub_left244]
        · simp [h]
    _ = _ := by simp only [Finset.sum_sub_distrib]

/-- The same complete convolution is right-additive, including all
ordered input pairs and all coincident output frequencies. -/
theorem thirdFullThreeBand_z3GalerkinQuadratic_sub_right244
    (s t : Finset Z3ExactIndex244)
    (u v w : Z3ExactIndex244 → Z3ExactBand244)
    (n : Z3ExactIndex244) :
    thirdFullThreeBandZ3GalerkinQuadratic244 s t u (fun q => v q - w q) n =
      thirdFullThreeBandZ3GalerkinQuadratic244 s t u v n -
        thirdFullThreeBandZ3GalerkinQuadratic244 s t u w n := by
  classical
  unfold thirdFullThreeBandZ3GalerkinQuadratic244
  calc
    (∑ p ∈ s, ∑ q ∈ t,
        if p + q = n then
          thirdFullThreeBandZ3ComplexTransport244 n q (u p) (v q - w q)
        else 0) =
      ∑ p ∈ s, ∑ q ∈ t,
        ((if p + q = n then
            thirdFullThreeBandZ3ComplexTransport244 n q (u p) (v q)
          else 0) -
         (if p + q = n then
            thirdFullThreeBandZ3ComplexTransport244 n q (u p) (w q)
          else 0)) := by
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.sum_congr rfl
        intro q hq
        by_cases h : p + q = n
        · simp [h, thirdFullThreeBand_z3ComplexTransport_sub_right244]
        · simp [h]
    _ = _ := by simp only [Finset.sum_sub_distrib]

/-- The missing algebraic proof boundary of the three-radius module,
now discharged for the ACTUAL complex full-output Leray convolution. -/
theorem thirdFullThreeBand_z3GalerkinQuadratic_exactPolarization244
    (s : Finset Z3ExactIndex244)
    (u v : Z3ExactIndex244 → Z3ExactBand244)
    (n : Z3ExactIndex244) :
    thirdFullThreeBandZ3GalerkinQuadratic244 s s u u n -
      thirdFullThreeBandZ3GalerkinQuadratic244 s s v v n =
    thirdFullThreeBandZ3GalerkinQuadratic244 s s (fun p => u p - v p) u n +
      thirdFullThreeBandZ3GalerkinQuadratic244 s s v (fun q => u q - v q) n := by
  have hLeft := thirdFullThreeBand_z3GalerkinQuadratic_sub_left244 s s u v u n
  have hRight := thirdFullThreeBand_z3GalerkinQuadratic_sub_right244 s s v u v n
  calc
    _ = (thirdFullThreeBandZ3GalerkinQuadratic244 s s u u n -
         thirdFullThreeBandZ3GalerkinQuadratic244 s s v u n) +
        (thirdFullThreeBandZ3GalerkinQuadratic244 s s v u n -
         thirdFullThreeBandZ3GalerkinQuadratic244 s s v v n) := by abel
    _ = _ := by rw [hLeft, hRight]

/-- The genuine quadratic source difference is 1000-Lipschitz between
W_(9/5)-bounded states, measured at the intermediate radius 3/2.
There is NO polarization hypothesis and NO frequency cutoff constant. -/
theorem thirdFullThreeBand_z3GalerkinSourceDiff_1000_middle244
    (outputs s : Finset Z3ExactIndex244)
    (u v : Z3ExactIndex244 → Z3ExactBand244)
    (hU : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (9 / 5 : ℝ)) s u ≤ 100)
    (hV : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (9 / 5 : ℝ)) s v ≤ 100) :
    (∑ n ∈ outputs,
      thirdFullThreeBandZ3Weight244 (Real.log (3 / 2 : ℝ)) n *
        ‖thirdFullThreeBandZ3GalerkinQuadratic244 s s u u n -
          thirdFullThreeBandZ3GalerkinQuadratic244 s s v v n‖) ≤
      1000 * thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (9 / 5 : ℝ)) s (fun p => u p - v p) := by
  apply thirdFullThreeBand_z3SourceDifference_100Ball244
    (Real.log (3 / 2 : ℝ)) (Real.log (9 / 5 : ℝ))
    (Real.log_nonneg (by norm_num))
    (Real.log_le_log (by norm_num) (by norm_num))
    outputs s u v
    (by intro n hn; exact thirdFullThreeBand_z3ThreeRadiusDerivativeEnvelope244 n)
    (by intro n hn; exact thirdFullThreeBand_z3GalerkinQuadratic_exactPolarization244 s u v n)
    hU hV

/-- The analogous unconditional Lipschitz estimate for 5/4 -> 3/2. -/
theorem thirdFullThreeBand_z3GalerkinSourceDiff_1000_lower244
    (outputs s : Finset Z3ExactIndex244)
    (u v : Z3ExactIndex244 → Z3ExactBand244)
    (hU : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (3 / 2 : ℝ)) s u ≤ 100)
    (hV : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (3 / 2 : ℝ)) s v ≤ 100) :
    (∑ n ∈ outputs,
      thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n *
        ‖thirdFullThreeBandZ3GalerkinQuadratic244 s s u u n -
          thirdFullThreeBandZ3GalerkinQuadratic244 s s v v n‖) ≤
      1000 * thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (3 / 2 : ℝ)) s (fun p => u p - v p) := by
  apply thirdFullThreeBand_z3SourceDifference_100Ball244
    (Real.log (5 / 4 : ℝ)) (Real.log (3 / 2 : ℝ))
    (Real.log_nonneg (by norm_num))
    (Real.log_le_log (by norm_num) (by norm_num))
    outputs s u v
    (by intro n hn; exact thirdFullThreeBand_z3TwoRadiusDerivativeEnvelope244 n)
    (by intro n hn; exact thirdFullThreeBand_z3GalerkinQuadratic_exactPolarization244 s u v n)
    hU hV

/-- The genuine positive Laplacian Fourier cost of a finite state. -/
def thirdFullThreeBandZ3GalerkinLaplacianWiener244
    (r : ℝ) (s : Finset Z3ExactIndex244)
    (u : Z3ExactIndex244 → Z3ExactBand244) : ℝ :=
  ∑ n ∈ s, thirdFullThreeBandZ3Weight244 r n *
      (‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2 * ‖u n‖)

/-- Two physical derivatives cost at most 100 units of the analytic
3/2 -> 9/5 reserve, for EVERY finite Galerkin set. -/
theorem thirdFullThreeBand_z3GalerkinLaplacianWiener_reserved244
    (s : Finset Z3ExactIndex244)
    (u : Z3ExactIndex244 → Z3ExactBand244) :
    thirdFullThreeBandZ3GalerkinLaplacianWiener244
      (Real.log (3 / 2 : ℝ)) s u ≤
      100 * thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (9 / 5 : ℝ)) s u := by
  classical
  unfold thirdFullThreeBandZ3GalerkinLaplacianWiener244
  calc
    _ ≤ ∑ n ∈ s, 100 *
        (thirdFullThreeBandZ3Weight244 (Real.log (9 / 5 : ℝ)) n * ‖u n‖) := by
      apply Finset.sum_le_sum
      intro n hn
      have h := mul_le_mul_of_nonneg_right
        (thirdFullThreeBand_z3ThreeRadiusLaplacianEnvelope244 n)
        (norm_nonneg (u n))
      calc
        _ = (‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2 *
          thirdFullThreeBandZ3Weight244 (Real.log (3 / 2 : ℝ)) n) * ‖u n‖ := by ring
        _ ≤ (100 * thirdFullThreeBandZ3Weight244
            (Real.log (9 / 5 : ℝ)) n) * ‖u n‖ := h
        _ = _ := by ring
    _ = _ := by
      unfold thirdFullThreeBandZ3GalerkinWienerMass244
      rw [Finset.mul_sum]

/-- The actual unforced Navier--Stokes Galerkin Fourier vector field:
heat Laplacian damping plus the COMPLETE complex Leray convolution. -/
def thirdFullThreeBandZ3GalerkinNSField244
    (mu : ℝ) (s : Finset Z3ExactIndex244)
    (u : Z3ExactIndex244 → Z3ExactBand244)
    (n : Z3ExactIndex244) : Z3ExactBand244 :=
  (-(mu * ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2)) • u n +
    thirdFullThreeBandZ3GalerkinQuadratic244 s s u u n

/-- The Galerkin vector-field speed is bounded by its genuine heat
contribution and the complete projected W*D source, with coefficient one. -/
theorem thirdFullThreeBand_z3GalerkinNSField_mass_bound244
    (mu r : ℝ) (hmu : 0 ≤ mu) (hr : 0 ≤ r)
    (s : Finset Z3ExactIndex244)
    (u : Z3ExactIndex244 → Z3ExactBand244) :
    thirdFullThreeBandZ3GalerkinWienerMass244 r s
      (thirdFullThreeBandZ3GalerkinNSField244 mu s u) ≤
    mu * thirdFullThreeBandZ3GalerkinLaplacianWiener244 r s u +
      thirdFullThreeBandZ3GalerkinWienerMass244 r s u *
        thirdFullThreeBandZ3GalerkinWienerDerivative244 r s u := by
  classical
  have hpoint (n : Z3ExactIndex244) :
      thirdFullThreeBandZ3Weight244 r n *
        ‖thirdFullThreeBandZ3GalerkinNSField244 mu s u n‖ ≤
      mu * (thirdFullThreeBandZ3Weight244 r n *
        (‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2 * ‖u n‖)) +
      thirdFullThreeBandZ3Weight244 r n *
        ‖thirdFullThreeBandZ3GalerkinQuadratic244 s s u u n‖ := by
    have hmul : 0 ≤ mu * ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2 :=
      mul_nonneg hmu (sq_nonneg _)
    have hnorm :
        ‖(-(mu * ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2)) • u n‖ =
          (mu * ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2) * ‖u n‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hmul]
    calc
      _ ≤ thirdFullThreeBandZ3Weight244 r n *
        (‖(-(mu * ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2)) • u n‖ +
          ‖thirdFullThreeBandZ3GalerkinQuadratic244 s s u u n‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _)
          (thirdFullThreeBand_z3Weight_pos244 r n).le
      _ = _ := by rw [hnorm]; ring
  have hQ := thirdFullThreeBand_z3GalerkinAllOutputWienerBound244
    r hr s s s u u
  unfold thirdFullThreeBandZ3GalerkinWienerMass244
    thirdFullThreeBandZ3GalerkinLaplacianWiener244
  calc
    _ ≤ ∑ n ∈ s,
        (mu * (thirdFullThreeBandZ3Weight244 r n *
          (‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2 * ‖u n‖)) +
        thirdFullThreeBandZ3Weight244 r n *
          ‖thirdFullThreeBandZ3GalerkinQuadratic244 s s u u n‖) := by
        apply Finset.sum_le_sum
        intro n hn
        exact hpoint n
    _ = mu * (∑ n ∈ s, thirdFullThreeBandZ3Weight244 r n *
            (‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2 * ‖u n‖)) +
        (∑ n ∈ s, thirdFullThreeBandZ3Weight244 r n *
          ‖thirdFullThreeBandZ3GalerkinQuadratic244 s s u u n‖) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := add_le_add_right hQ _

/-- The actual finite Galerkin Navier--Stokes vector field has a
SUPPORT-INDEPENDENT speed <=51000 in W_(3/2), under W_(9/5)<=100 and
0<=mu<=1/10. The nonlinearity uses every ordered complex Leray pair. -/
theorem thirdFullThreeBand_z3GalerkinNSField_speed51000_100Ball244
    (mu : ℝ) (hmu : 0 ≤ mu) (hmuMax : mu ≤ (1 / 10 : ℝ))
    (s : Finset Z3ExactIndex244)
    (u : Z3ExactIndex244 → Z3ExactBand244)
    (hU : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (9 / 5 : ℝ)) s u ≤ 100) :
    thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (3 / 2 : ℝ)) s
      (thirdFullThreeBandZ3GalerkinNSField244 mu s u) ≤ 51000 := by
  have hr : 0 ≤ Real.log (3 / 2 : ℝ) := Real.log_nonneg (by norm_num)
  have hRadius : Real.log (3 / 2 : ℝ) ≤ Real.log (9 / 5 : ℝ) :=
    Real.log_le_log (by norm_num) (by norm_num)
  have hMass := thirdFullThreeBand_z3WienerMass_radius_mono244
    _ _ hRadius s u
  have hDerivative := thirdFullThreeBand_z3WienerDerivative_reserved244
    _ _ 5 (by norm_num) s u
    (by intro n hn; exact thirdFullThreeBand_z3ThreeRadiusDerivativeEnvelope244 n)
  have hLaplacian := thirdFullThreeBand_z3GalerkinLaplacianWiener_reserved244 s u
  have hMassCap : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (3 / 2 : ℝ)) s u ≤ 100 := hMass.trans hU
  have hDerCap : thirdFullThreeBandZ3GalerkinWienerDerivative244
      (Real.log (3 / 2 : ℝ)) s u ≤ 500 := by
    have h := mul_le_mul_of_nonneg_left hU (by norm_num : (0 : ℝ) ≤ 5)
    linarith
  have hLapCap : thirdFullThreeBandZ3GalerkinLaplacianWiener244
      (Real.log (3 / 2 : ℝ)) s u ≤ 10000 := by
    have h := mul_le_mul_of_nonneg_left hU (by norm_num : (0 : ℝ) ≤ 100)
    linarith
  have hDnonneg : 0 ≤ thirdFullThreeBandZ3GalerkinWienerDerivative244
      (Real.log (3 / 2 : ℝ)) s u := by
    unfold thirdFullThreeBandZ3GalerkinWienerDerivative244
    apply Finset.sum_nonneg
    intro n hn
    exact mul_nonneg
      (mul_nonneg (thirdFullThreeBand_z3Weight_pos244 _ _).le
        (thirdFullThreeBand_z3Degree_nonneg244 n)) (norm_nonneg _)
  have hProd :
      thirdFullThreeBandZ3GalerkinWienerMass244 (Real.log (3 / 2 : ℝ)) s u *
        thirdFullThreeBandZ3GalerkinWienerDerivative244 (Real.log (3 / 2 : ℝ)) s u ≤
      50000 := by
    calc
      _ ≤ 100 * thirdFullThreeBandZ3GalerkinWienerDerivative244
            (Real.log (3 / 2 : ℝ)) s u :=
          mul_le_mul_of_nonneg_right hMassCap hDnonneg
      _ ≤ 100 * 500 :=
          mul_le_mul_of_nonneg_left hDerCap (by norm_num)
      _ = 50000 := by norm_num
  have hMuLap : mu * thirdFullThreeBandZ3GalerkinLaplacianWiener244
      (Real.log (3 / 2 : ℝ)) s u ≤ 1000 := by
    calc
      _ ≤ mu * 10000 := mul_le_mul_of_nonneg_left hLapCap hmu
      _ ≤ (1 / 10 : ℝ) * 10000 :=
        mul_le_mul_of_nonneg_right hmuMax (by norm_num)
      _ = 1000 := by norm_num
  have hField := thirdFullThreeBand_z3GalerkinNSField_mass_bound244
    mu (Real.log (3 / 2 : ℝ)) hmu hr s u
  linarith


/-- The actual Laplacian-weighted COMPLETE Leray output has a uniform
5,000,000 ceiling at radius 5/4, provided the input W_(9/5) is at most 100.
This discharges the second spatial input to the proposed local Duhamel
residual coefficient; no output collision or support factor appears. -/
theorem thirdFullThreeBand_z3GalerkinLaplacianSource5000000_100Ball244
    (outputs s : Finset Z3ExactIndex244)
    (u : Z3ExactIndex244 → Z3ExactBand244)
    (hU : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (9 / 5 : ℝ)) s u ≤ 100) :
    (∑ n ∈ outputs,
      ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2 *
        thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n *
        ‖thirdFullThreeBandZ3GalerkinQuadratic244 s s u u n‖) ≤
      5000000 := by
  have hSource := thirdFullThreeBand_z3GalerkinAnalyticReserveSource244
    (Real.log (5 / 4 : ℝ)) (Real.log (3 / 2 : ℝ)) 100
    (Real.log_nonneg (by norm_num))
    (Real.log_nonneg (by norm_num))
    (by norm_num) outputs s s u u
    (by intro n hn; exact thirdFullThreeBand_z3TwoRadiusLaplacianEnvelope244 n)
  have hRadius : Real.log (3 / 2 : ℝ) ≤ Real.log (9 / 5 : ℝ) :=
    Real.log_le_log (by norm_num) (by norm_num)
  have hMass := thirdFullThreeBand_z3WienerMass_radius_mono244
    _ _ hRadius s u
  have hDerivative := thirdFullThreeBand_z3WienerDerivative_reserved244
    _ _ 5 (by norm_num) s u
    (by intro n hn; exact thirdFullThreeBand_z3ThreeRadiusDerivativeEnvelope244 n)
  have hMassCap : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (3 / 2 : ℝ)) s u ≤ 100 := hMass.trans hU
  have hDerCap : thirdFullThreeBandZ3GalerkinWienerDerivative244
      (Real.log (3 / 2 : ℝ)) s u ≤ 500 := by
    have h := mul_le_mul_of_nonneg_left hU (by norm_num : (0 : ℝ) ≤ 5)
    linarith
  have hDnonneg : 0 ≤ thirdFullThreeBandZ3GalerkinWienerDerivative244
      (Real.log (3 / 2 : ℝ)) s u := by
    unfold thirdFullThreeBandZ3GalerkinWienerDerivative244
    apply Finset.sum_nonneg
    intro n hn
    exact mul_nonneg
      (mul_nonneg (thirdFullThreeBand_z3Weight_pos244 _ _).le
        (thirdFullThreeBand_z3Degree_nonneg244 n)) (norm_nonneg _)
  have hProd :
      thirdFullThreeBandZ3GalerkinWienerMass244 (Real.log (3 / 2 : ℝ)) s u *
        thirdFullThreeBandZ3GalerkinWienerDerivative244 (Real.log (3 / 2 : ℝ)) s u ≤
      50000 := by
    calc
      _ ≤ 100 * thirdFullThreeBandZ3GalerkinWienerDerivative244
            (Real.log (3 / 2 : ℝ)) s u :=
          mul_le_mul_of_nonneg_right hMassCap hDnonneg
      _ ≤ 100 * 500 :=
          mul_le_mul_of_nonneg_left hDerCap (by norm_num)
      _ = 50000 := by norm_num
  have hBound := mul_le_mul_of_nonneg_left hProd (by norm_num : (0 : ℝ) ≤ 100)
  calc
    _ ≤ 100 * (thirdFullThreeBandZ3GalerkinWienerMass244
          (Real.log (3 / 2 : ℝ)) s u *
          thirdFullThreeBandZ3GalerkinWienerDerivative244
            (Real.log (3 / 2 : ℝ)) s u) := by
        simpa only [thirdFullThreeBandZ3GalerkinWienerMass244,
          thirdFullThreeBandZ3GalerkinWienerDerivative244] using hSource
    _ ≤ 100 * 50000 := hBound
    _ = 5000000 := by norm_num

end
end PrimeTensor.FirstMonomialTriad
