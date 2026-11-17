import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3GalerkinODEToDuhamel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Shrinking analytic radius for the actual complex Z3 Galerkin source

The fixed-radius ODE bounds need a cutoff-independent analytic 100-ball.
At one radius r alone the differentiated Wiener mass D_r is not bounded by
W_r with a cutoff-independent coefficient. The Cauchy--Kowalevski repair
is to spend analytic radius: r_a(t) = log(2) - 100 (t-a).

This file proves the *exact* time derivative of its mode weights, the true
full-output Leray source absorption W_r(B(u,u)) <= 100 D_r(u) on the W_r
100-ball, and the cutoff-independent radius window

  0 <= t-a <= log(10/9)/100  ==>  r_a(t) >= log(9/5).

Thus the -100 D_r term in the moving weights has exactly the coefficient
needed to absorb the entire projected nonlinear source on that ball, with
no Fourier-cardinality factor. It also transfers a moving-radius 100-ball
to the older 9/5-ball and therefore to the proven strong-ODE Duhamel residual.

IMPORTANT: the invariance of the MOVING 100-ball itself is not proved here.
That requires the upper Dini derivative of the finite weighted norm at
zero Fourier coefficients, plus a comparison/first-exit argument. Nor is
the finite-dimensional ODE flow constructed here. No invariant ball,
Galerkin existence, or Navier--Stokes continuation is asserted.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Set
open scoped Interval

noncomputable section

private abbrev ShrinkIndex244 := thirdFullThreeBandZ3Index244
private abbrev ShrinkBand244 := EuclideanSpace ℂ (Fin 3)

/-- Radius lost to nonlinear advection at a fixed cutoff-independent rate. -/
noncomputable def thirdFullThreeBandZ3GalerkinMovingRadius244 (a t : ℝ) : ℝ :=
  Real.log (2 : ℝ) - 100 * (t - a)

/-- This duration spends precisely the log(2) to log(9/5) reserve. -/
noncomputable def thirdFullThreeBandZ3GalerkinMovingRadiusWindow244 : ℝ :=
  (Real.log (2 : ℝ) - Real.log (9 / 5 : ℝ)) / 100

/-- The uniform analytic-radius window is nonnegative. -/
theorem thirdFullThreeBand_z3MovingRadiusWindow_nonneg244 :
    0 ≤ thirdFullThreeBandZ3GalerkinMovingRadiusWindow244 := by
  unfold thirdFullThreeBandZ3GalerkinMovingRadiusWindow244
  apply div_nonneg
  · exact sub_nonneg.mpr
      (Real.log_le_log (by norm_num) (by norm_num))
  · norm_num

/-- The shrinking analytic radius remains at least log(9/5) on the
support-independent lifespan window. -/
theorem thirdFullThreeBand_z3MovingRadius_lower244
    (a t : ℝ)
    (ht : t - a ≤ thirdFullThreeBandZ3GalerkinMovingRadiusWindow244) :
    Real.log (9 / 5 : ℝ) ≤ thirdFullThreeBandZ3GalerkinMovingRadius244 a t := by
  unfold thirdFullThreeBandZ3GalerkinMovingRadius244
  unfold thirdFullThreeBandZ3GalerkinMovingRadiusWindow244 at ht
  have hScaled := mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ) ≤ 100)
  have hBound : 100 * (t - a) ≤
      Real.log (2 : ℝ) - Real.log (9 / 5 : ℝ) := by
    nlinarith
  linarith

/-- Larger time means smaller analytic radius; no statement about the
Fourier cutoff or an ODE trajectory is used. -/
theorem thirdFullThreeBand_z3MovingRadius_antitone244
    (a t₁ t₂ : ℝ) (hTime : t₁ ≤ t₂) :
    thirdFullThreeBandZ3GalerkinMovingRadius244 a t₂ ≤
      thirdFullThreeBandZ3GalerkinMovingRadius244 a t₁ := by
  unfold thirdFullThreeBandZ3GalerkinMovingRadius244
  linarith

/-- Exact weight derivative in the shrinking-radius method. The coefficient
-100*m(n) is physical integer-lattice degree, not a support-size proxy. -/
theorem thirdFullThreeBand_z3MovingWeight_hasDerivAt244
    (a t : ℝ) (n : ShrinkIndex244) :
    HasDerivAt
      (fun z : ℝ => thirdFullThreeBandZ3Weight244
        (thirdFullThreeBandZ3GalerkinMovingRadius244 a z) n)
      ((-100 * thirdFullThreeBandZ3Degree244 n) *
        thirdFullThreeBandZ3Weight244
          (thirdFullThreeBandZ3GalerkinMovingRadius244 a t) n) t := by
  have hLinear : HasDerivAt
      (fun z : ℝ => (Real.log (2 : ℝ) + 100 * a) + (-100) * z)
      (-100) t := by
    simpa using ((hasDerivAt_const_mul (x := t) (-100 : ℝ)).const_add
      (Real.log (2 : ℝ) + 100 * a))
  have hRadius : HasDerivAt
      (fun z : ℝ => thirdFullThreeBandZ3GalerkinMovingRadius244 a z)
      (-100) t := by
    convert hLinear using 1
    funext z
    unfold thirdFullThreeBandZ3GalerkinMovingRadius244
    ring
  have hExp :=
    (hRadius.mul_const (thirdFullThreeBandZ3Degree244 n)).exp
  have hExp' : HasDerivAt
      (fun z : ℝ => thirdFullThreeBandZ3Weight244
        (thirdFullThreeBandZ3GalerkinMovingRadius244 a z) n)
      (thirdFullThreeBandZ3Weight244
        (thirdFullThreeBandZ3GalerkinMovingRadius244 a t) n *
          (-100 * thirdFullThreeBandZ3Degree244 n)) t := by
    simpa only [thirdFullThreeBandZ3Weight244] using hExp
  exact hExp'.congr_deriv (by ring)

/-- The exact full-output complex Leray source is paid by at most 100
units of the differentiated Wiener mass on the same-radius 100-ball. -/
theorem thirdFullThreeBand_z3GalerkinSource_absorbed100244
    (r : ℝ) (hr : 0 ≤ r)
    (s : Finset ShrinkIndex244)
    (u : ShrinkIndex244 → ShrinkBand244)
    (hBall : thirdFullThreeBandZ3GalerkinWienerMass244 r s u ≤ 100) :
    thirdFullThreeBandZ3GalerkinWienerMass244 r s
      (thirdFullThreeBandZ3GalerkinQuadratic244 s s u u) ≤
      100 * thirdFullThreeBandZ3GalerkinWienerDerivative244 r s u := by
  have hQ := thirdFullThreeBand_z3GalerkinAllOutputWienerBound244
    r hr s s s u u
  have hD : 0 ≤ thirdFullThreeBandZ3GalerkinWienerDerivative244 r s u := by
    unfold thirdFullThreeBandZ3GalerkinWienerDerivative244
    apply Finset.sum_nonneg
    intro n hn
    exact mul_nonneg
      (mul_nonneg (thirdFullThreeBand_z3Weight_pos244 r n).le
        (thirdFullThreeBand_z3Degree_nonneg244 n)) (norm_nonneg _)
  have hCap := mul_le_mul_of_nonneg_right hBall hD
  have hSource := hQ.trans hCap
  simpa only [thirdFullThreeBandZ3GalerkinWienerMass244] using hSource

/-- The full complex Leray nonlinearity is exactly compensated by the rate
at which the analytic weight loses derivatives on the W_r 100-ball.
The negative term is the coefficient from the *proved* weight derivative. -/
theorem thirdFullThreeBand_z3GalerkinMovingRadius_sourceCompensation244
    (r : ℝ) (hr : 0 ≤ r)
    (s : Finset ShrinkIndex244)
    (u : ShrinkIndex244 → ShrinkBand244)
    (hBall : thirdFullThreeBandZ3GalerkinWienerMass244 r s u ≤ 100) :
    thirdFullThreeBandZ3GalerkinWienerMass244 r s
      (thirdFullThreeBandZ3GalerkinQuadratic244 s s u u) -
      100 * thirdFullThreeBandZ3GalerkinWienerDerivative244 r s u ≤ 0 := by
  linarith [thirdFullThreeBand_z3GalerkinSource_absorbed100244 r hr s u hBall]

/-- Every moving-radius 100-ball certificate gives the uniform 9/5-ball
required by the earlier strong-ODE/Duhamel consistency theorem. -/
theorem thirdFullThreeBand_z3MovingRadius_highBall244
    (a t : ℝ)
    (ht : t - a ≤ thirdFullThreeBandZ3GalerkinMovingRadiusWindow244)
    (s : Finset ShrinkIndex244)
    (u : ShrinkIndex244 → ShrinkBand244)
    (hMovingBall : thirdFullThreeBandZ3GalerkinWienerMass244
      (thirdFullThreeBandZ3GalerkinMovingRadius244 a t) s u ≤ 100) :
    thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (9 / 5 : ℝ)) s u ≤ 100 := by
  exact (thirdFullThreeBand_z3WienerMass_radius_mono244 _ _
    (thirdFullThreeBand_z3MovingRadius_lower244 a t ht) s u).trans hMovingBall

/-- A moving-radius Galerkin path certificate supplies exactly the higher
9/5-ball used in the genuine ODE-to-Duhamel residual theorem, without a
mode count, free frequency degree, or an assumed Duhamel identity.

The certificate is a visible hypothesis because its proof requires the
zero-safe upper-Dini estimate for the evolving norm and Galerkin existence. -/
theorem thirdFullThreeBand_z3MovingRadius_StrongODEResidual25750000_100Ball244
    (mu a b : ℝ) (hab : a ≤ b)
    (hmu : 0 ≤ mu) (hmuMax : mu ≤ (1 / 10 : ℝ))
    (hWindow : b - a ≤ thirdFullThreeBandZ3GalerkinMovingRadiusWindow244)
    (s : Finset ShrinkIndex244)
    (u : ℝ → ShrinkIndex244 → ShrinkBand244)
    (hContinuous : ∀ n ∈ s,
      ContinuousOn (fun t : ℝ => u t n) (Set.Icc a b))
    (hODE : ∀ n ∈ s, ∀ t ∈ Set.Ioo a b,
      HasDerivAt (fun z : ℝ => u z n)
        (thirdFullThreeBandZ3GalerkinNSField244 mu s (u t) n) t)
    (hFieldInt : ∀ t ∈ Set.Icc a b, ∀ n ∈ s,
      IntervalIntegrable
        (fun z : ℝ => thirdFullThreeBandZ3GalerkinNSField244 mu s (u z) n)
        volume a t)
    (hRetardedInt : ∀ n ∈ s,
      IntervalIntegrable (fun t : ℝ =>
        thirdFullThreeBandZ3GalerkinHeatFactor244 mu (b - t) n •
          thirdFullThreeBandZ3GalerkinQuadratic244 s s (u t) (u t) n)
        volume a b)
    (hMovingBall : ∀ t ∈ Set.Icc a b,
      thirdFullThreeBandZ3GalerkinWienerMass244
        (thirdFullThreeBandZ3GalerkinMovingRadius244 a t) s (u t) ≤ 100) :
    thirdFullThreeBandZ3GalerkinStepResidual244 mu (b - a)
        (Real.log (5 / 4 : ℝ)) s (u a) (u b) ≤
      thirdFullThreeBandZ3GalerkinLocalConsistencyCap244 * (b - a) ^ 2 := by
  have hHigh : ∀ t ∈ Set.Icc a b,
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (9 / 5 : ℝ)) s (u t) ≤ 100 := by
    intro t ht
    have hT : t - a ≤ b - a := sub_le_sub_right ht.2 a
    have hWindowT : t - a ≤ thirdFullThreeBandZ3GalerkinMovingRadiusWindow244 :=
      hT.trans hWindow
    exact thirdFullThreeBand_z3MovingRadius_highBall244 a t hWindowT
      s (u t) (hMovingBall t ht)
  exact thirdFullThreeBand_z3GalerkinStrongODE_fullResidual25750000_100Ball244
    mu a b hab hmu hmuMax s u hContinuous hODE hFieldInt
    hRetardedInt hHigh


/-- Fixed-cutoff Wiener derivative control without losing any frequency
cardinality factor. A finite cutoff is encoded by a bound on true l1 degree. -/
theorem thirdFullThreeBand_z3GalerkinFiniteDegreeDerivativeBound244
    (r K : ℝ) (s : Finset ShrinkIndex244)
    (u : ShrinkIndex244 → ShrinkBand244)
    (hDegree : ∀ n ∈ s, thirdFullThreeBandZ3Degree244 n ≤ K) :
    thirdFullThreeBandZ3GalerkinWienerDerivative244 r s u ≤
      K * thirdFullThreeBandZ3GalerkinWienerMass244 r s u := by
  classical
  unfold thirdFullThreeBandZ3GalerkinWienerDerivative244
    thirdFullThreeBandZ3GalerkinWienerMass244
  calc
    _ ≤ ∑ n ∈ s, K *
        (thirdFullThreeBandZ3Weight244 r n * ‖u n‖) := by
      apply Finset.sum_le_sum
      intro n hn
      have hProd : 0 ≤ thirdFullThreeBandZ3Weight244 r n * ‖u n‖ :=
        mul_nonneg (thirdFullThreeBand_z3Weight_pos244 r n).le (norm_nonneg _)
      have h := mul_le_mul_of_nonneg_right (hDegree n hn) hProd
      calc
        _ = thirdFullThreeBandZ3Degree244 n *
            (thirdFullThreeBandZ3Weight244 r n * ‖u n‖) := by ring
        _ ≤ K * (thirdFullThreeBandZ3Weight244 r n * ‖u n‖) := h
    _ = _ := by rw [Finset.mul_sum]

/-- The Laplacian of a fixed Galerkin cutoff is bounded in its own Wiener
radius. This constant depends on the maximal *frequency*, not card(s). -/
theorem thirdFullThreeBand_z3GalerkinFiniteFrequencyLaplacianBound244
    (r L : ℝ) (s : Finset ShrinkIndex244)
    (u : ShrinkIndex244 → ShrinkBand244)
    (hFrequency : ∀ n ∈ s,
      ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2 ≤ L) :
    thirdFullThreeBandZ3GalerkinLaplacianWiener244 r s u ≤
      L * thirdFullThreeBandZ3GalerkinWienerMass244 r s u := by
  classical
  unfold thirdFullThreeBandZ3GalerkinLaplacianWiener244
    thirdFullThreeBandZ3GalerkinWienerMass244
  calc
    _ ≤ ∑ n ∈ s, L *
        (thirdFullThreeBandZ3Weight244 r n * ‖u n‖) := by
      apply Finset.sum_le_sum
      intro n hn
      have hProd : 0 ≤ thirdFullThreeBandZ3Weight244 r n * ‖u n‖ :=
        mul_nonneg (thirdFullThreeBand_z3Weight_pos244 r n).le (norm_nonneg _)
      have h := mul_le_mul_of_nonneg_right (hFrequency n hn) hProd
      calc
        _ = ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2 *
            (thirdFullThreeBandZ3Weight244 r n * ‖u n‖) := by ring
        _ ≤ L * (thirdFullThreeBandZ3Weight244 r n * ‖u n‖) := h
    _ = _ := by rw [Finset.mul_sum]

/-- The genuine finite Galerkin Navier--Stokes vector field is locally
Lipschitz at ONE radius, with the frequency bounds K,L as explicit fixed-
cutoff parameters. This is the analytic input to finite-dimensional Picard,
not a claim that the ODE flow has already been constructed.
The exact polarization includes all colliding Leray output modes. -/
theorem thirdFullThreeBand_z3GalerkinFixedCutoffField_locallyLipschitz244
    (mu r K L : ℝ) (hmu : 0 ≤ mu) (hr : 0 ≤ r)
    (s : Finset ShrinkIndex244)
    (u v : ShrinkIndex244 → ShrinkBand244)
    (hDegree : ∀ n ∈ s, thirdFullThreeBandZ3Degree244 n ≤ K)
    (hFrequency : ∀ n ∈ s,
      ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2 ≤ L) :
    thirdFullThreeBandZ3GalerkinWienerMass244 r s
        (fun n => thirdFullThreeBandZ3GalerkinNSField244 mu s u n -
          thirdFullThreeBandZ3GalerkinNSField244 mu s v n) ≤
      (mu * L + K *
          (thirdFullThreeBandZ3GalerkinWienerMass244 r s u +
           thirdFullThreeBandZ3GalerkinWienerMass244 r s v)) *
        thirdFullThreeBandZ3GalerkinWienerMass244 r s (fun n => u n - v n) := by
  classical
  let d : ShrinkIndex244 → ShrinkBand244 := fun n => u n - v n
  let M := thirdFullThreeBandZ3GalerkinWienerMass244 r s d
  let U := thirdFullThreeBandZ3GalerkinWienerMass244 r s u
  let V := thirdFullThreeBandZ3GalerkinWienerMass244 r s v
  have hM : 0 ≤ M := by
    dsimp [M, thirdFullThreeBandZ3GalerkinWienerMass244]
    apply Finset.sum_nonneg
    intro n hn
    exact mul_nonneg (thirdFullThreeBand_z3Weight_pos244 r n).le (norm_nonneg _)
  have hV : 0 ≤ V := by
    dsimp [V, thirdFullThreeBandZ3GalerkinWienerMass244]
    apply Finset.sum_nonneg
    intro n hn
    exact mul_nonneg (thirdFullThreeBand_z3Weight_pos244 r n).le (norm_nonneg _)
  have hDU := thirdFullThreeBand_z3GalerkinFiniteDegreeDerivativeBound244
    r K s u hDegree
  have hDD := thirdFullThreeBand_z3GalerkinFiniteDegreeDerivativeBound244
    r K s d hDegree
  have hLap := thirdFullThreeBand_z3GalerkinFiniteFrequencyLaplacianBound244
    r L s d hFrequency
  have hPolar := thirdFullThreeBand_z3PolarizedSource_mass_bound244
    r hr s s u v
  have hSource :
      (∑ n ∈ s, thirdFullThreeBandZ3Weight244 r n *
          ‖thirdFullThreeBandZ3GalerkinQuadratic244 s s u u n -
            thirdFullThreeBandZ3GalerkinQuadratic244 s s v v n‖) ≤
      M * thirdFullThreeBandZ3GalerkinWienerDerivative244 r s u +
      V * thirdFullThreeBandZ3GalerkinWienerDerivative244 r s d := by
    calc
      _ = ∑ n ∈ s, thirdFullThreeBandZ3Weight244 r n *
          ‖thirdFullThreeBandZ3GalerkinQuadratic244 s s d u n +
            thirdFullThreeBandZ3GalerkinQuadratic244 s s v d n‖ := by
          apply Finset.sum_congr rfl
          intro n hn
          exact congrArg (fun X : ShrinkBand244 =>
            thirdFullThreeBandZ3Weight244 r n * ‖X‖)
            (thirdFullThreeBand_z3GalerkinQuadratic_exactPolarization244 s u v n)
      _ ≤ _ := by simpa only [M, V, d] using hPolar
  have hSourceCap :
      M * thirdFullThreeBandZ3GalerkinWienerDerivative244 r s u +
      V * thirdFullThreeBandZ3GalerkinWienerDerivative244 r s d ≤
      K * (U + V) * M := by
    have h1 : M * thirdFullThreeBandZ3GalerkinWienerDerivative244 r s u ≤
        M * (K * U) := mul_le_mul_of_nonneg_left hDU hM
    have h2 : V * thirdFullThreeBandZ3GalerkinWienerDerivative244 r s d ≤
        V * (K * M) := mul_le_mul_of_nonneg_left hDD hV
    calc
      _ ≤ M * (K * U) + V * (K * M) := add_le_add h1 h2
      _ = K * (U + V) * M := by ring
  have hField := thirdFullThreeBand_z3GalerkinNSFieldDifference_mass_bound244
    mu r hmu s u v
  have hVisc := mul_le_mul_of_nonneg_left hLap hmu
  calc
    _ ≤ mu * thirdFullThreeBandZ3GalerkinLaplacianWiener244 r s
          (fun n => u n - v n) +
        (∑ n ∈ s, thirdFullThreeBandZ3Weight244 r n *
          ‖thirdFullThreeBandZ3GalerkinQuadratic244 s s u u n -
            thirdFullThreeBandZ3GalerkinQuadratic244 s s v v n‖) := hField
    _ ≤ mu * (L * thirdFullThreeBandZ3GalerkinWienerMass244 r s
          (fun n => u n - v n)) +
        K * (thirdFullThreeBandZ3GalerkinWienerMass244 r s u +
          thirdFullThreeBandZ3GalerkinWienerMass244 r s v) *
          thirdFullThreeBandZ3GalerkinWienerMass244 r s (fun n => u n - v n) :=
      add_le_add hVisc (hSource.trans hSourceCap)
    _ = _ := by ring

end
end PrimeTensor.FirstMonomialTriad
