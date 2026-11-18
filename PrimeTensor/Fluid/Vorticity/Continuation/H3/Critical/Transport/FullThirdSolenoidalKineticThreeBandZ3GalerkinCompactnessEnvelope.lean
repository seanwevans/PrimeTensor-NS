import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3GalerkinSupremumFlow
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3GalerkinConstructedNonEscape
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# Cutoff-uniform analytic spectral tails and temporal equicontinuity for actual Galerkin flows

The verified common-horizon theorem constructs an exact solution for EVERY finite
Fourier cutoff. This module extracts two quantitative compactness estimates
without a uniform finite-state dimension: the low-radius Wiener tail beyond
integer frequency N is bounded by 100*(5/6)^N, and every trajectory is
51000-Lipschitz on the same closed time interval.

The final theorem constructs these estimates simultaneously for arbitrary
cutoff-indexed initial data satisfying a uniform strict initial analytic ball.
No compact subsequence, infinite Fourier solution, or limit interchange is
claimed here. Those remain the next mathematical obligations.
-/

namespace PrimeTensor.FirstMonomialTriad

open Set
noncomputable section

attribute [local instance 1100] NormedSpace.complexToReal

private abbrev CompactIndex244 := thirdFullThreeBandZ3Index244
private abbrev CompactBand244 := EuclideanSpace ℂ (Fin 3)

/-- The analytic radius gap bounds the entire high-frequency tail, not
just each coefficient separately. No cardinality factor appears. -/
theorem thirdFullThreeBand_z3WienerTail_twoRadius244
    (r R N : ℝ) (hrR : r ≤ R)
    (s : Finset CompactIndex244)
    (u : CompactIndex244 → CompactBand244) :
    thirdFullThreeBandZ3GalerkinWienerMass244 r
      (s.filter (fun n => N ≤ thirdFullThreeBandZ3Degree244 n)) u ≤
    Real.exp (-(R - r) * N) *
      thirdFullThreeBandZ3GalerkinWienerMass244 R s u := by
  classical
  have hGap : 0 ≤ R - r := sub_nonneg.mpr hrR
  have hNonneg (n : CompactIndex244) :
      0 ≤ thirdFullThreeBandZ3Weight244 R n * ‖u n‖ :=
    mul_nonneg (thirdFullThreeBand_z3Weight_pos244 R n).le (norm_nonneg _)
  have hCoeff (n : CompactIndex244)
      (hn : n ∈ s.filter (fun n => N ≤ thirdFullThreeBandZ3Degree244 n)) :
      thirdFullThreeBandZ3Weight244 r n * ‖u n‖ ≤
        Real.exp (-(R - r) * N) *
          (thirdFullThreeBandZ3Weight244 R n * ‖u n‖) := by
    have hN : N ≤ thirdFullThreeBandZ3Degree244 n := (Finset.mem_filter.mp hn).2
    have hMul := mul_le_mul_of_nonneg_left hN hGap
    have hExponent : -(R - r) * thirdFullThreeBandZ3Degree244 n ≤
        -(R - r) * N := by nlinarith
    have hExp := Real.exp_le_exp.mpr hExponent
    have hIdentity : thirdFullThreeBandZ3Weight244 r n =
        Real.exp (-(R - r) * thirdFullThreeBandZ3Degree244 n) *
          thirdFullThreeBandZ3Weight244 R n := by
      unfold thirdFullThreeBandZ3Weight244
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      thirdFullThreeBandZ3Weight244 r n * ‖u n‖ =
          Real.exp (-(R - r) * thirdFullThreeBandZ3Degree244 n) *
            (thirdFullThreeBandZ3Weight244 R n * ‖u n‖) := by
        rw [hIdentity]
        ring
      _ ≤ Real.exp (-(R - r) * N) *
            (thirdFullThreeBandZ3Weight244 R n * ‖u n‖) :=
        mul_le_mul_of_nonneg_right hExp (hNonneg n)
  unfold thirdFullThreeBandZ3GalerkinWienerMass244
  calc
    (∑ n ∈ s.filter (fun n => N ≤ thirdFullThreeBandZ3Degree244 n),
        thirdFullThreeBandZ3Weight244 r n * ‖u n‖) ≤
      ∑ n ∈ s.filter (fun n => N ≤ thirdFullThreeBandZ3Degree244 n),
        Real.exp (-(R - r) * N) *
          (thirdFullThreeBandZ3Weight244 R n * ‖u n‖) := by
        apply Finset.sum_le_sum
        intro n hn
        exact hCoeff n hn
    _ = Real.exp (-(R - r) * N) *
        (∑ n ∈ s.filter (fun n => N ≤ thirdFullThreeBandZ3Degree244 n),
          thirdFullThreeBandZ3Weight244 R n * ‖u n‖) := by
        rw [Finset.mul_sum]
    _ ≤ Real.exp (-(R - r) * N) *
        (∑ n ∈ s, thirdFullThreeBandZ3Weight244 R n * ‖u n‖) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro n hn hnNot
          exact hNonneg n

/-- The 9/5 analytic ball pays an exponentially decaying 3/2 Wiener tail.
For an integer threshold N, the factor is exactly `(5/6)^N`. -/
theorem thirdFullThreeBand_z3WienerTail_150_from180_100Ball244
    (N : ℝ) (s : Finset CompactIndex244)
    (u : CompactIndex244 → CompactBand244)
    (hHigh : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (9 / 5 : ℝ)) s u ≤ 100) :
    thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (3 / 2 : ℝ))
      (s.filter (fun n => N ≤ thirdFullThreeBandZ3Degree244 n)) u ≤
      Real.exp (-(Real.log (9 / 5 : ℝ) - Real.log (3 / 2 : ℝ)) * N) * 100 := by
  have hRadius : Real.log (3 / 2 : ℝ) ≤ Real.log (9 / 5 : ℝ) :=
    Real.log_le_log (by norm_num) (by norm_num)
  have hTail := thirdFullThreeBand_z3WienerTail_twoRadius244
    (Real.log (3 / 2 : ℝ)) (Real.log (9 / 5 : ℝ)) N hRadius s u
  exact hTail.trans (mul_le_mul_of_nonneg_left hHigh (Real.exp_pos _).le)

/-- Actual constructed Galerkin trajectories have a closed-time
51000-Lipschitz modulus, including at the right endpoint. -/
theorem thirdFullThreeBand_z3GalerkinFiniteODE_closedLipschitz51000_244
    (mu a b : ℝ) (s : Finset CompactIndex244)
    (gamma : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (hODE : ∀ t ∈ Icc a b,
      HasDerivAt gamma
        (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (gamma t)) t)
    (hSpeed : ∀ t ∈ Icc a b,
      ‖thirdFullThreeBandZ3GalerkinFiniteField244 mu s (gamma t)‖ ≤ 51000) :
    LipschitzOnWith (51000 : NNReal) gamma (Icc a b) := by
  have hDifferentiable : ∀ t ∈ Icc a b, DifferentiableAt ℝ gamma t := by
    intro t ht
    exact (hODE t ht).differentiableAt
  have hDerivative : ∀ t ∈ Icc a b, ‖deriv gamma t‖ ≤ (51000 : ℝ) := by
    intro t ht
    rw [(hODE t ht).deriv]
    exact hSpeed t ht
  apply LipschitzOnWith.of_dist_le_mul
  intro t ht v hv
  have hMean : ‖gamma t - gamma v‖ ≤ (51000 : ℝ) * ‖t - v‖ :=
    Convex.norm_image_sub_le_of_norm_deriv_le
      hDifferentiable hDerivative (convex_Icc a b) hv ht
  have hCast : ((51000 : NNReal) : ℝ) = (51000 : ℝ) := by norm_num
  simpa only [dist_eq_norm, hCast] using hMean

/-- The first concrete precompactness envelope for ACTUAL Galerkin flows:
exact ODE, moving analytic ball, uniform closed-time Lipschitz control,
and exponentially small low-radius Fourier tails. All constants are
independent of the finite Fourier cutoff s. -/
theorem thirdFullThreeBand_z3GalerkinFiniteODE_exists_compactnessEnvelope244
    (mu a : ℝ) (hmu : 0 ≤ mu) (hmuMax : mu ≤ (1 / 10 : ℝ))
    (s : Finset CompactIndex244)
    (x0 : thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (hInitial : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (2 : ℝ)) s
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 s x0) < 100) :
    ∃ gamma : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s,
      gamma a = x0 ∧
      (∀ t ∈ Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a),
        HasDerivAt gamma
          (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (gamma t)) t) ∧
      (∀ t ∈ Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a),
        thirdFullThreeBandZ3GalerkinWienerMass244
          (thirdFullThreeBandZ3GalerkinMovingRadius244 a t) s
          (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (gamma t)) ≤ 100) ∧
      LipschitzOnWith (51000 : NNReal) gamma
        (Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a)) ∧
      (∀ t ∈ Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a),
        thirdFullThreeBandZ3GalerkinWienerMass244 (Real.log (9 / 5 : ℝ)) s
          (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (gamma t)) ≤ 100) ∧
      (∀ t ∈ Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a),
        ‖thirdFullThreeBandZ3GalerkinFiniteField244 mu s (gamma t)‖ ≤ 51000) ∧
      (∀ t ∈ Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a), ∀ N : ℝ,
        thirdFullThreeBandZ3GalerkinWienerMass244 (Real.log (3 / 2 : ℝ))
          (s.filter (fun n => N ≤ thirdFullThreeBandZ3Degree244 n))
          (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (gamma t)) ≤
        Real.exp (-(Real.log (9 / 5 : ℝ) - Real.log (3 / 2 : ℝ)) * N) * 100) := by
  obtain ⟨gamma, hStart, hODE, hMoving⟩ :=
    thirdFullThreeBand_z3GalerkinFiniteODE_exists_commonHorizon244
      mu a hmu hmuMax s x0 hInitial
  have hHigh (t : ℝ)
      (ht : t ∈ Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a)) :
      thirdFullThreeBandZ3GalerkinWienerMass244 (Real.log (9 / 5 : ℝ)) s
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (gamma t)) ≤ 100 := by
    have hElapsed : t - a ≤ thirdFullThreeBandZ3GalerkinMovingRadiusWindow244 := by
      have hTop := ht.2
      unfold thirdFullThreeBandZ3GalerkinCommonHorizon244 at hTop
      linarith
    exact thirdFullThreeBand_z3MovingRadius_highBall244
      a t hElapsed s (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (gamma t))
      (hMoving t ht)
  have hSpeed (t : ℝ)
      (ht : t ∈ Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a)) :
      ‖thirdFullThreeBandZ3GalerkinFiniteField244 mu s (gamma t)‖ ≤ 51000 :=
    thirdFullThreeBand_z3GalerkinFiniteField_norm51000_100Ball244
      mu hmu hmuMax s (gamma t) (hHigh t ht)
  have hLip := thirdFullThreeBand_z3GalerkinFiniteODE_closedLipschitz51000_244
    mu a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a) s gamma hODE hSpeed
  have hTail (t : ℝ)
      (ht : t ∈ Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a))
      (N : ℝ) :
      thirdFullThreeBandZ3GalerkinWienerMass244 (Real.log (3 / 2 : ℝ))
        (s.filter (fun n => N ≤ thirdFullThreeBandZ3Degree244 n))
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (gamma t)) ≤
      Real.exp (-(Real.log (9 / 5 : ℝ) - Real.log (3 / 2 : ℝ)) * N) * 100 :=
    thirdFullThreeBand_z3WienerTail_150_from180_100Ball244 N s
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (gamma t)) (hHigh t ht)
  exact ⟨gamma, hStart, hODE, hMoving, hLip, hHigh, hSpeed, hTail⟩

/-- A whole cutoff-indexed family of honest trajectories with the SAME
Lipschitz and spectral-tail moduli. No consistency assumptions on the
cutoffs or existence assumptions on the trajectories are needed. -/
theorem thirdFullThreeBand_z3GalerkinFiniteODE_exists_uniformCutoffFamily244
    (mu a : ℝ) (hmu : 0 ≤ mu) (hmuMax : mu ≤ (1 / 10 : ℝ))
    (x0 : (s : Finset CompactIndex244) → thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (hInitial : ∀ s : Finset CompactIndex244,
      thirdFullThreeBandZ3GalerkinWienerMass244 (Real.log (2 : ℝ)) s
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (x0 s)) < 100) :
    ∃ gamma : (s : Finset CompactIndex244) → ℝ →
        thirdFullThreeBandZ3GalerkinFiniteState244 s,
      ∀ s : Finset CompactIndex244,
        gamma s a = x0 s ∧
        (∀ t ∈ Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a),
          HasDerivAt (gamma s)
            (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (gamma s t)) t) ∧
        LipschitzOnWith (51000 : NNReal) (gamma s)
          (Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a)) ∧
        (∀ t ∈ Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a), ∀ N : ℝ,
          thirdFullThreeBandZ3GalerkinWienerMass244 (Real.log (3 / 2 : ℝ))
            (s.filter (fun n => N ≤ thirdFullThreeBandZ3Degree244 n))
            (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (gamma s t)) ≤
          Real.exp (-(Real.log (9 / 5 : ℝ) - Real.log (3 / 2 : ℝ)) * N) * 100) := by
  classical
  have hExist (s : Finset CompactIndex244) :
      ∃ gamma : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s,
        gamma a = x0 s ∧
        (∀ t ∈ Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a),
          HasDerivAt gamma
            (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (gamma t)) t) ∧
        LipschitzOnWith (51000 : NNReal) gamma
          (Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a)) ∧
        (∀ t ∈ Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a), ∀ N : ℝ,
          thirdFullThreeBandZ3GalerkinWienerMass244 (Real.log (3 / 2 : ℝ))
            (s.filter (fun n => N ≤ thirdFullThreeBandZ3Degree244 n))
            (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (gamma t)) ≤
          Real.exp (-(Real.log (9 / 5 : ℝ) - Real.log (3 / 2 : ℝ)) * N) * 100) := by
    obtain ⟨gamma, hStart, hODE, _hMoving, hLip, _hHigh, _hSpeed, hTail⟩ :=
      thirdFullThreeBand_z3GalerkinFiniteODE_exists_compactnessEnvelope244
        mu a hmu hmuMax s (x0 s) (hInitial s)
    exact ⟨gamma, hStart, hODE, hLip, hTail⟩
  refine ⟨fun s => Classical.choose (hExist s), ?_⟩
  intro s
  exact Classical.choose_spec (hExist s)

end
end PrimeTensor.FirstMonomialTriad
