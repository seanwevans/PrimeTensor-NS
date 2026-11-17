import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3GalerkinFiniteODELocalExistence
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic

/-!
# Construct a genuine local finite Galerkin trajectory inside the moving ball

The previous module proves Picard local existence of the exact finite
Navier--Stokes Leray coefficient field. The cutoff-free persistence theorem
requires a coefficientwise strong ODE on a compact time interval.

Here the finite coordinate projections transfer the actual Picard solution
to the zero-extended integer-lattice representation. A positive, possibly
cutoff-dependent initial interval fits inside both the Picard interval and
the common analytic-radius window. Persistence then follows without an
assumed solution path or a re-postulated analytic 100-ball.

This is NOT the cutoff-independent existence-time theorem. To reach the
full window one must establish maximal continuation and its finite-state
non-blowup criterion, then apply persistence on every partial interval.
-/

namespace PrimeTensor.FirstMonomialTriad

open Set
noncomputable section

attribute [local instance 1100] NormedSpace.complexToReal

private abbrev LocalBallIndex244 := thirdFullThreeBandZ3Index244
private abbrev LocalBallBand244 := EuclideanSpace ℂ (Fin 3)

/-- The analytic-radius reserve is *strictly* positive. This is needed to
select a nontrivial intersection with the Picard existence interval. -/
theorem thirdFullThreeBand_z3MovingRadiusWindow_pos244 :
    0 < thirdFullThreeBandZ3GalerkinMovingRadiusWindow244 := by
  unfold thirdFullThreeBandZ3GalerkinMovingRadiusWindow244
  apply div_pos
  · exact sub_pos.mpr
      (Real.log_lt_log (by norm_num : (0 : ℝ) < 9 / 5) (by norm_num : (9 / 5 : ℝ) < 2))
  · norm_num

/-- A finite Picard path differentiates coordinatewise after zero extension.
No finiteness instance is ever requested on the whole infinite lattice. -/
theorem thirdFullThreeBand_z3GalerkinFiniteODE_coordinate_hasDerivAt244
    (mu : ℝ) (s : Finset LocalBallIndex244)
    (alpha : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (t : ℝ)
    (hODE : HasDerivAt alpha
      (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (alpha t)) t)
    (n : LocalBallIndex244) (hn : n ∈ s) :
    HasDerivAt
      (fun z : ℝ => thirdFullThreeBandZ3GalerkinFiniteExtend244 s (alpha z) n)
      (thirdFullThreeBandZ3GalerkinNSField244 mu s
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (alpha t)) n) t := by
  classical
  let i : {k : LocalBallIndex244 // k ∈ s} := ⟨n, hn⟩
  let P : thirdFullThreeBandZ3GalerkinFiniteState244 s →L[ℝ] LocalBallBand244 :=
    ContinuousLinearMap.proj i
  have hP : HasFDerivAt
      (fun x : thirdFullThreeBandZ3GalerkinFiniteState244 s => x i)
      P (alpha t) := hasFDerivAt_apply i (alpha t)
  have hComp : HasDerivAt
      ((fun x : thirdFullThreeBandZ3GalerkinFiniteState244 s => x i) ∘ alpha)
      (P (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (alpha t))) t :=
    hP.comp_hasDerivAt t hODE
  have hEval : HasDerivAt
      (fun z : ℝ => alpha z i)
      ((thirdFullThreeBandZ3GalerkinFiniteField244 mu s (alpha t)) i) t := by
    simpa only [Function.comp_def, P, ContinuousLinearMap.proj_apply] using hComp
  have hPath : (fun z : ℝ =>
      thirdFullThreeBandZ3GalerkinFiniteExtend244 s (alpha z) n) =
      (fun z : ℝ => alpha z i) := by
    funext z
    exact thirdFullThreeBand_z3GalerkinFiniteExtend_on244 s (alpha z) n hn
  have hValue : thirdFullThreeBandZ3GalerkinNSField244 mu s
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (alpha t)) n =
      (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (alpha t)) i := rfl
  simpa only [hPath, hValue] using hEval

/-- Continuous finite paths remain continuous at each retained Fourier
coordinate after zero extension. -/
theorem thirdFullThreeBand_z3GalerkinFiniteODE_coordinate_continuousAt244
    (s : Finset LocalBallIndex244)
    (alpha : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (t : ℝ) (hAlpha : ContinuousAt alpha t)
    (n : LocalBallIndex244) (hn : n ∈ s) :
    ContinuousAt
      (fun z : ℝ => thirdFullThreeBandZ3GalerkinFiniteExtend244 s (alpha z) n) t := by
  classical
  let i : {k : LocalBallIndex244 // k ∈ s} := ⟨n, hn⟩
  have hComp : ContinuousAt
      ((fun x : thirdFullThreeBandZ3GalerkinFiniteState244 s => x i) ∘ alpha) t :=
    (continuous_apply i).continuousAt.comp hAlpha
  have hEval : ContinuousAt (fun z : ℝ => alpha z i) t := by
    simpa only [Function.comp_def] using hComp
  have hPath : (fun z : ℝ =>
      thirdFullThreeBandZ3GalerkinFiniteExtend244 s (alpha z) n) =
      (fun z : ℝ => alpha z i) := by
    funext z
    exact thirdFullThreeBand_z3GalerkinFiniteExtend_on244 s (alpha z) n hn
  simpa only [hPath] using hEval

/-- The actual local Picard solution, rather than a hypothetical strong
Galerkin trajectory, stays in the cutoff-free moving analytic 100-ball
on some nontrivial interval. The selected interval may depend on S;
its pointwise mass bound and radius reserve do not. -/
theorem thirdFullThreeBand_z3GalerkinFiniteField_constructedLocalMovingBall244
    (mu a : ℝ) (hmu : 0 ≤ mu)
    (s : Finset LocalBallIndex244)
    (x0 : thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (hInitial :
      thirdFullThreeBandZ3GalerkinWienerMass244 (Real.log (2 : ℝ)) s
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 s x0) < 100) :
    ∃ delta : ℝ,
      0 < delta ∧
      delta ≤ thirdFullThreeBandZ3GalerkinMovingRadiusWindow244 ∧
      ∃ alpha : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s,
        alpha a = x0 ∧
        (∀ t ∈ Icc a (a + delta),
          HasDerivAt alpha
            (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (alpha t)) t) ∧
        (∀ t ∈ Icc a (a + delta),
          thirdFullThreeBandZ3GalerkinWienerMass244
            (thirdFullThreeBandZ3GalerkinMovingRadius244 a t) s
            (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (alpha t)) ≤ 100) := by
  classical
  obtain ⟨alpha, hAlphaInit, delta0, hDelta0, hAlphaODE⟩ :=
    thirdFullThreeBand_z3GalerkinFiniteField_exists_local244 mu a s x0
  let tau : ℝ := thirdFullThreeBandZ3GalerkinMovingRadiusWindow244
  have hTau : 0 < tau := thirdFullThreeBand_z3MovingRadiusWindow_pos244
  let delta : ℝ := min (delta0 / 2) (tau / 2)
  have hDelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hDeltaSmall : delta < delta0 := by
    have h := min_le_left (delta0 / 2) (tau / 2)
    dsimp [delta]
    linarith
  have hDeltaWindow : delta ≤ tau := by
    have h := min_le_right (delta0 / 2) (tau / 2)
    dsimp [delta]
    linarith
  have hInside (t : ℝ) (ht : t ∈ Icc a (a + delta)) :
      t ∈ Ioo (a - delta0) (a + delta0) := by
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hODESmall (t : ℝ) (ht : t ∈ Icc a (a + delta)) :
      HasDerivAt alpha
        (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (alpha t)) t :=
    hAlphaODE t (hInside t ht)
  let u : ℝ → LocalBallIndex244 → LocalBallBand244 :=
    fun t => thirdFullThreeBandZ3GalerkinFiniteExtend244 s (alpha t)
  have hContinuous : ∀ n ∈ s,
      ContinuousOn (fun t : ℝ => u t n) (Icc a (a + delta)) := by
    intro n hn t ht
    exact (thirdFullThreeBand_z3GalerkinFiniteODE_coordinate_continuousAt244
      s alpha t (hODESmall t ht).continuousAt n hn).continuousWithinAt
  have hODE : ∀ n ∈ s, ∀ t ∈ Ico a (a + delta),
      HasDerivAt (fun z : ℝ => u z n)
        (thirdFullThreeBandZ3GalerkinNSField244 mu s (u t) n) t := by
    intro n hn t ht
    have htClosed : t ∈ Icc a (a + delta) := ⟨ht.1, ht.2.le⟩
    exact thirdFullThreeBand_z3GalerkinFiniteODE_coordinate_hasDerivAt244
      mu s alpha t (hODESmall t htClosed) n hn
  have hInit : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (2 : ℝ)) s (u a) < 100 := by
    simpa only [u, hAlphaInit] using hInitial
  have hWindow : (a + delta) - a ≤
      thirdFullThreeBandZ3GalerkinMovingRadiusWindow244 := by
    simpa only [add_sub_cancel_left, tau] using hDeltaWindow
  have hPersist := thirdFullThreeBand_z3MovingBall_cutoffFreePersistence244
    mu a (a + delta) hmu hWindow s u hContinuous hODE hInit
  refine ⟨delta, hDelta, ?_, alpha, hAlphaInit, hODESmall, ?_⟩
  · simpa only [tau] using hDeltaWindow
  · simpa only [u] using hPersist

end
end PrimeTensor.FirstMonomialTriad
