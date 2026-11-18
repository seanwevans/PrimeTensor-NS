import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3InfiniteOrderedLerayIdentification
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3GalerkinConstructedLocalBall
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Infinite Z³ Fourier evolution from the genuine finite Galerkin ODEs

The actual finite Galerkin paths satisfy their exact, viscosity-plus-Leray
coefficient ODE. For an eventually retained Fourier mode, we obtain its
exact Bochner FTC. Uniform convergence of the Fourier coefficient and of
the complete Leray source allows us to pass the *time integral* to the
limit, not merely its pointwise nonlinearity. The final statement is the
infinite Navier--Stokes coefficientwise integral equation with the
independently identified, absolutely convergent ordered Leray series.

The cutoff-exhaustion and uniform limits are explicit hypotheses. They
are proved in separate preceding modules for constructed sequences (with
compatible extraction), rather than being disguised as ODE existence.
This remains a local periodic Fourier result, not global NS continuation.
-/

namespace PrimeTensor.FirstMonomialTriad

open Set Filter MeasureTheory
open scoped Interval
noncomputable section

attribute [local instance 1100] NormedSpace.complexToReal

private abbrev EvIndex244 := thirdFullThreeBandZ3Index244
private abbrev EvBand244 := EuclideanSpace ℂ (Fin 3)

/-- A quantitative uniform-limit FTC. There is no assumed integral identity
for the limit: it is deduced from actual approximating derivatives, their
continuity, and their uniform convergence throughout the interval. -/
theorem thirdFullThreeBand_z3UniformODE_FTC_limit244
    (a b : ℝ) (hab : a ≤ b)
    (f D : ℕ → ℝ → EvBand244) (g F : ℝ → EvBand244)
    (hCont : ∀ᶠ k : ℕ in atTop,
      ContinuousOn (f k) (Icc a b) ∧ ContinuousOn (D k) (Icc a b))
    (hODE : ∀ᶠ k : ℕ in atTop,
      ∀ t ∈ Ioo a b, HasDerivAt (f k) (D k t) t)
    (hVal : ∀ t ∈ Icc a b,
      Tendsto (fun k => f k t) atTop (nhds (g t)))
    (hField : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ k : ℕ in atTop, ∀ t ∈ Icc a b,
        dist (D k t) (F t) < epsilon) :
    g b - g a = ∫ t in a..b, F t := by
  have hFTC : ∀ᶠ k : ℕ in atTop,
      f k b - f k a = ∫ t in a..b, D k t := by
    filter_upwards [hCont, hODE] with k hc hd
    exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      hab hc.1 hd (hc.2.intervalIntegrable_of_Icc hab)).symm
  have hUniform : TendstoUniformlyOn D F atTop (uIcc a b) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro epsilon hEpsilon
    filter_upwards [hField epsilon hEpsilon] with k hk t ht
    have ht' : t ∈ Icc a b := by simpa only [uIcc_of_le hab] using ht
    simpa only [dist_comm] using hk t ht'
  have hDerivativeContinuous : ∀ᶠ k : ℕ in atTop,
      ContinuousOn (D k) (uIcc a b) := by
    filter_upwards [hCont] with k hk
    simpa only [uIcc_of_le hab] using hk.2
  have hInt : Tendsto (fun k : ℕ => ∫ t in a..b, D k t)
      atTop (nhds (∫ t in a..b, F t)) :=
    TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
      hDerivativeContinuous hUniform
  have hValA : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hValB : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hEnds : Tendsto (fun k : ℕ => f k b - f k a) atTop
      (nhds (g b - g a)) := (hVal b hValB).sub (hVal a hValA)
  have hEndsFromFTC : Tendsto (fun k : ℕ => f k b - f k a) atTop
      (nhds (∫ t in a..b, F t)) :=
    hInt.congr' (hFTC.mono fun k hk => hk.symm)
  exact tendsto_nhds_unique hEnds hEndsFromFTC

/-- Uniform convergence of a velocity coefficient and a projected source
implies uniform convergence of the exact viscosity-plus-source Fourier
vector field. The Fourier Laplacian constant is independent of time and
of the Galerkin cutoff. -/
theorem thirdFullThreeBand_z3FourierField_uniformLimit244
    (lambda : ℝ) (T : Set ℝ)
    (u q : ℕ → ℝ → EvBand244) (g Q : ℝ → EvBand244)
    (hu : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ k : ℕ in atTop, ∀ t ∈ T, dist (u k t) (g t) < epsilon)
    (hq : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ k : ℕ in atTop, ∀ t ∈ T, dist (q k t) (Q t) < epsilon) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ k : ℕ in atTop, ∀ t ∈ T,
        dist ((-lambda) • u k t + q k t)
          ((-lambda) • g t + Q t) < epsilon := by
  intro epsilon hEpsilon
  let delta : ℝ := epsilon / (2 * (|lambda| + 1))
  have hDen : 0 < 2 * (|lambda| + 1) := by positivity
  have hDelta : 0 < delta := div_pos hEpsilon hDen
  have hHalf : 0 < epsilon / 2 := by linarith
  filter_upwards [hu delta hDelta, hq (epsilon / 2) hHalf]
    with k hkU hkQ t ht
  have hU := hkU t ht
  have hQ := hkQ t ht
  have hIdentity : ‖(-lambda : ℝ)‖ = |lambda| := by simp
  have hBound : |lambda| * delta + epsilon / 2 < epsilon := by
    have hd : delta * (2 * (|lambda| + 1)) = epsilon := by
      dsimp only [delta]
      field_simp [ne_of_gt hDen]
    have hp : 0 < delta := hDelta
    nlinarith
  calc
    dist ((-lambda) • u k t + q k t) ((-lambda) • g t + Q t) ≤
      dist ((-lambda) • u k t) ((-lambda) • g t) +
        dist (q k t) (Q t) := dist_add_add_le _ _ _ _
    _ = |lambda| * dist (u k t) (g t) + dist (q k t) (Q t) := by
      rw [dist_smul₀, hIdentity]
    _ < |lambda| * delta + epsilon / 2 := by
      have hm : |lambda| * dist (u k t) (g t) ≤ |lambda| * delta :=
        mul_le_mul_of_nonneg_left hU.le (abs_nonneg _)
      linarith
    _ < epsilon := hBound

set_option maxHeartbeats 1000000

/-- The true finite coefficient field is continuous in time at a retained
mode, because it is a polynomial vector field evaluated on a Lipschitz
finite-dimensional Galerkin trajectory. -/
theorem thirdFullThreeBand_z3FiniteODE_fieldCoordinate_continuousOn244
    (mu a b : ℝ) (s : Finset EvIndex244)
    (gamma : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (hLip : LipschitzOnWith (51000 : NNReal) gamma (Icc a b))
    (n : EvIndex244) (hn : n ∈ s) :
    ContinuousOn (fun t : ℝ =>
      thirdFullThreeBandZ3GalerkinNSField244 mu s
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (gamma t)) n)
      (Icc a b) := by
  classical
  let i : {j : EvIndex244 // j ∈ s} := ⟨n, hn⟩
  have hF : Continuous
      (thirdFullThreeBandZ3GalerkinFiniteField244 mu s) :=
    (thirdFullThreeBand_z3GalerkinFiniteField_contDiff244 mu s).continuous
  have hEval : Continuous
      (fun x : thirdFullThreeBandZ3GalerkinFiniteState244 s => x i) :=
    continuous_apply i
  have hCoord : Continuous (fun x : thirdFullThreeBandZ3GalerkinFiniteState244 s =>
      (thirdFullThreeBandZ3GalerkinFiniteField244 mu s x) i) :=
    hEval.comp hF
  change ContinuousOn (fun t : ℝ =>
    (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (gamma t)) i)
    (Icc a b)
  exact hCoord.comp_continuousOn hLip.continuousOn

set_option maxHeartbeats 200000

/-- The actual *finite ODEs*, not an assumed mild identity, yield the
infinite Navier--Stokes coefficientwise FTC along an exhaustive Galerkin
subsequence. The hypotheses are precisely the already-established
uniform coefficient and nonlinear-source convergence interfaces. -/
theorem thirdFullThreeBand_z3Galerkin_limitFourierIntegralEquation244
    (mu a : ℝ)
    (s : ℕ → Finset EvIndex244)
    (gamma : (j : ℕ) → ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 (s j))
    (phi : ℕ → ℕ) (g Q : ℝ → EvIndex244 → EvBand244)
    (hExhaust : thirdFullThreeBandZ3GalerkinExhausts244 (fun k => s (phi k)))
    (hLip : ∀ j, LipschitzOnWith (51000 : NNReal) (gamma j)
      (Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a)))
    (hODE : ∀ j, ∀ t ∈ Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a),
      HasDerivAt (gamma j)
        (thirdFullThreeBandZ3GalerkinFiniteField244 mu (s j) (gamma j t)) t)
    (hState : ∀ n, ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ k : ℕ in atTop, ∀ t ∈ Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a),
        dist (thirdFullThreeBandZ3GalerkinFiniteExtend244
          (s (phi k)) (gamma (phi k) t) n) (g t n) < epsilon)
    (hSource : ∀ n, ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ k : ℕ in atTop, ∀ t ∈ Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a),
        dist (thirdFullThreeBandZ3GalerkinQuadratic244
          (s (phi k)) (s (phi k))
          (thirdFullThreeBandZ3GalerkinFiniteExtend244
            (s (phi k)) (gamma (phi k) t))
          (thirdFullThreeBandZ3GalerkinFiniteExtend244
            (s (phi k)) (gamma (phi k) t)) n)
          (Q t n) < epsilon) :
    ∀ t ∈ Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a),
    ∀ n : EvIndex244,
      g t n - g a n =
        ∫ r in a..t,
          (-(mu * ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2)) •
            g r n + Q r n := by
  classical
  let b : ℝ := thirdFullThreeBandZ3GalerkinCommonHorizon244 a
  intro t ht n
  have hn : ∀ᶠ k : ℕ in atTop, n ∈ s (phi k) := hExhaust n
  let u : ℕ → ℝ → EvBand244 := fun k z =>
    thirdFullThreeBandZ3GalerkinFiniteExtend244
      (s (phi k)) (gamma (phi k) z) n
  let q : ℕ → ℝ → EvBand244 := fun k z =>
    thirdFullThreeBandZ3GalerkinQuadratic244
      (s (phi k)) (s (phi k))
      (thirdFullThreeBandZ3GalerkinFiniteExtend244
        (s (phi k)) (gamma (phi k) z))
      (thirdFullThreeBandZ3GalerkinFiniteExtend244
        (s (phi k)) (gamma (phi k) z)) n
  let lambda : ℝ := mu * ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2
  let D : ℕ → ℝ → EvBand244 := fun k z =>
    thirdFullThreeBandZ3GalerkinNSField244 mu (s (phi k))
      (thirdFullThreeBandZ3GalerkinFiniteExtend244
        (s (phi k)) (gamma (phi k) z)) n
  let F : ℝ → EvBand244 := fun z => (-lambda) • g z n + Q z n
  have hFiniteField (k : ℕ) (z : ℝ) :
      D k z = (-lambda) • u k z + q k z := rfl
  have hCont : ∀ᶠ k : ℕ in atTop,
      ContinuousOn (u k) (Icc a t) ∧ ContinuousOn (D k) (Icc a t) := by
    filter_upwards [hn] with k hnk
    constructor
    · exact (thirdFullThreeBand_z3Galerkin_zeroExtend_modeLipschitz244
        a (s (phi k)) (gamma (phi k)) (hLip (phi k)) n).continuousOn.mono
          (by intro z hz; exact ⟨hz.1, hz.2.trans ht.2⟩)
    · exact (thirdFullThreeBand_z3FiniteODE_fieldCoordinate_continuousOn244
        mu a b (s (phi k)) (gamma (phi k)) (hLip (phi k)) n hnk).mono
          (by intro z hz; exact ⟨hz.1, hz.2.trans ht.2⟩)
  have hODECoord : ∀ᶠ k : ℕ in atTop,
      ∀ z ∈ Ioo a t, HasDerivAt (u k) (D k z) z := by
    filter_upwards [hn] with k hnk z hz
    exact thirdFullThreeBand_z3GalerkinFiniteODE_coordinate_hasDerivAt244
      mu (s (phi k)) (gamma (phi k)) z
      (hODE (phi k) z ⟨hz.1.le, hz.2.le.trans ht.2⟩) n hnk
  have hVal : ∀ z ∈ Icc a t, Tendsto (fun k => u k z) atTop (nhds (g z n)) := by
    intro z hz
    apply Metric.tendsto_atTop.mpr
    intro epsilon hEpsilon
    obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp (hState n epsilon hEpsilon)
    exact ⟨K, fun k hk => hK k hk z ⟨hz.1, hz.2.trans ht.2⟩⟩
  have hDerivative : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ k : ℕ in atTop, ∀ z ∈ Icc a t,
        dist (D k z) (F z) < epsilon := by
    intro epsilon hEpsilon
    have hState' : ∀ delta : ℝ, 0 < delta →
        ∀ᶠ k : ℕ in atTop, ∀ z ∈ Icc a t,
          dist (u k z) (g z n) < delta := by
      intro delta hd
      filter_upwards [hState n delta hd] with k hk z hz
      exact hk z ⟨hz.1, hz.2.trans ht.2⟩
    have hSource' : ∀ delta : ℝ, 0 < delta →
        ∀ᶠ k : ℕ in atTop, ∀ z ∈ Icc a t,
          dist (q k z) (Q z n) < delta := by
      intro delta hd
      filter_upwards [hSource n delta hd] with k hk z hz
      exact hk z ⟨hz.1, hz.2.trans ht.2⟩
    have hFull := thirdFullThreeBand_z3FourierField_uniformLimit244
      lambda (Icc a t) u q (fun z => g z n) (fun z => Q z n)
      hState' hSource' epsilon hEpsilon
    filter_upwards [hFull] with k hk z hz
    simpa only [hFiniteField, F] using hk z hz
  exact thirdFullThreeBand_z3UniformODE_FTC_limit244 a t ht.1 u D
    (fun z => g z n) F hCont hODECoord hVal hDerivative

/-- Identifying the already completed source with the absolutely summable
ordered Fourier convolution converts the limit FTC into the physical
infinite-dimensional Navier--Stokes Fourier integral equation. -/
theorem thirdFullThreeBand_z3Galerkin_orderedLerayIntegralEquation244
    (mu a : ℝ)
    (s : ℕ → Finset EvIndex244)
    (gamma : (j : ℕ) → ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 (s j))
    (phi : ℕ → ℕ) (g Q : ℝ → EvIndex244 → EvBand244)
    (hExhaust : thirdFullThreeBandZ3GalerkinExhausts244 (fun k => s (phi k)))
    (hLip : ∀ j, LipschitzOnWith (51000 : NNReal) (gamma j)
      (Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a)))
    (hODE : ∀ j, ∀ t ∈ Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a),
      HasDerivAt (gamma j)
        (thirdFullThreeBandZ3GalerkinFiniteField244 mu (s j) (gamma j t)) t)
    (hState : ∀ n, ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ k : ℕ in atTop, ∀ t ∈ Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a),
        dist (thirdFullThreeBandZ3GalerkinFiniteExtend244
          (s (phi k)) (gamma (phi k) t) n) (g t n) < epsilon)
    (hSource : ∀ n, ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ k : ℕ in atTop, ∀ t ∈ Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a),
        dist (thirdFullThreeBandZ3GalerkinQuadratic244
          (s (phi k)) (s (phi k))
          (thirdFullThreeBandZ3GalerkinFiniteExtend244
            (s (phi k)) (gamma (phi k) t))
          (thirdFullThreeBandZ3GalerkinFiniteExtend244
            (s (phi k)) (gamma (phi k) t)) n)
          (Q t n) < epsilon)
    (hIdentity : ∀ t ∈ Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a),
      ∀ n, Q t n = thirdFullThreeBandZ3InfiniteOrderedLeray244 (g t) n) :
    ∀ t ∈ Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a),
    ∀ n : EvIndex244,
      g t n - g a n =
        ∫ r in a..t,
          (-(mu * ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2)) •
            g r n + thirdFullThreeBandZ3InfiniteOrderedLeray244 (g r) n := by
  intro t ht n
  have hFTC := thirdFullThreeBand_z3Galerkin_limitFourierIntegralEquation244
    mu a s gamma phi g Q hExhaust hLip hODE hState hSource t ht n
  rw [hFTC]
  apply intervalIntegral.integral_congr
  intro r hr
  have hr' : r ∈ Icc a t := by
    simpa only [uIcc_of_le ht.1] using hr
  exact congrArg
    (fun z : EvBand244 =>
      (-(mu * ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2)) • g r n + z)
    (hIdentity r ⟨hr'.1, hr'.2.trans ht.2⟩ n)

end
end PrimeTensor.FirstMonomialTriad
