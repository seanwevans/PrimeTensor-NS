import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3GalerkinConstructedNonEscape
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Tactic

/-!
# Finite Z³ Galerkin: cutoff-free temporal Lipschitz and endpoint traces

The nonlinear Fourier field is the exact complete complex Leray convolution.
No modification of the Navier--Stokes field and no assumed global flow occur here.

On any preterminal interval of a strong finite-coefficient solution, a
51000 bound on the ACTUAL field norm gives a 51000-Lipschitz path in time,
independent of the number of retained modes. All Cauchy sequences of times
inside the interval therefore have convergent finite-coefficient states.
If the finite-state ball holds along the path, it passes to their limits.

This is the endpoint nonescape input for a maximal-interval gluing theorem;
that maximal gluing theorem is NOT proved in this module.
-/

namespace PrimeTensor.FirstMonomialTriad

open Set Filter
noncomputable section

attribute [local instance 1100] NormedSpace.complexToReal

private abbrev TraceIndex244 := thirdFullThreeBandZ3Index244

/-- A uniform bound on the *genuine* finite Galerkin vector field implies
Lipschitz continuity on a half-open preterminal interval. The endpoint
need not belong to the domain or carry a postulated derivative. -/
theorem thirdFullThreeBand_z3GalerkinFiniteODE_preterminalLipschitz51000_244
    (mu a b : ℝ) (s : Finset TraceIndex244)
    (alpha : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (hODE : ∀ t ∈ Ico a b,
      HasDerivAt alpha
        (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (alpha t)) t)
    (hSpeed : ∀ t ∈ Ico a b,
      ‖thirdFullThreeBandZ3GalerkinFiniteField244 mu s (alpha t)‖ ≤ 51000) :
    LipschitzOnWith (51000 : NNReal) alpha (Ico a b) := by
  have hDifferentiable : ∀ t ∈ Ico a b, DifferentiableAt ℝ alpha t := by
    intro t ht
    exact (hODE t ht).differentiableAt
  have hDerivative : ∀ t ∈ Ico a b, ‖deriv alpha t‖ ≤ (51000 : ℝ) := by
    intro t ht
    rw [(hODE t ht).deriv]
    exact hSpeed t ht
  apply LipschitzOnWith.of_dist_le_mul
  intro t ht u hu
  have hMean : ‖alpha t - alpha u‖ ≤ (51000 : ℝ) * ‖t - u‖ :=
    Convex.norm_image_sub_le_of_norm_deriv_le
      hDifferentiable hDerivative (convex_Ico a b) hu ht
  have hCast : ((51000 : NNReal) : ℝ) = (51000 : ℝ) := by norm_num
  simpa only [dist_eq_norm, hCast] using hMean

/-- Any Cauchy sequence of times inside the preterminal interval has
converging finite Galerkin states. Completeness is for the finite Pi space;
no compactness of the infinite Fourier lattice is invoked. -/
theorem thirdFullThreeBand_z3GalerkinFiniteODE_endpointSequence_exists244
    (mu a b : ℝ) (s : Finset TraceIndex244)
    (alpha : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (hODE : ∀ t ∈ Ico a b,
      HasDerivAt alpha
        (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (alpha t)) t)
    (hSpeed : ∀ t ∈ Ico a b,
      ‖thirdFullThreeBandZ3GalerkinFiniteField244 mu s (alpha t)‖ ≤ 51000)
    (times : ℕ → ℝ) (hTimes : ∀ n, times n ∈ Ico a b)
    (hTimeCauchy : CauchySeq times) :
    ∃ endpoint : thirdFullThreeBandZ3GalerkinFiniteState244 s,
      Tendsto (fun n => alpha (times n)) atTop (nhds endpoint) := by
  have hLip := thirdFullThreeBand_z3GalerkinFiniteODE_preterminalLipschitz51000_244
    mu a b s alpha hODE hSpeed
  have hRange : Set.range times ⊆ Ico a b := by
    rintro t ⟨n, rfl⟩
    exact hTimes n
  have hCauchyState : CauchySeq (alpha ∘ times) :=
    hLip.cauchySeq_comp hTimeCauchy hRange
  simpa only [Function.comp_def] using
    (cauchySeq_tendsto_of_complete hCauchyState)

/-- A finite-state bound survives the one-sided endpoint sequence limit.
No analytic-radius estimate beyond the preterminal bounds is assumed. -/
theorem thirdFullThreeBand_z3GalerkinFiniteODE_endpointSequence_nonescape244
    (mu a b : ℝ) (s : Finset TraceIndex244)
    (alpha : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (hODE : ∀ t ∈ Ico a b,
      HasDerivAt alpha
        (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (alpha t)) t)
    (hSpeed : ∀ t ∈ Ico a b,
      ‖thirdFullThreeBandZ3GalerkinFiniteField244 mu s (alpha t)‖ ≤ 51000)
    (hState : ∀ t ∈ Ico a b, ‖alpha t‖ ≤ 100)
    (times : ℕ → ℝ) (hTimes : ∀ n, times n ∈ Ico a b)
    (hTimeCauchy : CauchySeq times) :
    ∃ endpoint : thirdFullThreeBandZ3GalerkinFiniteState244 s,
      Tendsto (fun n => alpha (times n)) atTop (nhds endpoint) ∧
      ‖endpoint‖ ≤ 100 := by
  obtain ⟨endpoint, hLimit⟩ :=
    thirdFullThreeBand_z3GalerkinFiniteODE_endpointSequence_exists244
      mu a b s alpha hODE hSpeed times hTimes hTimeCauchy
  refine ⟨endpoint, hLimit, ?_⟩
  have hNormLimit : Tendsto (fun n => ‖alpha (times n)‖)
      atTop (nhds ‖endpoint‖) :=
    (continuous_norm.tendsto endpoint).comp hLimit
  apply le_of_tendsto hNormLimit
  exact Filter.Eventually.of_forall (fun n => hState (times n) (hTimes n))

/-- The constructed genuine Picard path is uniformly 51000-Lipschitz
in time, without dependence on the Galerkin frequency cutoff. The local
interval itself still depends on the cutoff; maximal continuation is next. -/
theorem thirdFullThreeBand_z3GalerkinConstructedLocal_temporalLipschitz244
    (mu a : ℝ) (hmu : 0 ≤ mu) (hmuMax : mu ≤ (1 / 10 : ℝ))
    (s : Finset TraceIndex244)
    (x0 : thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (hInitial : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (2 : ℝ)) s
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 s x0) < 100) :
    ∃ delta : ℝ,
      0 < delta ∧
      delta ≤ thirdFullThreeBandZ3GalerkinMovingRadiusWindow244 ∧
      ∃ alpha : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s,
        alpha a = x0 ∧
        (∀ t ∈ Icc a (a + delta),
          HasDerivAt alpha
            (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (alpha t)) t) ∧
        (∀ t ∈ Icc a (a + delta), ‖alpha t‖ ≤ 100) ∧
        LipschitzOnWith (51000 : NNReal) alpha (Ico a (a + delta)) := by
  obtain ⟨delta, hDelta, hWindow, alpha, hInit, hODE, hState,
      _hHigh, hSpeed, _hWienerSpeed, _hInt⟩ :=
    thirdFullThreeBand_z3GalerkinConstructedLocal_nonEscapeAndSpeed244
      mu a hmu hmuMax s x0 hInitial
  have hInclusion : Ico a (a + delta) ⊆ Icc a (a + delta) := by
    intro t ht
    exact ⟨ht.1, ht.2.le⟩
  have hLip := thirdFullThreeBand_z3GalerkinFiniteODE_preterminalLipschitz51000_244
    mu a (a + delta) s alpha
    (fun t ht => hODE t (hInclusion ht))
    (fun t ht => hSpeed t (hInclusion ht))
  exact ⟨delta, hDelta, hWindow, alpha, hInit, hODE, hState, hLip⟩

end
end PrimeTensor.FirstMonomialTriad
