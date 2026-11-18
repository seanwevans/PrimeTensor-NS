import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3GalerkinMaximalEndpointAlternative
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic

/-!
# Genuine finite Z³ Leray Galerkin field: compact-ball Lipschitz and overlap uniqueness

The previously constructed finite coefficient field is C¹, but it is quadratic,
so a GLOBAL Lipschitz bound is not asserted. On every fixed compact finite-state
ball, its derivative is bounded and therefore the exact complete Leray field
has a finite, potentially cutoff-dependent Lipschitz constant.

ODE uniqueness then forces any two strong finite-Galerkin trajectories with
identical initial state, which remain in that ball, to agree throughout the
common compact time interval. The previously established cutoff-free analytic
persistence supplies the necessary 100-ball automatically on every compact
initial subinterval before the universal analytic-radius horizon.

This gives canonical overlap compatibility of local Picard continuations;
it is the input for constructing a maximal path, NOT a construction of the
maximal path and NOT yet unconditional common-horizon existence.
-/

namespace PrimeTensor.FirstMonomialTriad

open Set
noncomputable section

attribute [local instance 1100] NormedSpace.complexToReal

private abbrev UniqueIndex244 := thirdFullThreeBandZ3Index244

/-- The genuine finite Leray field has a Lipschitz constant on every fixed
finite-state closed ball. The constant may depend on S and R; no global
Lipschitz estimate for this quadratic field is claimed. -/
theorem thirdFullThreeBand_z3GalerkinFiniteField_lipschitzOnClosedBall244
    (mu : ℝ) (s : Finset UniqueIndex244) (R : ℝ) :
    ∃ K : NNReal, LipschitzOnWith K
      (thirdFullThreeBandZ3GalerkinFiniteField244 mu s)
      (Metric.closedBall
        (0 : thirdFullThreeBandZ3GalerkinFiniteState244 s) R) := by
  classical
  let E := thirdFullThreeBandZ3GalerkinFiniteState244 s
  let F : E → E := thirdFullThreeBandZ3GalerkinFiniteField244 mu s
  have hSmooth : ContDiffOn ℝ 1 F (Metric.closedBall (0 : E) R) :=
    (thirdFullThreeBand_z3GalerkinFiniteField_contDiff244 mu s).contDiffOn
  have hConvex : Convex ℝ (Metric.closedBall (0 : E) R) :=
    convex_closedBall (0 : E) R
  have hCompact : IsCompact (Metric.closedBall (0 : E) R) :=
    isCompact_closedBall (0 : E) R
  exact hSmooth.exists_lipschitzOnWith (by norm_num) hConvex hCompact

/-- Exact strong ODE uniqueness on a common compact time interval, assuming
both paths lie in one finite-state ball. This uses the actual finite Leray
polynomial rather than a surrogate globally Lipschitz vector field. -/
theorem thirdFullThreeBand_z3GalerkinFiniteODE_uniqueOnCompactBall244
    (mu a b : ℝ) (s : Finset UniqueIndex244)
    (alpha beta : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (R : ℝ)
    (hAlphaODE : ∀ t ∈ Icc a b,
      HasDerivAt alpha
        (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (alpha t)) t)
    (hBetaODE : ∀ t ∈ Icc a b,
      HasDerivAt beta
        (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (beta t)) t)
    (hAlphaBound : ∀ t ∈ Icc a b, ‖alpha t‖ ≤ R)
    (hBetaBound : ∀ t ∈ Icc a b, ‖beta t‖ ≤ R)
    (hInitial : alpha a = beta a) :
    Set.EqOn alpha beta (Icc a b) := by
  classical
  let E := thirdFullThreeBandZ3GalerkinFiniteState244 s
  let F : E → E := thirdFullThreeBandZ3GalerkinFiniteField244 mu s
  obtain ⟨K, hLip⟩ :=
    thirdFullThreeBand_z3GalerkinFiniteField_lipschitzOnClosedBall244 mu s R
  have hAlphaCont : ContinuousOn alpha (Icc a b) := by
    intro t ht
    exact (hAlphaODE t ht).continuousAt.continuousWithinAt
  have hBetaCont : ContinuousOn beta (Icc a b) := by
    intro t ht
    exact (hBetaODE t ht).continuousAt.continuousWithinAt
  have hAlphaRight : ∀ t ∈ Ico a b,
      HasDerivWithinAt alpha (F (alpha t)) (Ici t) t := by
    intro t ht
    exact (hAlphaODE t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt
  have hBetaRight : ∀ t ∈ Ico a b,
      HasDerivWithinAt beta (F (beta t)) (Ici t) t := by
    intro t ht
    exact (hBetaODE t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt
  have hAlphaInside : ∀ t ∈ Ico a b,
      alpha t ∈ Metric.closedBall (0 : E) R := by
    intro t ht
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      (hAlphaBound t ⟨ht.1, ht.2.le⟩)
  have hBetaInside : ∀ t ∈ Ico a b,
      beta t ∈ Metric.closedBall (0 : E) R := by
    intro t ht
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      (hBetaBound t ⟨ht.1, ht.2.le⟩)
  exact ODE_solution_unique_of_mem_Icc_right
    (v := fun _ => F)
    (s := fun _ => Metric.closedBall (0 : E) R)
    (K := K) (f := alpha) (g := beta)
    (fun _ _ => hLip)
    hAlphaCont hAlphaRight hAlphaInside
    hBetaCont hBetaRight hBetaInside hInitial

/-- Automatic overlap uniqueness of two genuine Z³ Galerkin strong
trajectories inside the common analytic window: ONLY the strict initial
analytic bound and ODE equations are supplied. No late-time 100-ball or
Lipschitz premise is postulated. In particular, compatible local Picard
restarts cannot branch before the analytic horizon. -/
theorem thirdFullThreeBand_z3GalerkinFiniteODE_automaticOverlapUnique244
    (mu a b : ℝ) (hmu : 0 ≤ mu) (hmuMax : mu ≤ (1 / 10 : ℝ))
    (hWindow : b - a ≤ thirdFullThreeBandZ3GalerkinMovingRadiusWindow244)
    (s : Finset UniqueIndex244)
    (alpha beta : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (hAlphaODE : ∀ t ∈ Ico a b,
      HasDerivAt alpha
        (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (alpha t)) t)
    (hBetaODE : ∀ t ∈ Ico a b,
      HasDerivAt beta
        (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (beta t)) t)
    (hInitial : alpha a = beta a)
    (hInitialBall : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (2 : ℝ)) s
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (alpha a)) < 100) :
    Set.EqOn alpha beta (Ico a b) := by
  have hBetaInitialBall : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (2 : ℝ)) s
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (beta a)) < 100 := by
    simpa only [← hInitial] using hInitialBall
  have hAlphaAuto :=
    thirdFullThreeBand_z3GalerkinFiniteODE_preterminalAutomaticNonEscape244
      mu a b hmu hmuMax hWindow s alpha hAlphaODE hInitialBall
  have hBetaAuto :=
    thirdFullThreeBand_z3GalerkinFiniteODE_preterminalAutomaticNonEscape244
      mu a b hmu hmuMax hWindow s beta hBetaODE hBetaInitialBall
  intro t ht
  have hSubset : Icc a t ⊆ Ico a b := by
    intro z hz
    exact ⟨hz.1, lt_of_le_of_lt hz.2 ht.2⟩
  have hEqual :=
    thirdFullThreeBand_z3GalerkinFiniteODE_uniqueOnCompactBall244
      mu a t s alpha beta 100
      (fun z hz => hAlphaODE z (hSubset hz))
      (fun z hz => hBetaODE z (hSubset hz))
      (fun z hz => (hAlphaAuto z (hSubset hz)).2.1)
      (fun z hz => (hBetaAuto z (hSubset hz)).2.1)
      hInitial
  exact hEqual ⟨ht.1, le_rfl⟩

end
end PrimeTensor.FirstMonomialTriad
