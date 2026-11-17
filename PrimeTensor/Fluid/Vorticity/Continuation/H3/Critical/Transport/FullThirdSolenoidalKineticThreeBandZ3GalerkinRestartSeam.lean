import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3GalerkinPreterminalRestartGlue
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic

/-!
# Exact finite Z³ Galerkin ODE across the Picard restart seam

For the actual finite complex Leray-Galerkin polynomial vector field F_S,
the already-constructed preterminal flow alpha has a quantitative endpoint
trace and an honest Picard restart beta with beta b = lim_{t↑b} alpha t.
This module closes the one previously missing derivative: the piecewise
pasted path is differentiable at the joining time b and has derivative
F_S(gamma b) there.

The proof uses a one-sided derivative-extension theorem, rather than
assuming the endpoint derivative or replacing the Navier–Stokes field:
(1) 51000*|t-b| controls the left-side path discontinuity;
(2) continuity of F_S controls the limit of the actual left derivatives;
(3) the new Picard solution supplies the right derivative at b;
(4) matching one-sided derivatives gives a genuine two-sided derivative.

The resulting strong ODE holds on [a,b+delta), with delta>0. This is a
restart theorem for ANY candidate preterminal solution; construction of a
maximal solution and the common cutoff-independent lifespan remain next.
-/

namespace PrimeTensor.FirstMonomialTriad

open Set Filter
noncomputable section

attribute [local instance 1100] NormedSpace.complexToReal

private abbrev SeamIndex244 := thirdFullThreeBandZ3Index244

/-- The quantitative endpoint trace and a same-field Picard restart force
matching one-sided derivatives at the exact splice time. No postulated
endpoint derivative of the old trajectory is used. -/
theorem thirdFullThreeBand_z3GalerkinRestartGlue_seamHasDerivAt244
    (mu a b delta : ℝ) (hab : a < b) (hDelta : 0 < delta)
    (s : Finset SeamIndex244)
    (alpha beta : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (hAlphaODE : ∀ t ∈ Ico a b,
      HasDerivAt alpha
        (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (alpha t)) t)
    (hBetaODE : ∀ t ∈ Ioo (b - delta) (b + delta),
      HasDerivAt beta
        (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (beta t)) t)
    (hApproach : ∀ t ∈ Ico a b,
      dist (alpha t) (beta b) ≤ (51000 : ℝ) * dist t b) :
    HasDerivAt (thirdFullThreeBandZ3GalerkinRestartGlue244 s b alpha beta)
      (thirdFullThreeBandZ3GalerkinFiniteField244 mu s
        (thirdFullThreeBandZ3GalerkinRestartGlue244 s b alpha beta b)) b := by
  classical
  let gamma := thirdFullThreeBandZ3GalerkinRestartGlue244 s b alpha beta
  let F := thirdFullThreeBandZ3GalerkinFiniteField244 mu s
  have hEnd : gamma b = beta b :=
    thirdFullThreeBand_z3GalerkinRestartGlue_after244 s b alpha beta b le_rfl
  have hLeftODE : ∀ t ∈ Ico a b, HasDerivAt gamma (F (gamma t)) t :=
    thirdFullThreeBand_z3GalerkinRestartGlue_leftODE244
      mu a b s alpha beta hAlphaODE
  have hContLeft : ContinuousWithinAt gamma (Iio b) b := by
    apply Metric.continuousWithinAt_iff.mpr
    intro epsilon hepsilon
    refine ⟨min (b - a) (epsilon / 51000), ?_, ?_⟩
    · exact lt_min (sub_pos.mpr hab) (div_pos hepsilon (by norm_num))
    intro t htb hdist
    have hShort : dist t b < b - a :=
      lt_of_lt_of_le hdist (min_le_left _ _)
    have hNear : dist t b < epsilon / 51000 :=
      lt_of_lt_of_le hdist (min_le_right _ _)
    have hta : a ≤ t := by
      rw [Real.dist_eq] at hShort
      have hLow := (abs_lt.mp hShort).1
      linarith
    have hRate : dist (gamma t) (gamma b) ≤ (51000 : ℝ) * dist t b := by
      have hBefore : gamma t = alpha t :=
        thirdFullThreeBand_z3GalerkinRestartGlue_before244
          s b alpha beta t htb
      calc
        dist (gamma t) (gamma b) = dist (alpha t) (beta b) := by
          rw [hBefore, hEnd]
        _ ≤ (51000 : ℝ) * dist t b := hApproach t ⟨hta, htb⟩
    have hSmall : (51000 : ℝ) * dist t b < epsilon := by
      calc
        (51000 : ℝ) * dist t b < 51000 * (epsilon / 51000) :=
          mul_lt_mul_of_pos_left hNear (by norm_num)
        _ = epsilon := by field_simp <;> ring
    exact lt_of_le_of_lt hRate hSmall
  have hDifferentiable : DifferentiableOn ℝ gamma (Ioo a b) := by
    intro t ht
    exact (hLeftODE t ⟨ht.1.le, ht.2⟩).differentiableAt.differentiableWithinAt
  have hContInterior : ContinuousWithinAt gamma (Ioo a b) b :=
    hContLeft.mono (by intro t ht; exact ht.2)
  have hInteriorNear : Ioo a b ∈ nhdsWithin b (Iio b) := by
    have hAbove : Ioi a ∈ nhdsWithin b (Iio b) :=
      mem_nhdsWithin_of_mem_nhds (isOpen_Ioi.mem_nhds hab)
    filter_upwards [hAbove, self_mem_nhdsWithin] with t hta htb
    exact ⟨hta, htb⟩
  have hFieldCont : Continuous F :=
    (thirdFullThreeBand_z3GalerkinFiniteField_contDiff244 mu s).continuous
  have hFieldLeft : Tendsto (fun t : ℝ => F (gamma t))
      (nhdsWithin b (Iio b)) (nhds (F (gamma b))) :=
    hFieldCont.continuousAt.tendsto.comp hContLeft
  have hDerivativeEq : (fun t : ℝ => deriv gamma t) =ᶠ[nhdsWithin b (Iio b)]
      (fun t : ℝ => F (gamma t)) := by
    filter_upwards [hInteriorNear] with t ht
    exact (hLeftODE t ⟨ht.1.le, ht.2⟩).deriv
  have hDerivativeLimit : Tendsto (fun t : ℝ => deriv gamma t)
      (nhdsWithin b (Iio b)) (nhds (F (gamma b))) :=
    Filter.Tendsto.congr' hDerivativeEq.symm hFieldLeft
  have hLeft : HasDerivWithinAt gamma (F (gamma b)) (Iic b) b :=
    hasDerivWithinAt_Iic_of_tendsto_deriv
      hDifferentiable hContInterior hInteriorNear hDerivativeLimit
  have hBetaAt : HasDerivAt beta (F (beta b)) b :=
    hBetaODE b ⟨by linarith, by linarith⟩
  have hRight : HasDerivWithinAt gamma (F (gamma b)) (Ici b) b := by
    have hSame : ∀ t ∈ Ici b, gamma t = beta t := by
      intro t ht
      exact thirdFullThreeBand_z3GalerkinRestartGlue_after244
        s b alpha beta t ht
    have hBetaRight : HasDerivWithinAt beta (F (beta b)) (Ici b) b :=
      hBetaAt.hasDerivWithinAt
    rw [hEnd]
    exact hBetaRight.congr hSame (hSame b (by simp))
  have hJoined := hLeft.union hRight
  simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hJoined

/-- For ANY finite Galerkin solution defined up to a candidate terminal
b in the analytic window, Picard restart produces an extension across b
which solves the exact finite Leray ODE at EVERY time in [a,b+delta),
including t=b. The restart needs no extra endpoint smallness. -/
theorem thirdFullThreeBand_z3GalerkinPreterminalGluedStrongRestart244
    (mu a b : ℝ) (hab : a < b)
    (hmu : 0 ≤ mu) (hmuMax : mu ≤ (1 / 10 : ℝ))
    (hWindow : b - a ≤ thirdFullThreeBandZ3GalerkinMovingRadiusWindow244)
    (s : Finset SeamIndex244)
    (alpha : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (hAlphaODE : ∀ t ∈ Ico a b,
      HasDerivAt alpha
        (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (alpha t)) t)
    (hInitial : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (2 : ℝ)) s
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (alpha a)) < 100) :
    ∃ delta : ℝ, 0 < delta ∧
      ∃ gamma : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s,
        gamma a = alpha a ∧
        (∀ t ∈ Ico a b, gamma t = alpha t) ∧
        (∀ t ∈ Ico a (b + delta),
          HasDerivAt gamma
            (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (gamma t)) t) ∧
        thirdFullThreeBandZ3GalerkinWienerMass244
          (Real.log (9 / 5 : ℝ)) s
          (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (gamma b)) ≤ 100 ∧
        ‖thirdFullThreeBandZ3GalerkinFiniteField244 mu s (gamma b)‖ ≤ 51000 := by
  obtain ⟨endpoint, delta, hDelta, beta, hBetaInit, hBetaODE,
      _hNorm, hHigh, hSpeed, hApproach⟩ :=
    thirdFullThreeBand_z3GalerkinPreterminalPicardRestart244
      mu a b hab hmu hmuMax hWindow s alpha hAlphaODE hInitial
  let gamma := thirdFullThreeBandZ3GalerkinRestartGlue244 s b alpha beta
  have hStart : gamma a = alpha a :=
    thirdFullThreeBand_z3GalerkinRestartGlue_before244 s b alpha beta a hab
  have hEndpoint : gamma b = endpoint := by
    change thirdFullThreeBandZ3GalerkinRestartGlue244 s b alpha beta b = endpoint
    rw [thirdFullThreeBand_z3GalerkinRestartGlue_after244
      s b alpha beta b le_rfl, hBetaInit]
  have hLeft : ∀ t ∈ Ico a b,
      HasDerivAt gamma (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (gamma t)) t :=
    thirdFullThreeBand_z3GalerkinRestartGlue_leftODE244
      mu a b s alpha beta hAlphaODE
  have hRight : ∀ t ∈ Ioo b (b + delta),
      HasDerivAt gamma (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (gamma t)) t :=
    thirdFullThreeBand_z3GalerkinRestartGlue_rightODE244
      mu b delta hDelta s alpha beta hBetaODE
  have hSeam : HasDerivAt gamma
      (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (gamma b)) b :=
    thirdFullThreeBand_z3GalerkinRestartGlue_seamHasDerivAt244
      mu a b delta hab hDelta s alpha beta hAlphaODE hBetaODE hApproach
  have hFull : ∀ t ∈ Ico a (b + delta),
      HasDerivAt gamma
        (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (gamma t)) t := by
    intro t ht
    by_cases htb : t < b
    · exact hLeft t ⟨ht.1, htb⟩
    · by_cases heq : t = b
      · subst t
        exact hSeam
      · have hgt : b < t := lt_of_le_of_ne (le_of_not_gt htb) (Ne.symm heq)
        exact hRight t ⟨hgt, ht.2⟩
  refine ⟨delta, hDelta, gamma, hStart, ?_, hFull, ?_, ?_⟩
  · intro t ht
    exact thirdFullThreeBand_z3GalerkinRestartGlue_before244
      s b alpha beta t ht.2
  · rw [hEndpoint]
    exact hHigh
  · rw [hEndpoint]
    exact hSpeed

end
end PrimeTensor.FirstMonomialTriad
