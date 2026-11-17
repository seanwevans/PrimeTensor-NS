import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3GalerkinPreterminalAutomaticBarrier
import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Tactic

/-!
# Restart the genuine finite Z³ Leray ODE from its automatic endpoint trace

The previous endpoint theorem required an externally supplied preterminal
sequence. Here the approach sequence is CONSTRUCTED from b in closure [a,b)
for a < b. Automatic moving-ball persistence then gives an analytic endpoint
state, and the actual finite-dimensional Picard theorem restarts the SAME
viscous-plus-complete-Leray vector field at that state.

The past and restarted paths are pasted as a single function. The pasted
trajectory solves the genuine ODE on each OPEN SIDE of the joining time,
retains the original initial value, and satisfies an explicit quantitative
preterminal endpoint bound. No extra ball, speed, or restart smallness
hypothesis is introduced.

IMPORTANT: Differentiability precisely at the joining time b and the global
maximal-solution construction are separate mathematical obligations. This
module does not assert a C¹ solution across the seam or a uniform lifespan.
-/

namespace PrimeTensor.FirstMonomialTriad

open Set Filter
noncomputable section

attribute [local instance 1100] NormedSpace.complexToReal

private abbrev RestartIndex244 := thirdFullThreeBandZ3Index244

/-- Every genuine half-open interval [a,b), a<b, contains an approaching
sequence. No arbitrary Cauchy-time or limit witness need be postulated. -/
theorem thirdFullThreeBand_z3GalerkinPreterminalTimes_exists244
    (a b : ℝ) (hab : a < b) :
    ∃ times : ℕ → ℝ,
      (∀ n, times n ∈ Ico a b) ∧
      CauchySeq times ∧
      Tendsto times atTop (nhds b) := by
  have hb : b ∈ closure (Ico a b) := by
    rw [closure_Ico (ne_of_lt hab)]
    exact ⟨hab.le, le_rfl⟩
  obtain ⟨times, hTimes, hTends⟩ :=
    (mem_closure_iff_seq_limit).mp hb
  have hCauchy : CauchySeq times := by
    rw [Metric.cauchySeq_iff]
    intro epsilon hepsilon
    have hHalf : 0 < epsilon / 2 := by positivity
    have hEventually : ∀ᶠ n : ℕ in atTop,
        dist (times n) b < epsilon / 2 :=
      (Metric.tendsto_nhds.mp hTends) (epsilon / 2) hHalf
    obtain ⟨N, hN⟩ := eventually_atTop.mp hEventually
    refine ⟨N, ?_⟩
    intro m hm n hn
    calc
      dist (times m) (times n) ≤
          dist (times m) b + dist b (times n) :=
        dist_triangle _ _ _
      _ < epsilon / 2 + epsilon / 2 := by
        apply add_lt_add (hN m hm)
        simpa only [dist_comm] using hN n hn
      _ = epsilon := by ring
  exact ⟨times, hTimes, hCauchy, hTends⟩

/-- The automatic analytic endpoint trace can actually be restarted by
Picard, with no strictly smaller Wiener-ball requirement at b. The new
Picard interval may depend on the finite cutoff; the endpoint norm,
analytic mass and field-speed bounds do not. -/
theorem thirdFullThreeBand_z3GalerkinPreterminalPicardRestart244
    (mu a b : ℝ) (hab : a < b)
    (hmu : 0 ≤ mu) (hmuMax : mu ≤ (1 / 10 : ℝ))
    (hWindow : b - a ≤ thirdFullThreeBandZ3GalerkinMovingRadiusWindow244)
    (s : Finset RestartIndex244)
    (alpha : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (hODE : ∀ t ∈ Ico a b,
      HasDerivAt alpha
        (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (alpha t)) t)
    (hInitial : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (2 : ℝ)) s
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (alpha a)) < 100) :
    ∃ endpoint : thirdFullThreeBandZ3GalerkinFiniteState244 s,
      ∃ delta : ℝ, 0 < delta ∧
      ∃ beta : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s,
        beta b = endpoint ∧
        (∀ t ∈ Ioo (b - delta) (b + delta),
          HasDerivAt beta
            (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (beta t)) t) ∧
        ‖endpoint‖ ≤ 100 ∧
        thirdFullThreeBandZ3GalerkinWienerMass244
          (Real.log (9 / 5 : ℝ)) s
          (thirdFullThreeBandZ3GalerkinFiniteExtend244 s endpoint) ≤ 100 ∧
        ‖thirdFullThreeBandZ3GalerkinFiniteField244 mu s endpoint‖ ≤ 51000 ∧
        (∀ t ∈ Ico a b,
          dist (alpha t) (beta b) ≤ (51000 : ℝ) * dist t b) := by
  obtain ⟨times, hTimes, hCauchy, hTends⟩ :=
    thirdFullThreeBand_z3GalerkinPreterminalTimes_exists244 a b hab
  obtain ⟨_hLip, endpoint, _hLimit, hNorm, hHigh, hSpeed, hApproach⟩ :=
    thirdFullThreeBand_z3GalerkinFiniteODE_preterminalAutomaticEndpoint244
      mu a b hmu hmuMax hWindow s alpha hODE hInitial
      times hTimes hCauchy hTends
  obtain ⟨beta, hBetaInit, delta, hDelta, hBetaODE⟩ :=
    thirdFullThreeBand_z3GalerkinFiniteField_exists_local244
      mu b s endpoint
  refine ⟨endpoint, delta, hDelta, beta, hBetaInit,
    hBetaODE, hNorm, hHigh, hSpeed, ?_⟩
  intro t ht
  simpa only [hBetaInit] using hApproach t ht

/-- The actual past solution and the actual restarted Picard path are
pasted with no interpolation or alteration of their equations. -/
noncomputable def thirdFullThreeBandZ3GalerkinRestartGlue244
    (s : Finset RestartIndex244) (b : ℝ)
    (alpha beta : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s) :
    ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s := by
  classical
  exact fun t => if t < b then alpha t else beta t

theorem thirdFullThreeBand_z3GalerkinRestartGlue_before244
    (s : Finset RestartIndex244) (b : ℝ)
    (alpha beta : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (t : ℝ) (ht : t < b) :
    thirdFullThreeBandZ3GalerkinRestartGlue244 s b alpha beta t = alpha t := by
  simp [thirdFullThreeBandZ3GalerkinRestartGlue244, ht]

theorem thirdFullThreeBand_z3GalerkinRestartGlue_after244
    (s : Finset RestartIndex244) (b : ℝ)
    (alpha beta : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (t : ℝ) (ht : b ≤ t) :
    thirdFullThreeBandZ3GalerkinRestartGlue244 s b alpha beta t = beta t := by
  simp [thirdFullThreeBandZ3GalerkinRestartGlue244, not_lt.mpr ht]

/-- On the left of the seam the pasted solution differentiates according
to the ORIGINAL finite Leray ODE, including at the initial time a. -/
theorem thirdFullThreeBand_z3GalerkinRestartGlue_leftODE244
    (mu a b : ℝ) (s : Finset RestartIndex244)
    (alpha beta : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (hODE : ∀ t ∈ Ico a b,
      HasDerivAt alpha
        (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (alpha t)) t) :
    ∀ t ∈ Ico a b,
      HasDerivAt (thirdFullThreeBandZ3GalerkinRestartGlue244 s b alpha beta)
        (thirdFullThreeBandZ3GalerkinFiniteField244 mu s
          (thirdFullThreeBandZ3GalerkinRestartGlue244 s b alpha beta t)) t := by
  intro t ht
  have hEventually :
      thirdFullThreeBandZ3GalerkinRestartGlue244 s b alpha beta =ᶠ[nhds t]
        alpha := by
    filter_upwards [isOpen_Iio.mem_nhds ht.2] with z hz
    exact thirdFullThreeBand_z3GalerkinRestartGlue_before244 s b alpha beta z hz
  have hDeriv := (hODE t ht).congr_of_eventuallyEq hEventually
  rw [thirdFullThreeBand_z3GalerkinRestartGlue_before244 s b alpha beta t ht.2]
  exact hDeriv

/-- On the right of the seam the pasted solution differentiates according
to the SAME full finite Leray field, rather than a surrogate dynamics. -/
theorem thirdFullThreeBand_z3GalerkinRestartGlue_rightODE244
    (mu b delta : ℝ) (hDelta : 0 < delta)
    (s : Finset RestartIndex244)
    (alpha beta : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (hODE : ∀ t ∈ Ioo (b - delta) (b + delta),
      HasDerivAt beta
        (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (beta t)) t) :
    ∀ t ∈ Ioo b (b + delta),
      HasDerivAt (thirdFullThreeBandZ3GalerkinRestartGlue244 s b alpha beta)
        (thirdFullThreeBandZ3GalerkinFiniteField244 mu s
          (thirdFullThreeBandZ3GalerkinRestartGlue244 s b alpha beta t)) t := by
  intro t ht
  have hEventually :
      thirdFullThreeBandZ3GalerkinRestartGlue244 s b alpha beta =ᶠ[nhds t]
        beta := by
    filter_upwards [isOpen_Ioi.mem_nhds ht.1] with z hz
    exact thirdFullThreeBand_z3GalerkinRestartGlue_after244 s b alpha beta z hz.le
  have hDeriv := (hODE t ⟨by linarith [ht.1, hDelta], ht.2⟩).congr_of_eventuallyEq
    hEventually
  rw [thirdFullThreeBand_z3GalerkinRestartGlue_after244 s b alpha beta t ht.1.le]
  exact hDeriv

/-- A constructed, explicitly pasted finite Z³ Leray trajectory continues
beyond EVERY potential preterminal endpoint b, with the same equation on
both open sides of b, and with a quantitative continuous endpoint trace.

The remaining seam derivative and maximality construction are explicit
obligations: do NOT infer a global C¹ flow or a cutoff-independent lifespan
from this theorem alone. -/
theorem thirdFullThreeBand_z3GalerkinPreterminalGluedRestart244
    (mu a b : ℝ) (hab : a < b)
    (hmu : 0 ≤ mu) (hmuMax : mu ≤ (1 / 10 : ℝ))
    (hWindow : b - a ≤ thirdFullThreeBandZ3GalerkinMovingRadiusWindow244)
    (s : Finset RestartIndex244)
    (alpha : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (hODE : ∀ t ∈ Ico a b,
      HasDerivAt alpha
        (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (alpha t)) t)
    (hInitial : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (2 : ℝ)) s
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (alpha a)) < 100) :
    ∃ delta : ℝ, 0 < delta ∧
      ∃ gamma : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s,
        gamma a = alpha a ∧
        (∀ t ∈ Ico a b, gamma t = alpha t) ∧
        (∀ t ∈ Ico a b,
          HasDerivAt gamma
            (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (gamma t)) t) ∧
        (∀ t ∈ Ioo b (b + delta),
          HasDerivAt gamma
            (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (gamma t)) t) ∧
        (∀ t ∈ Ico a b,
          dist (gamma t) (gamma b) ≤ (51000 : ℝ) * dist t b) ∧
        thirdFullThreeBandZ3GalerkinWienerMass244
          (Real.log (9 / 5 : ℝ)) s
          (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (gamma b)) ≤ 100 ∧
        ‖thirdFullThreeBandZ3GalerkinFiniteField244 mu s (gamma b)‖ ≤ 51000 := by
  obtain ⟨endpoint, delta, hDelta, beta, hBetaInit, hBetaODE,
      _hNorm, hHigh, hSpeed, hApproach⟩ :=
    thirdFullThreeBand_z3GalerkinPreterminalPicardRestart244
      mu a b hab hmu hmuMax hWindow s alpha hODE hInitial
  let gamma := thirdFullThreeBandZ3GalerkinRestartGlue244 s b alpha beta
  have hStart : gamma a = alpha a :=
    thirdFullThreeBand_z3GalerkinRestartGlue_before244
      s b alpha beta a hab
  have hEndpoint : gamma b = endpoint := by
    change thirdFullThreeBandZ3GalerkinRestartGlue244 s b alpha beta b = endpoint
    rw [thirdFullThreeBand_z3GalerkinRestartGlue_after244
      s b alpha beta b le_rfl, hBetaInit]
  refine ⟨delta, hDelta, gamma, hStart, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact thirdFullThreeBand_z3GalerkinRestartGlue_before244
      s b alpha beta t ht.2
  · exact thirdFullThreeBand_z3GalerkinRestartGlue_leftODE244
      mu a b s alpha beta hODE
  · exact thirdFullThreeBand_z3GalerkinRestartGlue_rightODE244
      mu b delta hDelta s alpha beta hBetaODE
  · intro t ht
    have hBefore : gamma t = alpha t :=
      thirdFullThreeBand_z3GalerkinRestartGlue_before244
        s b alpha beta t ht.2
    calc
      dist (gamma t) (gamma b) = dist (alpha t) (beta b) := by
        rw [hBefore, hEndpoint, hBetaInit]
      _ ≤ (51000 : ℝ) * dist t b := hApproach t ht
  · rw [hEndpoint]
    exact hHigh
  · rw [hEndpoint]
    exact hSpeed

end
end PrimeTensor.FirstMonomialTriad
