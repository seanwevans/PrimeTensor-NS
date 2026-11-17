import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3GalerkinEndpointTrace
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Tactic

/-!
# Automatic preterminal analytic barrier, endpoint analytic trace, and nonescape

The input is the GENUINE finite complex Leray-Galerkin ODE on the half-open
interval [a,b), with a strict initial W_log(2) analytic ball and
b-a <= (log(2)-log(9/5))/100. No analytic-ball, speed, or finite-state
bound is postulated at later times.

The earlier persistence proof works on every compact initial subinterval
[a,t] with t<b. This gives the 100 moving-radius ball throughout [a,b),
the 100 finite-state bound, and the 51000 derivative bound, uniformly in
S. Combining this with the established Lipschitz/endpoint-sequence result
produces an endpoint state in the fixed W_log(9/5) 100-ball, where the
actual finite Leray field also has speed <= 51000.

This is a rigorous maximal-interval nonescape input, not a claim that a
maximal ODE solution or the restart/gluing construction has been built.
-/

namespace PrimeTensor.FirstMonomialTriad

open Set Filter
noncomputable section

attribute [local instance 1100] NormedSpace.complexToReal

private abbrev AutoIndex244 := thirdFullThreeBandZ3Index244
private abbrev AutoBand244 := EuclideanSpace ℂ (Fin 3)

/-- The existing finite-coordinate zero-extension makes the Wiener mass
continuous in the ACTUAL finite state, for each fixed radius. This is the
endpoint analytic-ball closure lemma; no infinite-dimensional compactness
or density argument is involved. -/
theorem thirdFullThreeBand_z3GalerkinFiniteWienerMass_continuous244
    (r : ℝ) (s : Finset AutoIndex244) :
    Continuous (fun x : thirdFullThreeBandZ3GalerkinFiniteState244 s =>
      thirdFullThreeBandZ3GalerkinWienerMass244 r s
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 s x)) := by
  classical
  unfold thirdFullThreeBandZ3GalerkinWienerMass244
  apply continuous_finsetSum
  intro n hn
  have hCoord : Continuous
      (fun x : thirdFullThreeBandZ3GalerkinFiniteState244 s => x ⟨n, hn⟩) :=
    continuous_apply (⟨n, hn⟩ : {k : AutoIndex244 // k ∈ s})
  have hTerm : Continuous
      (fun x : thirdFullThreeBandZ3GalerkinFiniteState244 s =>
        thirdFullThreeBandZ3Weight244 r n * ‖x ⟨n, hn⟩‖) :=
    continuous_const.mul (continuous_norm.comp hCoord)
  simpa only [thirdFullThreeBandZ3GalerkinFiniteExtend244, dif_pos hn] using hTerm

/-- Strong Galerkin evolution and a STRICT initial W_log(2) ball imply the
moving analytic bound at EVERY preterminal time, without hypothesizing any
ball certificate or a cutoff-dependent continuation radius. The proof
applies the already-verified persistence theorem on [a,t] separately for
each t<b. -/
theorem thirdFullThreeBand_z3GalerkinFiniteODE_preterminalAutomaticMovingBall244
    (mu a b : ℝ) (hmu : 0 ≤ mu)
    (hWindow : b - a ≤ thirdFullThreeBandZ3GalerkinMovingRadiusWindow244)
    (s : Finset AutoIndex244)
    (alpha : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (hODE : ∀ t ∈ Ico a b,
      HasDerivAt alpha
        (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (alpha t)) t)
    (hInitial : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (2 : ℝ)) s
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (alpha a)) < 100) :
    ∀ t ∈ Ico a b,
      thirdFullThreeBandZ3GalerkinWienerMass244
        (thirdFullThreeBandZ3GalerkinMovingRadius244 a t) s
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (alpha t)) ≤ 100 := by
  classical
  let u : ℝ → AutoIndex244 → AutoBand244 :=
    fun z => thirdFullThreeBandZ3GalerkinFiniteExtend244 s (alpha z)
  intro t ht
  have hSubset : Icc a t ⊆ Ico a b := by
    intro z hz
    exact ⟨hz.1, lt_of_le_of_lt hz.2 ht.2⟩
  have hContinuous : ∀ n ∈ s,
      ContinuousOn (fun z : ℝ => u z n) (Icc a t) := by
    intro n hn z hz
    exact (thirdFullThreeBand_z3GalerkinFiniteODE_coordinate_continuousAt244
      s alpha z ((hODE z (hSubset hz)).continuousAt) n hn).continuousWithinAt
  have hStrong : ∀ n ∈ s, ∀ z ∈ Ico a t,
      HasDerivAt (fun w : ℝ => u w n)
        (thirdFullThreeBandZ3GalerkinNSField244 mu s (u z) n) z := by
    intro n hn z hz
    have hzPre : z ∈ Ico a b :=
      ⟨hz.1, lt_of_le_of_lt hz.2.le ht.2⟩
    exact thirdFullThreeBand_z3GalerkinFiniteODE_coordinate_hasDerivAt244
      mu s alpha z (hODE z hzPre) n hn
  have hElapsed : t - a ≤ thirdFullThreeBandZ3GalerkinMovingRadiusWindow244 :=
    (sub_le_sub_right ht.2.le a).trans hWindow
  have hPersist := thirdFullThreeBand_z3MovingBall_cutoffFreePersistence244
    mu a t hmu hElapsed s u hContinuous hStrong (by simpa only [u] using hInitial)
  exact hPersist t ⟨ht.1, le_rfl⟩

/-- Consequences of the automatic barrier: cutoff-independent finite-state
100 nonescape and the genuine full Leray field speed 51000. These conclusions
are proved for EVERY half-open preterminal time and have no extra speed or
analytic-ball premises. -/
theorem thirdFullThreeBand_z3GalerkinFiniteODE_preterminalAutomaticNonEscape244
    (mu a b : ℝ) (hmu : 0 ≤ mu) (hmuMax : mu ≤ (1 / 10 : ℝ))
    (hWindow : b - a ≤ thirdFullThreeBandZ3GalerkinMovingRadiusWindow244)
    (s : Finset AutoIndex244)
    (alpha : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (hODE : ∀ t ∈ Ico a b,
      HasDerivAt alpha
        (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (alpha t)) t)
    (hInitial : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (2 : ℝ)) s
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (alpha a)) < 100) :
    ∀ t ∈ Ico a b,
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (9 / 5 : ℝ)) s
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (alpha t)) ≤ 100 ∧
      ‖alpha t‖ ≤ 100 ∧
      ‖thirdFullThreeBandZ3GalerkinFiniteField244 mu s (alpha t)‖ ≤ 51000 := by
  have hMoving :=
    thirdFullThreeBand_z3GalerkinFiniteODE_preterminalAutomaticMovingBall244
      mu a b hmu hWindow s alpha hODE hInitial
  intro t ht
  have hElapsed : t - a ≤ thirdFullThreeBandZ3GalerkinMovingRadiusWindow244 :=
    (sub_le_sub_right ht.2.le a).trans hWindow
  have hHigh := thirdFullThreeBand_z3MovingRadius_highBall244
    a t hElapsed s (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (alpha t))
    (hMoving t ht)
  have hState := thirdFullThreeBand_z3GalerkinFiniteState_norm_le_of_Wiener244
    (Real.log (9 / 5 : ℝ)) (Real.log_nonneg (by norm_num))
    s (alpha t) 100 (by norm_num) hHigh
  have hSpeed := thirdFullThreeBand_z3GalerkinFiniteField_norm51000_100Ball244
    mu hmu hmuMax s (alpha t) hHigh
  exact ⟨hHigh, hState, hSpeed⟩

/-- Quantitative endpoint approach. The endpoint trace is independent of
which preterminal sequence is used to construct it: every preterminal
state is within 51000*(b-t) of that same limit, and this bound tends to
zero at the right endpoint. -/
theorem thirdFullThreeBand_z3GalerkinFiniteODE_endpointDistance51000_244
    (a b : ℝ) (s : Finset AutoIndex244)
    (alpha : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (hLip : LipschitzOnWith (51000 : NNReal) alpha (Ico a b))
    (times : ℕ → ℝ) (hTimes : ∀ n, times n ∈ Ico a b)
    (hTimesEnd : Tendsto times atTop (nhds b))
    (endpoint : thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (hLimit : Tendsto (fun n => alpha (times n)) atTop (nhds endpoint)) :
    ∀ t ∈ Ico a b, dist (alpha t) endpoint ≤ (51000 : ℝ) * dist t b := by
  intro t ht
  have hL : Tendsto (fun n : ℕ => dist (alpha t) (alpha (times n)))
      atTop (nhds (dist (alpha t) endpoint)) :=
    tendsto_const_nhds.dist hLimit
  have hR : Tendsto (fun n : ℕ => (51000 : ℝ) * dist t (times n))
      atTop (nhds ((51000 : ℝ) * dist t b)) :=
    (tendsto_const_nhds.dist hTimesEnd).const_mul 51000
  apply le_of_tendsto_of_tendsto hL hR
  exact Filter.Eventually.of_forall (fun n => by
    have h := hLip.dist_le_mul t ht (times n) (hTimes n)
    have hCast : ((51000 : NNReal) : ℝ) = (51000 : ℝ) := by norm_num
    simpa only [hCast] using h)

/-- The finite Navier--Stokes field cannot blow up before a right endpoint
of the radius window: every Cauchy sequence of preterminal times has an
endpoint state in the FIXED W_log(9/5) analytic 100-ball. Both the state
and its actual projected Leray field remain bounded at that endpoint.

No preterminal ball, speed or finite-state boundedness assumption occurs in
this theorem; they follow from the strict initial ball and the genuine ODE.
The next obligation is to restart and glue at this endpoint and construct a
maximal flow covering the common interval. -/
theorem thirdFullThreeBand_z3GalerkinFiniteODE_preterminalAutomaticEndpoint244
    (mu a b : ℝ) (hmu : 0 ≤ mu) (hmuMax : mu ≤ (1 / 10 : ℝ))
    (hWindow : b - a ≤ thirdFullThreeBandZ3GalerkinMovingRadiusWindow244)
    (s : Finset AutoIndex244)
    (alpha : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (hODE : ∀ t ∈ Ico a b,
      HasDerivAt alpha
        (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (alpha t)) t)
    (hInitial : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (2 : ℝ)) s
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (alpha a)) < 100)
    (times : ℕ → ℝ) (hTimes : ∀ n, times n ∈ Ico a b)
    (hTimeCauchy : CauchySeq times)
    (hTimesEnd : Tendsto times atTop (nhds b)) :
    LipschitzOnWith (51000 : NNReal) alpha (Ico a b) ∧
      ∃ endpoint : thirdFullThreeBandZ3GalerkinFiniteState244 s,
        Tendsto (fun n => alpha (times n)) atTop (nhds endpoint) ∧
        ‖endpoint‖ ≤ 100 ∧
        thirdFullThreeBandZ3GalerkinWienerMass244
          (Real.log (9 / 5 : ℝ)) s
          (thirdFullThreeBandZ3GalerkinFiniteExtend244 s endpoint) ≤ 100 ∧
        ‖thirdFullThreeBandZ3GalerkinFiniteField244 mu s endpoint‖ ≤ 51000 ∧
        (∀ t ∈ Ico a b, dist (alpha t) endpoint ≤ (51000 : ℝ) * dist t b) := by
  have hNonescape :=
    thirdFullThreeBand_z3GalerkinFiniteODE_preterminalAutomaticNonEscape244
      mu a b hmu hmuMax hWindow s alpha hODE hInitial
  have hHigh : ∀ t ∈ Ico a b,
      thirdFullThreeBandZ3GalerkinWienerMass244 (Real.log (9 / 5 : ℝ)) s
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (alpha t)) ≤ 100 := by
    intro t ht
    exact (hNonescape t ht).1
  have hState : ∀ t ∈ Ico a b, ‖alpha t‖ ≤ 100 := by
    intro t ht
    exact (hNonescape t ht).2.1
  have hSpeed : ∀ t ∈ Ico a b,
      ‖thirdFullThreeBandZ3GalerkinFiniteField244 mu s (alpha t)‖ ≤ 51000 := by
    intro t ht
    exact (hNonescape t ht).2.2
  have hLip := thirdFullThreeBand_z3GalerkinFiniteODE_preterminalLipschitz51000_244
    mu a b s alpha hODE hSpeed
  obtain ⟨endpoint, hLimit, hNorm⟩ :=
    thirdFullThreeBand_z3GalerkinFiniteODE_endpointSequence_nonescape244
      mu a b s alpha hODE hSpeed hState times hTimes hTimeCauchy
  have hMassLimit :
      Tendsto (fun n : ℕ =>
        thirdFullThreeBandZ3GalerkinWienerMass244 (Real.log (9 / 5 : ℝ)) s
          (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (alpha (times n))))
        atTop (nhds (thirdFullThreeBandZ3GalerkinWienerMass244
          (Real.log (9 / 5 : ℝ)) s
          (thirdFullThreeBandZ3GalerkinFiniteExtend244 s endpoint))) :=
    (thirdFullThreeBand_z3GalerkinFiniteWienerMass_continuous244
      (Real.log (9 / 5 : ℝ)) s).continuousAt.tendsto.comp hLimit
  have hEndHigh : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (9 / 5 : ℝ)) s
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 s endpoint) ≤ 100 := by
    exact le_of_tendsto hMassLimit
      (Filter.Eventually.of_forall (fun n => hHigh (times n) (hTimes n)))
  have hEndSpeed := thirdFullThreeBand_z3GalerkinFiniteField_norm51000_100Ball244
    mu hmu hmuMax s endpoint hEndHigh
  have hEndRate := thirdFullThreeBand_z3GalerkinFiniteODE_endpointDistance51000_244
    a b s alpha hLip times hTimes hTimesEnd endpoint hLimit
  exact ⟨hLip, endpoint, hLimit, hNorm, hEndHigh, hEndSpeed, hEndRate⟩

end
end PrimeTensor.FirstMonomialTriad
